import NumpyLean.Common.Intp

/-
Model of the integer and index arithmetic in NumPy's string functions, for the three string kinds: `S` (bytes padded with NULs), `U` (UCS4 padded with NULs) and `T` (`StringDType`, UTF-8 with no padding).

A string is a list of code units. For `S` the units are bytes and for `U` and `T` they are code points. Reading an `S` or `U` element drops its trailing NULs, because the buffer cannot tell them from padding (`Buffer::num_codepoints`, `_core/src/umath/string_buffer.h:280`). A `T` element is read as it is. The C code for `T` works on UTF-8 bytes, but every index it exposes counts code points, so the model uses code points for all three kinds and the differential tests check that this is right.

Source paths are relative to `vendor/numpy/numpy/`. C signed arithmetic on values that stay far from the limits is written as plain `Int` arithmetic, with a comment where an overflow would be possible.
-/
namespace NumpyLean.Strings

inductive Kind where
  | S
  | U
  | T
  deriving DecidableEq, Repr

abbrev Str := List Int

/-- Drop the NULs at the end of a list. -/
def dropTrailingZeros (s : Str) : Str := (s.reverse.dropWhile (· == 0)).reverse

/-- What the C code sees as the string held in a buffer. `_core/src/umath/string_buffer.h:280` -/
def readStr : Kind → Str → Str
  | .T, s => s
  | _, s => dropTrailingZeros s

/-- `np.strings.str_len`. -/
def strLen (k : Kind) (s : Str) : Int := ((readStr k s).length : Int)

/-- Errors, one constructor per distinct error site. -/
inductive SErr where
  /-- `ValueError: substring not found` from `string_index` and `string_rindex` (`string_buffer.h:949`, `:1055`). -/
  | notFound
  /-- `ValueError: empty separator` from `string_partition` (`string_buffer.h:1668`) and the `StringDType` partition loop. -/
  | emptySep
  /-- `TypeError: The fill character must be exactly one character long` from `center`, `ljust` and `rjust` (`strings.py:735`). -/
  | fillLen
  /-- `OverflowError: new string is too long` from `string_expandtabs_length` (`string_buffer.h:1518`). -/
  | tooLong
  /-- `ValueError: slice step cannot be zero` (`string_ufuncs.cpp:688`). -/
  | stepZero
  /-- `TypeError: data type 'U<width>' not understood`. The Python wrapper builds the output dtype `S<width>` or `U<width>` before calling the ufunc, and `np.dtype` refuses an item size above `INT_MAX` (`strings.py:754`). -/
  | dtype
  /-- `OverflowError: Overflow encountered in _center` or `in zfill` from the `StringDType` loops (`stringdtype_ufuncs.cpp:1795`, `:1920`). -/
  | overflow
  /-- `MemoryError: Failed to allocate string` from the `StringDType` loops when the allocation cannot be made. -/
  | alloc
  deriving DecidableEq, Repr

/-! ## Offsets, `find`, `rfind`, `count`, `startswith`, `endswith` -/

/--
`adjust_offsets` (`_core/src/umath/string_buffer.h:829`), taken from CPython. It returns the adjusted `(start, end)`. Nothing here can overflow: `end += len` only runs for a negative `end` and `start += len` for a negative `start`.
-/
def adjustOffsets (start end_ : Int) (len : Nat) : Int × Int :=
  let l : Int := len
  let e := if end_ > l then l else if end_ < 0 then (if end_ + l < 0 then 0 else end_ + l) else end_
  let s := if start < 0 then (if start + l < 0 then 0 else start + l) else start
  (s, e)

/-- All positions at which `n` is a prefix of the window `w`, trying `fuel` positions from `p`. Every search in `string_find`, `string_rfind`, `string_count` and `string_replace` runs on a window of the haystack, and a match must lie inside it. -/
def matchPositions (n : Str) : Str → Nat → Nat → List Nat
  | _, _, 0 => []
  | w, p, fuel + 1 => (if n.isPrefixOf w then [p] else []) ++ matchPositions n w.tail (p + 1) fuel

/-! ## The two-way search of `string_fastsearch.h` -/

/-- Result of `lex_search` (`string_fastsearch.h:454`): the start of the maximal suffix and the period of the right half. `inv` reverses the alphabet order. The loop adds at least one to `candidate + k + max_suffix` each time, so `4 * m + 4` rounds are enough. -/
def lexSearchGo (nd : Array Int) (inv : Bool) (m : Nat) : Nat → Nat → Nat → Nat → Nat → Nat × Nat
  | 0, ms, _, _, per => (ms, per)
  | fuel + 1, ms, cand, k, per =>
    if cand + k < m then
      let a := nd[cand + k]!
      let b := nd[ms + k]!
      if (if inv then b < a else a < b) then
        let cand' := cand + k + 1
        lexSearchGo nd inv m fuel ms cand' 0 (cand' - ms)
      else if a == b then
        if k + 1 != per then lexSearchGo nd inv m fuel ms cand (k + 1) per
        else lexSearchGo nd inv m fuel ms (cand + per) 0 per
      else lexSearchGo nd inv m fuel cand (cand + 1) 0 1
    else (ms, per)

/-- `factorize` (`string_fastsearch.h:547`): the later of the two cuts, with its period. -/
def factorize (nd : Array Int) (m : Nat) : Nat × Nat :=
  let (cut1, per1) := lexSearchGo nd false m (4 * m + 4) 0 1 0 1
  let (cut2, per2) := lexSearchGo nd true m (4 * m + 4) 0 1 0 1
  if cut1 > cut2 then (cut1, per1) else (cut2, per2)

/-- The data that `preprocess` builds for the needle (`string_fastsearch.h:623`). -/
structure Prep where
  nd : Array Int
  m : Nat
  cut : Nat
  period : Nat
  gap : Nat
  periodic : Bool
  table : Array Nat

/--
`preprocess`. The test for a periodic needle is `memcmp(needle, needle + period, cut)` (`string_fastsearch.h:639`). C's `memcmp` counts bytes and `cut` is a count of characters, so for `char_type = npy_ucs4` only the first `cut` bytes are compared, which is the first `cut / 4` characters and the low `cut % 4` bytes of the next one on a little-endian machine (arm64 and x86-64). `bytes` is 4 for `U` and 1 for `S` and for the UTF-8 loops of `StringDType`. The memcmp is the line that differs from CPython's `stringlib/fastsearch.h`, which multiplies by `STRINGLIB_SIZEOF_CHAR`.
-/
def preprocess (nd : Array Int) (m : Nat) (bytes : Nat) : Prep :=
  let (cut, per) := factorize nd m
  let full := cut / bytes
  let rem := cut % bytes
  let eqFull := (List.range full).all fun i => nd[i]! == nd[per + i]!
  let eqPart := rem == 0 || nd[full]! % ((256 : Int) ^ rem) == nd[per + full]! % ((256 : Int) ^ rem)
  let periodic := eqFull && eqPart
  let period := if periodic then per else max cut (m - cut) + 1
  let lastIdx := (List.range (m - 1)).reverse.find? fun i => nd[i]! % 64 == nd[m - 1]! % 64
  let gap := if periodic then 0 else (match lastIdx with | some i => m - 1 - i | none => m)
  let nfs := min m 255
  let t0 := Array.replicate 64 nfs
  let table := (List.range' (m - nfs) nfs).foldl (fun t i => t.set! (nd[i]! % 64).toNat (m - 1 - i)) t0
  { nd, m, cut, period, gap, periodic, table }

/-- The bad-character skip loop at the top of the window loops. `none` means the window ran past the end, so `two_way` returns -1. -/
def horspool (P : Prep) (h : Array Int) (len : Nat) : Nat → Nat → Option Nat
  | 0, wl => some wl
  | f + 1, wl =>
    let sh := P.table[(h[wl]! % 64).toNat]!
    if sh == 0 then some wl
    else if wl + sh ≥ len then none
    else horspool P h len f (wl + sh)

/-- The first index in `[lo, hi)` where the needle and the window starting at `win` differ. -/
def firstMismatch (P : Prep) (h : Array Int) (win lo hi : Nat) : Option Nat :=
  (List.range' lo (hi - lo)).find? fun i => P.nd[i]! != h[win + i]!

/-- The periodic branch of `two_way` (`string_fastsearch.h:760`). `skip` is true when C jumps to `no_shift` and so skips the bad-character loop. -/
def twoWayPeriodic (P : Prep) (h : Array Int) (len : Nat) : Nat → Nat → Nat → Bool → Int
  | 0, _, _, _ => -1
  | f + 1, wl, memory, skip =>
    if wl ≥ len && !skip then -1
    else
      match (if skip then some wl else horspool P h len len wl) with
      | none => -1
      | some wl1 =>
        let win := wl1 + 1 - P.m
        match firstMismatch P h win (max P.cut memory) P.m with
        | some i => twoWayPeriodic P h len f (wl1 + (i - P.cut + 1)) 0 false
        | none =>
          match firstMismatch P h win memory P.cut with
          | some _ =>
            let wl2 := wl1 + P.period
            let mem2 := P.m - P.period
            if wl2 ≥ len then -1
            else
              let sh := P.table[(h[wl2]! % 64).toNat]!
              if sh != 0 then
                let memJump := max P.cut mem2 - P.cut + 1
                twoWayPeriodic P h len f (wl2 + max sh memJump) 0 false
              else twoWayPeriodic P h len f wl2 mem2 true
          | none => (win : Int)

/-- The non-periodic branch of `two_way` (`string_fastsearch.h:830`). -/
def twoWayPlain (P : Prep) (h : Array Int) (len : Nat) (per gapJumpEnd : Nat) : Nat → Nat → Int
  | 0, _ => -1
  | f + 1, wl =>
    if wl ≥ len then -1
    else
      match horspool P h len len wl with
      | none => -1
      | some wl1 =>
        let win := wl1 + 1 - P.m
        match firstMismatch P h win P.cut gapJumpEnd with
        | some _ => twoWayPlain P h len per gapJumpEnd f (wl1 + P.gap)
        | none =>
          match firstMismatch P h win gapJumpEnd P.m with
          | some i => twoWayPlain P h len per gapJumpEnd f (wl1 + (i - P.cut + 1))
          | none =>
            match firstMismatch P h win 0 P.cut with
            | some _ => twoWayPlain P h len per gapJumpEnd f (wl1 + per)
            | none => (win : Int)

/-- `two_way`: the index of the first match of the prepared needle in `h`, or -1. Each round moves the window right, so `len + 1` rounds are enough, but the round count is also bounded by `len * m` for safety. -/
def twoWay (P : Prep) (h : Array Int) : Int :=
  let len := h.size
  let fuel := 4 * len + 4
  if P.periodic then twoWayPeriodic P h len fuel (P.m - 1) 0 false
  else twoWayPlain P h len (max P.gap P.period) (min P.m (P.cut + P.gap)) fuel (P.m - 1)

/-- `two_way_count`: non-overlapping matches, each search starting after the previous match. -/
def twoWayCount (P : Prep) (w : Array Int) : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, idx =>
    let r := twoWay P (w.extract idx w.size)
    if r < 0 then 0 else 1 + twoWayCount P w f (idx + r.toNat + P.m)

/--
`fastsearch` for `FAST_SEARCH` and `FAST_COUNT` over a window of `n` units with a needle of `m >= 2` units (`string_fastsearch.h:1258`). It returns `none` when the C code takes `adaptive_find`, which this model does not port: that happens when the needle is longer than a third of a haystack of 2500 or more units, and the tests keep `U` away from it.
-/
def useTwoWay (n m : Nat) : Option Bool :=
  if n < 2500 || (m < 100 && n < 30000) || m < 6 then some false
  else if (m / 4) * 3 < (n / 4) then some true
  else none

/-- The lowest match position of the non-empty `n` in the window `w`. This is `find_char` and `fastsearch` with `FAST_SEARCH`. For `U` a long window goes through the two-way search with the periodicity test of `UTF32`. -/
def findIn (k : Kind) (n w : Str) : Option Nat :=
  if k == .U && n.length ≥ 2 && useTwoWay w.length n.length == some true then
    let P := preprocess n.toArray n.length 4
    let r := twoWay P w.toArray
    if r < 0 then none else some r.toNat
  else (matchPositions n w 0 (w.length + 1 - n.length)).head?

/-- The highest match position of the non-empty `n` in the window `w`. This is `rfind_char` and `fastsearch` with `FAST_RSEARCH`, which always runs `default_rfind`. -/
def rfindIn (n w : Str) : Option Nat := (matchPositions n w 0 (w.length + 1 - n.length)).getLast?

/-- The number of non-overlapping matches of the non-empty `n` in the window `w`, found from the left (`fastsearch` with `FAST_COUNT`). `rem` is the number of start positions still to try, which is `|w| - |n| + 1` at the start. -/
def countSpec (n : Str) : Str → Nat → Nat → Nat
  | _, _, 0 => 0
  | w, rem, fuel + 1 =>
    if rem == 0 then 0
    else if n.isPrefixOf w then 1 + countSpec n (w.drop n.length) (rem - n.length) fuel
    else countSpec n w.tail (rem - 1) fuel

def countIn (k : Kind) (n w : Str) (fuel : Nat) : Nat :=
  if k == .U && n.length ≥ 2 && useTwoWay w.length n.length == some true then
    twoWayCount (preprocess n.toArray n.length 4) w.toArray w.length 0
  else countSpec n w (w.length + 1 - n.length) fuel

/-- The part of `a` that the search sees: the window [s, e) of `adjust_offsets`. -/
def window (a : Str) (s e : Int) : Str := (a.drop s.toNat).take (e - s).toNat

/-- `string_find` (`string_buffer.h:851`). Returns -1 when the needle is absent. The `T` kind runs the same function on UTF-8 and converts byte offsets back to code point offsets. -/
def findImpl (k : Kind) (a0 n0 : Str) (start end_ : Int) : Int :=
  let a := readStr k a0
  let n := readStr k n0
  let (s, e) := adjustOffsets start end_ a.length
  if e - s < (n.length : Int) then -1
  else if n.length == 0 then s
  else
    match findIn k n (window a s e) with
    | some p => s + (p : Int)
    | none => -1

/-- `string_rfind` (`string_buffer.h:954`). An empty needle gives `end`. -/
def rfindImpl (k : Kind) (a0 n0 : Str) (start end_ : Int) : Int :=
  let a := readStr k a0
  let n := readStr k n0
  let (s, e) := adjustOffsets start end_ a.length
  if e - s < (n.length : Int) then -1
  else if n.length == 0 then e
  else
    match rfindIn n (window a s e) with
    | some p => s + (p : Int)
    | none => -1

/-- `string_index`. -/
def indexImpl (k : Kind) (a n : Str) (start end_ : Int) : Except SErr Int :=
  let p := findImpl k a n start end_
  if p == -1 then .error .notFound else .ok p

/-- `string_rindex`. -/
def rindexImpl (k : Kind) (a n : Str) (start end_ : Int) : Except SErr Int :=
  let p := rfindImpl k a n start end_
  if p == -1 then .error .notFound else .ok p

/-- `string_count` (`string_buffer.h:1066`). The empty needle gives `end - start + 1`, which cannot reach `PY_SSIZE_T_MAX` for these lengths. -/
def countImpl (k : Kind) (a0 n0 : Str) (start end_ : Int) : Int :=
  let a := readStr k a0
  let n := readStr k n0
  let (s, e) := adjustOffsets start end_ a.length
  if e < s || e - s < (n.length : Int) then 0
  else if n.length == 0 then e - s + 1
  else
    -- The search runs on the window [s, e), so a match must end at or before e.
    ((countIn k n (window a s e) (e - s + 1).toNat : Nat) : Int)

/-- `tailmatch` (`string_buffer.h:1110`). `front` is `startswith` and not `front` is `endswith`. In C `end -= len2` runs on a signed `npy_int64` and `len2` is a `size_t`, but both are small after `adjust_offsets`, so there is no wrap. -/
def tailmatchImpl (k : Kind) (front : Bool) (a0 n0 : Str) (start end_ : Int) : Bool :=
  let a := readStr k a0
  let n := readStr k n0
  let (s, e0) := adjustOffsets start end_ a.length
  let e := e0 - n.length
  if e < s then false
  else if n.length == 0 then true
  else
    let off := if front then s else e
    (window a off (off + n.length)) == n


/-! ## Sizes of UTF-8 strings and of the output dtype -/

/-- Bytes in the UTF-8 encoding of a code point (`ucs4_code_to_utf8_char`). -/
def utf8Size (c : Int) : Int := if c < 0x80 then 1 else if c < 0x800 then 2 else if c < 0x10000 then 3 else 4

/-- The bytes of the UTF-8 encoding of a code point. -/
def utf8Encode (c : Int) : List Int :=
  if c < 0x80 then [c]
  else if c < 0x800 then [0xC0 + c / 64, 0x80 + c % 64]
  else if c < 0x10000 then [0xE0 + c / 4096, 0x80 + (c / 64) % 64, 0x80 + c % 64]
  else [0xF0 + c / 262144, 0x80 + (c / 4096) % 64, 0x80 + (c / 64) % 64, 0x80 + c % 64]

def utf8Bytes (s : Str) : Int := (s.map utf8Size).foldl (· + ·) 0

/-- Largest width for which `np.dtype("S<w>")` or `np.dtype("U<w>")` works. The item size must fit in a C `int`, which is 2^31 - 1 bytes. For `U` the item size is four times the width. -/
def maxDtypeWidth : Kind → Int
  | .S => 2147483647
  | .U => 536870911
  | .T => 0

/-- The model treats a `StringDType` allocation above this many bytes as failing. The real limit is the allocator and the memory of the machine, so the tests only use sizes far below it or far above it. -/
def allocLimit : Int := 2 ^ 40

/-! ## `center`, `ljust`, `rjust`, `zfill` -/

inductive Pos where
  | center
  | left
  | right
  deriving DecidableEq, Repr

/-- The padding arithmetic of `string_pad` (`string_buffer.h:1569`) for a string that is shorter than the final width. In C `pad & final_width & 1` is a bitwise and of two `size_t`. -/
def padSplit (pos : Pos) (len final : Nat) : Nat × Nat :=
  match pos with
  | .center =>
    let pad := final - len
    let left := pad / 2 + (if pad % 2 == 1 && final % 2 == 1 then 1 else 0)
    (left, pad - left)
  | .left => (0, final - len)
  | .right => (final - len, 0)

/-- `string_pad` on a string of known length, for `final` already clamped to be non-negative. -/
def padCore (pos : Pos) (a : Str) (final : Nat) (fill : Int) : Str :=
  if a.length ≥ final then a
  else
    let (l, r) := padSplit pos a.length final
    List.replicate l fill ++ a ++ List.replicate r fill

/-- The checks around the padded width. The `S` and `U` wrappers in `strings.py` take the larger of the string length and the width and build a dtype from it. The `StringDType` loop computes the byte size with `safe_mul` and `safe_add`. `size` is the UTF-8 size of the input and `fillBytes` the UTF-8 size of the fill, which is 1 for zfill. -/
def padWidthCheck (k : Kind) (a : Str) (w : Int) (fillBytes : Int) : Option SErr :=
  match k with
  | .T =>
    let newsize := fillBytes * (w - a.length) + utf8Bytes a
    if newsize > intpMax then some .overflow
    else if newsize > allocLimit then some .alloc
    else none
  | _ => if w > maxDtypeWidth k then some .dtype else none

/-- `np.strings.center`, `ljust` and `rjust` with a fill string. The fill must be exactly one character after the trailing NULs of `S` and `U` are dropped (`strings.py:735`). -/
def justImpl (k : Kind) (pos : Pos) (a0 : Str) (width : Int) (fill0 : Str) : Except SErr Str :=
  let a := readStr k a0
  let fill := readStr k fill0
  if fill.length != 1 then .error .fillLen
  else
    let f := fill.headD 0
    let w := max (a.length : Int) width
    match padWidthCheck k a w (if k == .T then utf8Size f else 1) with
    | some e => .error e
    | none => .ok (padCore pos a w.toNat f)

/-- `np.strings.zfill` (`string_zfill`, `string_buffer.h:1628`). The sign is moved in front of the zeros when padding was added. -/
def zfillImpl (k : Kind) (a0 : Str) (width : Int) : Except SErr Str :=
  let a := readStr k a0
  let w := max (a.length : Int) width
  match padWidthCheck k a w 1 with
  | some e => .error e
  | none =>
    let out := padCore .right a w.toNat 48
    if a.length > 0 && w > a.length then
      let off := (w - a.length).toNat
      let c := out.getD off 0
      if c == 43 || c == 45 then .ok ((out.set off 48).set 0 c) else .ok out
    else .ok out

/-! ## `expandtabs` -/

/-- Bytes that one non-tab character adds to the output length: the UTF-8 size for `StringDType` and one unit for `S` and `U`. -/
def charBytes (k : Kind) (c : Int) : Int := if k == .T then utf8Size c else 1

/--
The loop of `string_expandtabs_length` and `string_expandtabs` (`string_buffer.h:1496`, `:1532`). `lp` is `line_pos` and `nl` is `new_len`. The length check runs after every character and stops at once, so the signed additions in C cannot wrap before the check: `nl` is at most `INT_MAX` before each addition and an increment is at most `2^63 - 1`, and a wrapped sum would be negative, which the check also rejects. The output piece is built only after the check passes.
-/
def expandGo (k : Kind) (ts : Int) : Str → Int → Int → Except SErr Str
  | [], _, _ => .ok []
  | c :: rest, lp, nl =>
    if c == 9 then
      if ts > 0 then
        let incr := ts - lp % ts
        let nl' := nl + incr
        if nl' > 2147483647 || nl' < 0 then .error .tooLong
        else (expandGo k ts rest (lp + incr) nl').map (List.replicate incr.toNat 32 ++ ·)
      else expandGo k ts rest lp nl
    else
      let nl' := nl + charBytes k c
      let lp' := if c == 10 || c == 13 then 0 else lp + 1
      if nl' > 2147483647 || nl' < 0 then .error .tooLong
      else (expandGo k ts rest lp' nl').map (c :: ·)

/-- The result is read back through `readStr`, because removing tabs can leave NULs at the end of an `S` or `U` result. -/
def expandtabsImpl (k : Kind) (a0 : Str) (ts : Int) : Except SErr Str :=
  (expandGo k ts (readStr k a0) 0 0).map (readStr k)

/-! ## `replace` -/

/-- Replace the first `c` non-overlapping matches of a non-empty `old`, as the loop in `string_replace` does. -/
def replaceLoop (k : Kind) (old new : Str) : Nat → Str → Str
  | 0, rest => rest
  | c + 1, rest =>
    match findIn k old rest with
    | none => rest
    | some p => rest.take p ++ new ++ replaceLoop k old new c (rest.drop (p + old.length))

/-- The interleaving branch for an empty `old`: `new` before each of the first `c` positions. The C loop copies one character of the input after each insertion except the last. -/
def interleave (new : Str) : Nat → Str → Str
  | 0, rest => rest
  | c + 1, rest =>
    new ++ (if c == 0 then rest else match rest with
      | [] => []
      | x :: r => x :: interleave new c r)

/--
`string_replace` (`string_buffer.h:1372`) with the count already clamped. The `S` and `U` wrapper in `strings.py:1344` clamps with the result of `count`, and the `StringDType` loop clamps in `stringdtype_ufuncs.cpp:1466`. In both a negative count means all matches.
-/
def replaceCore (k : Kind) (a old new : Str) (count : Nat) : Str :=
  if count == 0 || a.length < old.length || (old.length == 0 && new.length == 0) || (old.length == new.length && old == new) then a
  else if old.length > 0 then replaceLoop k old new count a
  else interleave new count a

def replaceImpl (k : Kind) (a0 o0 n0 : Str) (count : Int) : Str :=
  let a := readStr k a0
  let o := readStr k o0
  let n := readStr k n0
  let found := countImpl k a o 0 intpMax
  let eff := if count < 0 then found else min found count
  readStr k (replaceCore k a o n eff.toNat)

/-! ## `partition` and `rpartition` -/

/-- `string_partition` (`string_buffer.h:1658`) with the position found by `find` or `rfind` over the whole string. Returns the three parts. -/
def partitionImpl (k : Kind) (front : Bool) (a0 sep0 : Str) : Except SErr (Str × Str × Str) :=
  let a := readStr k a0
  let sep := readStr k sep0
  if sep.length == 0 then .error .emptySep
  else
    let idx := if front then findImpl k a sep 0 intpMax else rfindImpl k a sep 0 intpMax
    if idx < 0 then
      if front then .ok (a, [], []) else .ok ([], [], a)
    else
      let i := idx.toNat
      .ok (readStr k (a.take i), sep, a.drop (i + sep.length))

/-! ## `strip`, `lstrip`, `rstrip` -/

/-- `Py_UNICODE_ISSPACE` for `U` and `StringDType`, and `NumPyOS_ascii_isspace` for `S`. -/
def isSpace (k : Kind) (c : Int) : Bool :=
  match k with
  | .S => c == 32 || (9 ≤ c && c ≤ 13)
  | _ =>
    c == 32 || (9 ≤ c && c ≤ 13) || (28 ≤ c && c ≤ 31) || c == 0x85 || c == 0xA0 || c == 0x1680 ||
    (0x2000 ≤ c && c ≤ 0x200A) || c == 0x2028 || c == 0x2029 || c == 0x202F || c == 0x205F || c == 0x3000

inductive Strip where
  | left
  | right
  | both
  deriving DecidableEq, Repr

/-- The stripping loops of `string_lrstrip_whitespace` and `string_lrstrip_chars` (`string_buffer.h:1166`, `:1230`). `inLeft` and `inRight` say whether a character is removed from the left or from the right. The right-hand test of the whitespace version for `S` and `U` also removes NUL (`string_buffer.h:1202`), which the chars version and the `StringDType` version do not. -/
def stripCore (mode : Strip) (inLeft inRight : Int → Bool) (a : Str) : Str :=
  let start := if mode == .right then 0 else (a.takeWhile inLeft).length
  let rest := a.drop start
  if mode == .left then rest
  else (rest.reverse.dropWhile inRight).reverse

/--
Whether `c` is found in the strip set `ch`. For `S` and `U` this is `find_char` over the `len2` units of `ch`. For `StringDType` the C code takes the one-byte branch for an ASCII character and passes `len2`, the number of code points, as the length of a search over the UTF-8 bytes of `ch` (`string_buffer.h:1270`, `:1316`). When `ch` holds multi-byte characters the byte string is longer than `len2`, so the last bytes are never searched. A character of two or more bytes is searched for in the whole byte string.
-/
def inStripSet (k : Kind) (ch : Str) (c : Int) : Bool :=
  if k == .T && utf8Size c == 1 then ((ch.flatMap utf8Encode).take ch.length).contains c
  else ch.contains c

/-- `np.strings.strip` and friends. `chars = none` strips whitespace. -/
def stripImpl (k : Kind) (mode : Strip) (a0 : Str) (chars : Option Str) : Str :=
  let a := readStr k a0
  readStr k <| match chars with
  | none => stripCore mode (isSpace k) (fun c => isSpace k c || (k != .T && c == 0)) a
  | some c0 =>
    let ch := readStr k c0
    if ch.isEmpty then a else stripCore mode (inStripSet k ch) (inStripSet k ch) a

/-! ## `slice` -/

/-- `PySlice_AdjustIndices` for a string of `len` units. Returns the adjusted start and stop and the length of the slice. -/
def adjustSlice (len : Int) (start stop step : Int) : Int × Int × Int :=
  let s :=
    if start < 0 then (if start + len < 0 then (if step < 0 then -1 else 0) else start + len)
    else if start ≥ len then (if step < 0 then len - 1 else len) else start
  let e :=
    if stop < 0 then (if stop + len < 0 then (if step < 0 then -1 else 0) else stop + len)
    else if stop ≥ len then (if step < 0 then len - 1 else len) else stop
  let n :=
    if step < 0 then (if e < s then (s - e - 1) / (-step) + 1 else 0)
    else (if s < e then (e - s - 1) / step + 1 else 0)
  (s, e, n)

/-- `np.strings.slice` (`string_slice_loop`, `string_ufuncs.cpp:670`). The step is clamped to `-INTP_MAX` for the index adjustment only. -/
def sliceImpl (k : Kind) (a0 : Str) (start stop step : Int) : Except SErr Str :=
  if step == 0 then .error .stepZero
  else
    let a := readStr k a0
    let (s, _, n) := adjustSlice a.length start stop (if step < -intpMax then -intpMax else step)
    .ok (readStr k ((List.range n.toNat).map fun (i : Nat) => a.getD (s + step * (i : Int)).toNat 0))

end NumpyLean.Strings
