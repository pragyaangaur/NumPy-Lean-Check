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

/-- Whether `n` occurs in `a` at position `p`. -/
def matchAt (a n : Str) (p : Nat) : Bool := (a.drop p).take n.length == n

/-- The lowest match position at or above `p`, trying `fuel` positions. -/
def findFrom (a n : Str) (p : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 => if matchAt a n p then some p else findFrom a n (p + 1) fuel

/-- The highest match position at or below `p`, trying `fuel` positions going down. -/
def rfindFrom (a n : Str) (p : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 => if matchAt a n p then some p else if p == 0 then none else rfindFrom a n (p - 1) fuel

/-- Count of non-overlapping matches that end at or before `lim`, scanning from `p`, trying `fuel` positions. -/
def countFrom (a n : Str) (lim : Nat) (p : Nat) : Nat → Nat
  | 0 => 0
  | fuel + 1 =>
    if p + n.length > lim then 0
    else if matchAt a n p then 1 + countFrom a n lim (p + n.length) fuel
    else countFrom a n lim (p + 1) fuel

/-- `string_find` (`string_buffer.h:851`). Returns -1 when the needle is absent. The `T` kind runs the same function on UTF-8 and converts byte offsets back to code point offsets. -/
def findImpl (k : Kind) (a0 n0 : Str) (start end_ : Int) : Int :=
  let a := readStr k a0
  let n := readStr k n0
  let (s, e) := adjustOffsets start end_ a.length
  if e - s < (n.length : Int) then -1
  else if n.length == 0 then s
  else
    let fuel := (e - n.length - s + 1).toNat
    match findFrom a n s.toNat fuel with
    | some p => (p : Int)
    | none => -1

/-- `string_rfind` (`string_buffer.h:954`). An empty needle gives `end`. -/
def rfindImpl (k : Kind) (a0 n0 : Str) (start end_ : Int) : Int :=
  let a := readStr k a0
  let n := readStr k n0
  let (s, e) := adjustOffsets start end_ a.length
  if e - s < (n.length : Int) then -1
  else if n.length == 0 then e
  else
    let hi := (e - n.length).toNat
    let fuel := (e - n.length - s + 1).toNat
    match rfindFrom a n hi fuel with
    | some p => (p : Int)
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
    (countFrom a n e.toNat s.toNat (e - s + 1).toNat : Nat)

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
    matchAt a n off.toNat


/-! ## Sizes of UTF-8 strings and of the output dtype -/

/-- Bytes in the UTF-8 encoding of a code point (`ucs4_code_to_utf8_char`). -/
def utf8Size (c : Int) : Int := if c < 0x80 then 1 else if c < 0x800 then 2 else if c < 0x10000 then 3 else 4

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
def replaceLoop (old new : Str) : Nat → Str → Str
  | 0, rest => rest
  | c + 1, rest =>
    match findFrom rest old 0 (rest.length + 1 - old.length) with
    | none => rest
    | some p => rest.take p ++ new ++ replaceLoop old new c (rest.drop (p + old.length))

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
def replaceCore (a old new : Str) (count : Nat) : Str :=
  if count == 0 || a.length < old.length || (old.length == 0 && new.length == 0) || (old.length == new.length && old == new) then a
  else if old.length > 0 then replaceLoop old new count a
  else interleave new count a

def replaceImpl (k : Kind) (a0 o0 n0 : Str) (count : Int) : Str :=
  let a := readStr k a0
  let o := readStr k o0
  let n := readStr k n0
  let found := countImpl k a o 0 intpMax
  let eff := if count < 0 then found else min found count
  readStr k (replaceCore a o n eff.toNat)

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

/-- `np.strings.strip` and friends. `chars = none` strips whitespace. -/
def stripImpl (k : Kind) (mode : Strip) (a0 : Str) (chars : Option Str) : Str :=
  let a := readStr k a0
  readStr k <| match chars with
  | none => stripCore mode (isSpace k) (fun c => isSpace k c || (k != .T && c == 0)) a
  | some c0 =>
    let ch := readStr k c0
    if ch.isEmpty then a else stripCore mode (fun c => ch.contains c) (fun c => ch.contains c) a

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
