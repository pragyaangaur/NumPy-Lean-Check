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
  /-- Any error that comes from allocating the result: a width or size too large for the array constructor or the allocator. -/
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

end NumpyLean.Strings
