import NumpyLean.Common.Intp
import NumpyLean.Indexing.Model

/-
Models of integer-valued library functions of NumPy 2.5.4: the length and values of `arange` for Python integer arguments (`_core/src/multiarray/ctors.c`), `binary_repr` and `base_repr` (`_core/numeric.py`), `packbits` and `unpackbits` (`_core/src/multiarray/compiled_base.c`), the three `kind` paths of `isin` (`lib/_arraysetops_impl.py`), `digitize` (`lib/_function_base_impl.py`) and `bincount` (`compiled_base.c`).

C signed overflow is undefined behaviour. Where the source can overflow, the model assumes the two's complement wrap that the arm64 and x86-64 builds show.
-/
namespace NumpyLean.LibInt

/-! ## Doubles of integers and of quotients

Several paths convert a Python integer or a quotient of Python integers to a C `double`. Python rounds both conversions correctly, to nearest with ties to even. The helpers below compute that rounding with integer arithmetic. They use fuel instead of well-founded recursion so that the kernel can evaluate them with `decide`.
-/

/-- The number of binary digits of `n`, with `fuel` steps at most. -/
def bitLenAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n = 0 then 0 else bitLenAux fuel (n / 2) + 1

/-- The number of binary digits of `n`. 4096 steps are enough for every integer below `2 ^ 4096`, which covers every input that is used here. -/
def bitLen (n : Nat) : Nat := bitLenAux 4096 n

/-- The floor and remainder of `n / (d * 2 ^ e)`, together with the divisor, for an exponent of either sign. -/
def scaledQuot (n d : Nat) (e : Int) : Nat × Nat × Nat :=
  if e ≥ 0 then
    let D := d * 2 ^ e.toNat
    (n / D, n % D, D)
  else
    let N := n * 2 ^ (-e).toNat
    (N / d, N % d, d)

/--
The double nearest to `n / d` for positive `n` and `d`, as a pair `(m, e)` with value `m * 2 ^ e` and `2 ^ 52 ≤ m < 2 ^ 53`. Ties go to the even mantissa. Subnormal results and overflow to infinity are not modelled here; the callers handle the ranges where they matter.
-/
def roundQuot (n d : Nat) : Nat × Int :=
  let e0 : Int := (bitLen n : Int) - (bitLen d : Int) - 53
  let q0 := (scaledQuot n d e0).1
  let e := if q0 ≥ 2 ^ 53 then e0 + 1 else e0
  let (q, r, D) := scaledQuot n d e
  let m := if 2 * r > D ∨ (2 * r = D ∧ q % 2 = 1) then q + 1 else q
  if m = 2 ^ 53 then (2 ^ 52, e + 1) else (m, e)

/-- The value `m * 2 ^ e` of a double that is known to be an integer, that is with `e ≥ 0` or with `m` divisible by `2 ^ (-e)`. -/
def dyadicInt (m : Nat) (e : Int) : Int :=
  if e ≥ 0 then ((m * 2 ^ e.toNat : Nat) : Int) else ((m / 2 ^ (-e).toNat : Nat) : Int)

/-- The double nearest to the integer `x`, which is again an integer. Integers below `2 ^ 53` in absolute value are exact. -/
def roundInt (x : Int) : Int :=
  if x.natAbs < 2 ^ 53 then x
  else
    let (m, e) := roundQuot x.natAbs 1
    if x < 0 then -(dyadicInt m e) else dyadicInt m e

/-- True when the integer `x` converts to a finite double, as `PyLong_AsDouble` requires. Otherwise Python raises `OverflowError`. -/
def fitsDouble (x : Int) : Bool := decide ((roundInt x).natAbs < 2 ^ 1024)

/-- `ceil` of the double `m * 2 ^ e` with the given sign. -/
def ceilDyadic (neg : Bool) (m : Nat) (e : Int) : Int :=
  if e ≥ 0 then
    let v : Int := ((m * 2 ^ e.toNat : Nat) : Int)
    if neg then -v else v
  else
    let p := 2 ^ (-e).toNat
    if neg then -((m / p : Nat) : Int) else (((m + p - 1) / p : Nat) : Int)

/-! ## arange -/

/-- The data types that `arange` can produce in this model. `int bits signed` is a fixed-width integer type. -/
inductive ADType where
  | bool
  | int (bits : Nat) (signed : Bool)
  | float64
  | object
  deriving Repr, DecidableEq

def ADType.itemsize : ADType → Int
  | .bool => 1
  | .int bits _ => (bits / 8 : Nat)
  | .float64 => 8
  | .object => 8

/-- The dtype that array discovery gives a single Python integer: `int64` when it fits, `uint64` when it fits that, and `object` otherwise. -/
def discoverInt (x : Int) : ADType :=
  if intpMin ≤ x ∧ x ≤ intpMax then .int 64 true
  else if 0 ≤ x ∧ x < 2 ^ 64 then .int 64 false
  else .object

/--
One step of the chain `dtype = PyArray_DescrFromObject(x, dtype)` at `ctors.c:3318-3330`, which promotes the discovered dtype of `x` with the running dtype by the legacy rules. The running dtype starts as `intp` ("intentionally made to be at least NPY_LONG", `ctors.c:3317`), so it is only ever `int64`, `float64` or `object`, and `int64` with `uint64` promotes to `float64`.
-/
def promoteDiscover (acc : ADType) (x : Int) : ADType :=
  match acc, discoverInt x with
  | .object, _ => .object
  | _, .object => .object
  | .float64, _ => .float64
  | _, .int 64 false => .float64
  | a, _ => a

inductive ArangeErr where
  /-- `ZeroDivisionError` "division by zero" from `PyNumber_TrueDivide` at `ctors.c:3213`. -/
  | zeroDivision
  /-- `ValueError` "Maximum allowed size exceeded" at `ctors.c:3383`, which replaces the `OverflowError` of `_arange_safe_ceil_to_intp` (`ctors.c:3080`) or of the true division. -/
  | maxSize
  /-- `ValueError` "array is too big; `arr.size * arr.dtype.itemsize` is larger than the maximum possible size." from the array constructor at `ctors.c:3392`. -/
  | tooBig
  /-- `OverflowError` from `setitem` at `ctors.c:3404` or `ctors.c:3410`, when `start` or `start + step` does not fit the dtype. -/
  | setitem
  /-- `TypeError` "arange() is only supported for booleans when the result has at most length 2." from `BOOL_fill` (`arraytypes.c.src:3744`). -/
  | boolFill
  deriving Repr, DecidableEq

/--
`_calc_length` at `ctors.c:3181` for Python integer `start`, `stop` and nonzero `step`, followed by `_arange_safe_ceil_to_intp` at `ctors.c:3069`. Python computes `(stop - start) / step` as the double nearest to the exact quotient, `ceil` is taken of that double, and the result must lie in `[(double)NPY_MIN_INTP, (double)NPY_MAX_INTP]`, which is `[-2^63, 2^63]`. `none` is the `OverflowError`.

A quotient strictly between -1 and 1 has ceiling 1 or 0, both through the general path and through the underflow branch at `ctors.c:3259`, so the model decides it by the signs. A ceiling of exactly `2^63` passes the range check and is then cast with `(npy_intp)ivalue` at `ctors.c:3086`, which is undefined behaviour in C. The arm64 instruction `fcvtzs` saturates it to `2^63 - 1`, and the model follows arm64. On x86-64 the same cast gives `-2^63`.
-/
def arangeCeil (delta step : Int) : Option Int :=
  if delta = 0 then some 0
  else
    let neg := decide (delta < 0) != decide (step < 0)
    let a := delta.natAbs
    let b := step.natAbs
    if a < b then some (if neg then 0 else 1)
    else
      let (m, e) := roundQuot a b
      let c := ceilDyadic neg m e
      if c < -(2 ^ 63) ∨ c > 2 ^ 63 then none
      else if c = 2 ^ 63 then some intpMax
      else some c

/-- The value that `setitem` stores for a Python integer, or `none` for the `OverflowError` of an out-of-bounds integer or of an integer too large for a double. -/
def setitemInt (dt : ADType) (x : Int) : Option Int :=
  match dt with
  | .bool => some (if x = 0 then 0 else 1)
  | .int bits true => if -(2 ^ (bits - 1)) ≤ x ∧ x < 2 ^ (bits - 1) then some x else none
  | .int bits false => if 0 ≤ x ∧ x < 2 ^ bits then some x else none
  | .float64 => if fitsDouble x then some (roundInt x) else none
  | .object => some x

/--
Element `i` of the result from the first two stored values, as the `fill` functions compute it at `arraytypes.c.src:3803` (`buffer[i] = start + i*delta` with `delta = buffer[1] - buffer[0]` in the element type) and at `arraytypes.c.src:3754` for objects (repeated Python addition of `delta`). Integer types wrap and objects are exact. For doubles, `delta` is rounded once, and the arm64 build contracts `start + i*delta` into one fused multiply-add, so that the sum is rounded only once. A build without contraction rounds the product as well, so the double values of long results are platform dependent.
-/
def arangeElem (dt : ADType) (v0 v1 : Int) (i : Nat) : Int :=
  if i = 0 then v0
  else if i = 1 then v1
  else
    match dt with
    | .int bits true => wrapSigned bits (v0 + i * (v1 - v0))
    | .int bits false => wrapUnsigned bits (v0 + i * (v1 - v0))
    | .float64 => roundInt (v0 + i * roundInt (v1 - v0))
    | _ => v0 + i * (v1 - v0)

/-- The result of `arange`: the dtype, the length, and the first two stored values (zero when the result is shorter). -/
structure ArangeOut where
  dtype : ADType
  length : Int
  v0 : Int
  v1 : Int
  deriving Repr, DecidableEq

/--
`PyArray_ArangeObj` at `ctors.c:3291` for Python integer `start` and `stop`, an optional Python integer `step` and an optional dtype. The order of the steps follows the source: dtype discovery (`ctors.c:3316-3331`), the default step of 1, the length (`ctors.c:3377`), the clamp of a negative length to 0 (`ctors.c:3387`), the array constructor with its size check (`ctors.c:3392`), `setitem` of `start` and of `start + step` (`ctors.c:3404` and `3410`) and `fill` (`ctors.c:3419`).
-/
def arangeObj (start stop : Int) (step : Option Int) (dtype : Option ADType) : Except ArangeErr ArangeOut := do
  let dt := match dtype with
    | some d => d
    | none =>
      let d := promoteDiscover (promoteDiscover (.int 64 true) start) stop
      match step with
      | some s => promoteDiscover d s
      | none => d
  let s := step.getD 1
  if s = 0 then throw .zeroDivision
  let len ← match arangeCeil (stop - start) s with
    | none => throw .maxSize
    | some l => pure (max 0 l)
  if len * dt.itemsize > intpMax then throw .tooBig
  if len = 0 then return ⟨dt, 0, 0, 0⟩
  let v0 ← match setitemInt dt start with
    | none => throw .setitem
    | some v => pure v
  if len = 1 then return ⟨dt, 1, v0, 0⟩
  let v1 ← match setitemInt dt (start + s) with
    | none => throw .setitem
    | some v => pure v
  if len = 2 then return ⟨dt, 2, v0, v1⟩
  if dt = .bool then throw .boolFill
  return ⟨dt, len, v0, v1⟩

/-- The values of a result, for a length that is small enough to list. -/
def ArangeOut.values (o : ArangeOut) : List Int :=
  (List.range o.length.toNat).map (arangeElem o.dtype o.v0 o.v1)

/-! ## binary_repr and base_repr -/

/-- Python `f'{n:b}'` for a non-negative integer. -/
def binStr (n : Nat) : String := String.ofList (Nat.toDigits 2 n)

def zeros (k : Int) : String := "".pushn '0' k.toNat

def ones (k : Int) : String := "".pushn '1' k.toNat

inductive ReprErr where
  /-- `ValueError` "Insufficient bit width=... provided for binwidth=..." from `err_if_insufficient` at `numeric.py:2064`. -/
  | insufficient (width binwidth : Int)
  /-- `ValueError` "Bases greater than 36 not handled in base_repr." at `numeric.py:2146`. -/
  | baseTooLarge
  /-- `ValueError` "Bases less than 2 not handled in base_repr." at `numeric.py:2148`. -/
  | baseTooSmall
  deriving Repr, DecidableEq

/-- `width is not None and width < binwidth` in `err_if_insufficient` at `numeric.py:2064`. -/
def checkWidth (width : Option Int) (binwidth : Int) : Except ReprErr Unit :=
  match width with
  | some w => if w < binwidth then .error (.insufficient w binwidth) else .ok ()
  | none => .ok ()

/--
`binary_repr` at `numeric.py:1999` for a Python integer. The zero case at `numeric.py:2074` is `'0' * (width or 1)`, so a width of `None` or 0 gives `'0'` and a negative width gives the empty string. Positive numbers are zero filled. Negative numbers with a width are written in two's complement with the width fix of gh-8679 at `numeric.py:2093`.
-/
def binaryRepr (num : Int) (width : Option Int) : Except ReprErr String :=
  if num = 0 then
    .ok (zeros (match width with | none => 1 | some 0 => 1 | some w => w))
  else if num > 0 then
    let binary := binStr num.toNat
    let binwidth : Int := binary.length
    let outwidth := match width with | none => binwidth | some w => max binwidth w
    (checkWidth width binwidth).map fun _ => zeros (outwidth - binwidth) ++ binary
  else
    match width with
    | none => .ok ("-" ++ binStr num.natAbs)
    | some w =>
      let pw0 : Int := (binStr num.natAbs).length
      let poswidth := if (2 : Int) ^ (pw0 - 1).toNat = -num then pw0 - 1 else pw0
      let twocomp := (2 : Int) ^ (poswidth + 1).toNat + num
      let binary := binStr twocomp.toNat
      let binwidth : Int := binary.length
      let outwidth := max binwidth w
      (checkWidth width binwidth).map fun _ => ones (outwidth - binwidth) ++ binary

def digitChars : List Char := "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ".toList

/-- The digits of `n` in base `b`, least significant first, as the `while num` loop of `base_repr` appends them. -/
def baseDigitsAux (b : Nat) : Nat → Nat → List Char
  | 0, _ => []
  | fuel + 1, n => if n = 0 then [] else digitChars.getD (n % b) '?' :: baseDigitsAux b fuel (n / b)

/--
`base_repr` at `numeric.py:2106`. The list `res` collects the digits least significant first, then the padding string when `padding` is nonzero (`numeric.py:2156`), then `'-'`, and the result is `''.join(reversed(res or '0'))` (`numeric.py:2160`). The string `'0'` is used only when `res` is empty, so a zero with nonzero padding gets the padding and no digit.
-/
def baseRepr (number : Int) (base : Int) (padding : Int) : Except ReprErr String :=
  if base > 36 then .error .baseTooLarge
  else if base < 2 then .error .baseTooSmall
  else
    let num := number.natAbs
    let res : List String := (baseDigitsAux base.toNat (num + 1) num).map (fun c => String.singleton c)
    let res := if padding ≠ 0 then res ++ [zeros padding] else res
    let res := if number < 0 then res ++ ["-"] else res
    if res.isEmpty then .ok "0" else .ok (String.join res.reverse)

/-! ## packbits and unpackbits

An array is a shape and a flat list of values in C order. `axis = none` is `NPY_RAVEL_AXIS`.
-/

inductive BitsErr where
  /-- `TypeError` "Expected an input array of integer or boolean data type" at `compiled_base.c:1777`, or "Expected an input array of unsigned byte data type" at `compiled_base.c:1883`. -/
  | dtype
  /-- `AxisError` from `check_and_adjust_axis` in `PyArray_CheckAxis` at `ctors.c:2927`. -/
  | axis
  /-- `ValueError` "-count larger than number of elements" at `compiled_base.c:1924`. -/
  | count
  /-- `ValueError` "negative dimensions are not allowed" from the array constructor. -/
  | negDim
  deriving Repr, DecidableEq

def prod (l : List Int) : Int := l.foldl (· * ·) 1

/--
`PyArray_CheckAxis(arr, &axis, 0)` at `ctors.c:2886`. With the ravel axis, or for a 0-d array, an array that is not 1-d is flattened, and the ravel axis becomes 0. Then the axis is checked against the new number of dimensions. The result is the new shape and the axis.
-/
def checkAxis (shape : List Int) (axis : Option Int) : Except BitsErr (List Int × Nat) :=
  let (shape', ax) :=
    if axis.isNone ∨ shape.length = 0 then
      if shape.length ≠ 1 then ([prod shape], axis.getD 0) else (shape, 0)
    else (shape, axis.getD 0)
  let n : Int := shape'.length
  if ax < -n ∨ ax ≥ n then .error .axis
  else .ok (shape', (if ax < 0 then ax + n else ax).toNat)

/-- The number of elements before and after an axis, and the axis length. -/
def splitAt (shape : List Int) (axis : Nat) : Int × Int × Int :=
  (prod (shape.take axis), shape.getD axis 0, prod (shape.drop (axis + 1)))

/--
`pack_inner` at `compiled_base.c:1620` for one output byte: the `maxi` input elements from position `8 * b` on, each 1 when nonzero. The big order shifts `build` left and puts the first element in the top bit (`compiled_base.c:1731`). The little order shifts right and puts the first element in the bottom bit (`compiled_base.c:1744`). A short last group is shifted so that its bits start at the top or the bottom. The SIMD block above the scalar loop computes the same bytes for full groups.
-/
def packByte (bits : List Bool) (big : Bool) : Int :=
  let k := bits.length
  if big then
    (List.range k).foldl (fun acc i => acc + if bits.getD i false then 2 ^ (7 - i) else 0) 0
  else
    (List.range k).foldl (fun acc i => acc + if bits.getD i false then 2 ^ i else 0) 0

/--
`pack_bits` at `compiled_base.c:1760`. `isInt` says whether the input has an integer or boolean dtype. The output axis has length `((n - 1) >> 3) + 1` (`compiled_base.c:1821`). Each output byte is computed independently from its group of eight inputs along the axis.
-/
def packbits (shape : List Int) (data : List Int) (isInt : Bool) (axis : Option Int) (big : Bool) :
    Except BitsErr (List Int × List Int) := do
  if !isInt then throw .dtype
  let (shp, ax) ← checkAxis shape axis
  if shp.length = 0 then
    -- The 0-d branch at `compiled_base.c:1788`. `PyArray_CheckAxis` has already made every array at least 1-d, so this branch is not reached.
    return ([], [if data.any (· ≠ 0) then 1 else 0])
  let (outer, n, inner) := splitAt shp ax
  let nout := Int.shiftRight (n - 1) 3 + 1
  let outShape := shp.set ax nout
  let total := outer * nout * inner
  let out := (List.range total.toNat).map fun (idx0 : Nat) =>
    let idx : Int := idx0
    let j := idx % inner
    let b := (idx / inner) % nout
    let o := idx / inner / nout
    let ks := (List.range 8).map (fun (t : Nat) => 8 * b + (t : Int)) |>.filter (· < n)
    packByte (ks.map fun k => data.getD ((o * n + k) * inner + j).toNat 0 ≠ 0) big
  return (outShape, out)

/--
`unpack_bits` at `compiled_base.c:1865`. `isUbyte` says whether the input dtype is `uint8`. The output axis length is `8 * n` computed in `npy_intp` (`compiled_base.c:1915`, wrapped here), then replaced by `count` when it is non-negative or reduced by `-count` when it is negative (`compiled_base.c:1921-1931`). Positions past `8 * n` are padding zeros (`compiled_base.c:1953`).

The output comes from `PyArray_NewFromDescr` without initialisation, and every element is written inside the loop `while (PyArray_ITER_NOTDONE(it))` over the input. `PyArray_IterAllButAxis` (`iterators.c:261`) keeps the iterator size at 0 when the input is empty, so for an empty input and a non-empty output nothing is written, not even the padding. The model returns `none` for the data in that case, which stands for uninitialised memory.
-/
def unpackbits (shape : List Int) (data : List Int) (isUbyte : Bool) (axis : Option Int) (count : Option Int) (big : Bool) :
    Except BitsErr (List Int × Option (List Int)) := do
  if !isUbyte then throw .dtype
  let (shp, ax) ← checkAxis shape axis
  let (outer, n, inner) := splitAt shp ax
  let d0 := wrap64 (n * 8)
  let dim ← match count with
    | none => pure d0
    | some c =>
      if c < 0 then
        let d := wrap64 (d0 + c)
        if d < 0 then throw .count else pure d
      else pure c
  if dim < 0 then throw .negDim
  let outShape := shp.set ax dim
  let total := outer * dim * inner
  if outer * n * inner = 0 ∧ total > 0 then return (outShape, none)
  let avail := wrap64 (n * 8)
  let out := (List.range total.toNat).map fun (idx0 : Nat) =>
    let idx : Int := idx0
    let j := idx % inner
    let t := (idx / inner) % dim
    let o := idx / inner / dim
    if t < avail then
      let byte := data.getD ((o * n + t / 8) * inner + j).toNat 0
      let sh := if big then 7 - t % 8 else t % 8
      (byte / 2 ^ sh.toNat) % 2
    else 0
  return (outShape, some out)

/-! ## isin -/

/-- The integer dtypes used for `isin`. -/
inductive IDType where
  | i8 | u8 | i64 | u64
  deriving Repr, DecidableEq

def IDType.signed : IDType → Bool
  | .i8 => true | .i64 => true | _ => false

/-- `np.iinfo(dtype).max`. -/
def IDType.imax : IDType → Int
  | .i8 => 127 | .u8 => 255 | .i64 => intpMax | .u64 => 2 ^ 64 - 1

/-- True when the promotion of the two dtypes is `float64`, which happens for a signed type with `uint64`. Every other pair promotes to an integer type that holds both value ranges. -/
def promotesToFloat (a b : IDType) : Bool :=
  (a.signed && b == .u64) || (b.signed && a == .u64)

inductive IsinKind where
  | auto | sort | table
  deriving Repr, DecidableEq

inductive IsinErr where
  /-- `RuntimeError` "You have specified kind='table', but the range of values in `ar2` or `ar1` exceed the maximum integer of the datatype." at `_arraysetops_impl.py:896`. -/
  | tableRange
  deriving Repr, DecidableEq

/--
The limit of the loop path at `_arraysetops_impl.py:917`: the loop runs when `len(ar2) < 10 * len(ar1) ** 0.145`, which is `len(ar2) < isinLoopLimit len(ar1)`. The power is a `libm` function, so the table was computed with CPython floats for `len(ar1)` up to 64. Longer inputs are outside the model.
-/
def isinLoopTable : List Nat :=
  [0, 10, 12, 12, 13, 13, 13, 14, 14, 14, 14, 15, 15, 15, 15, 15, 15, 16, 16, 16, 16, 16, 16, 16, 16, 16,
   17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18,
   18, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 19]

def isinLoopLimit (n1 : Nat) : Nat := isinLoopTable.getD n1 0

/-- Sorted distinct values. -/
def uniqueSorted (l : List Int) : List Int := (l.mergeSort (· ≤ ·)).eraseDups

/-- The position of `x` in a list, as `return_inverse` of `np.unique` gives it. -/
def indexOf (l : List Int) (x : Int) : Nat := l.idxOf x

/--
The sort path at `_arraysetops_impl.py:929-950` with `assume_unique=False`. Both inputs go through `np.unique` in their own dtypes, `np.concatenate` converts them to the promoted dtype, a stable merge sort orders the result, and each element is compared with its successor. When the promoted dtype is `float64`, the comparison is between the doubles of the values.
-/
def isinSort (a1 a2 : List Int) (d1 d2 : IDType) (invert : Bool) : List Bool :=
  let u1 := uniqueSorted a1
  let u2 := uniqueSorted a2
  let key : Int → Int := if promotesToFloat d1 d2 then roundInt else id
  let ar := (u1 ++ u2).map key
  let tagged := (List.range ar.length).map fun i => (ar.getD i 0, i)
  let sorted := tagged.mergeSort (fun p q => p.1 ≤ q.1)
  let flags := (List.range sorted.length).map fun k =>
    let cur := (sorted.getD k (0, 0)).1
    match sorted[k + 1]? with
    | some nxt => if invert then cur != nxt.1 else cur == nxt.1
    | none => invert
  let ret := fun (pos : Nat) =>
    match (List.range sorted.length).find? (fun k => (sorted.getD k (0, 0)).2 = pos) with
    | some k => flags.getD k false
    | none => false
  a1.map fun x => ret (indexOf u1 x)

/-- Exact membership, which the table path and the loop path compute. NumPy 2 compares `int64` with `uint64` exactly. -/
def isinExact (a1 a2 : List Int) (invert : Bool) : List Bool :=
  a1.map fun x => if invert then !(a2.contains x) else a2.contains x

/--
`_isin` at `_arraysetops_impl.py:806` for integer arrays. The table method is used for `kind` None or 'table' (`_arraysetops_impl.py:821`) when the range of `ar2` fits its dtype and, for None, when the range is at most six times the total size (`_arraysetops_impl.py:843-845`). Otherwise 'table' raises and the others fall through to the loop when `ar2` is short (`_arraysetops_impl.py:917`) and to the sort path otherwise.
-/
def isin (a1 a2 : List Int) (d1 d2 : IDType) (kind : IsinKind) (invert : Bool) : Except IsinErr (List Bool) := do
  if kind ≠ .sort then
    if a2.isEmpty then return a1.map fun _ => invert
    let mn := a2.foldl min (a2.headD 0)
    let mx := a2.foldl max (a2.headD 0)
    let range := mx - mn
    let below := decide (range ≤ 6 * (a1.length + a2.length))
    let safe := decide (range ≤ d2.imax)
    if safe && (below || kind == .table) then return isinExact a1 a2 invert
    if kind = .table then throw .tableRange
  if a2.length < isinLoopLimit a1.length then return isinExact a1 a2 invert
  return isinSort a1 a2 d1 d2 invert

/-- The range of `ar2` that the table path would allocate, used by the tests to skip large tables. -/
def isinTableRange (a2 : List Int) : Int := a2.foldl max (a2.headD 0) - a2.foldl min (a2.headD 0)

/-! ## digitize -/

/--
`check_array_monotonic` at `compiled_base.c:35`, which `_monotonicity` calls on the bins converted to `double`. The model takes the doubles of integer bins. It skips the leading run of equal values (`compiled_base.c:48`) and then decides the direction from the first change.
-/
def monotonic (bins : List Int) : Int :=
  let a := bins.map roundInt
  match a with
  | [] => 1
  | first :: rest =>
    match rest.dropWhile (· = first) with
    | [] => 1
    | next :: more =>
      let pairs := (next :: more).zip more
      if first < next then (if pairs.any (fun p => p.1 > p.2) then 0 else 1)
      else (if pairs.any (fun p => p.1 < p.2) then 0 else -1)

inductive DigitizeErr where
  /-- `ValueError` "bins must be monotonically increasing or decreasing" at `_function_base_impl.py:5768`. -/
  | notMonotonic
  deriving Repr, DecidableEq

/--
`digitize` at `_function_base_impl.py:5766-5776` for `int64` inputs and bins. The direction comes from the double check above, and the search itself is `searchsorted` on the `int64` values, modelled in `NumpyLean.Indexing.searchsorted`.
-/
def digitize (x bins : List Int) (right : Bool) : Except DigitizeErr (List Int) :=
  let mono := monotonic bins
  if mono = 0 then .error .notMonotonic
  else if mono = -1 then
    match Indexing.searchsorted bins.reverse x (!right) none with
    | .ok r => .ok (r.map fun v => (bins.length : Int) - v)
    | .error _ => .ok []
  else
    match Indexing.searchsorted bins x (!right) none with
    | .ok r => .ok r
    | .error _ => .ok []

/-! ## bincount -/

inductive BincountErr where
  /-- `ValueError` "'minlength' must not be negative" at `compiled_base.c:201`. -/
  | negMinlength
  /-- `ValueError` "'list' argument must have no negative elements" at `compiled_base.c:219`. -/
  | negElement
  /-- `ValueError` "negative dimensions are not allowed" from `PyArray_ZEROS`. -/
  | negDim
  /-- `ValueError` "array is too big; ..." from `PyArray_ZEROS`. -/
  | tooBig
  deriving Repr, DecidableEq

/-- The size check of the array constructor for a 1-d array of `npy_intp`. -/
def zerosCheck (n : Int) : Except BincountErr Unit :=
  if n < 0 then .error .negDim else if n * 8 > intpMax then .error .tooBig else .ok ()

/--
`arr_bincount` at `compiled_base.c:115` without weights, for an `int64` list. The output length is `mx + 1` (`compiled_base.c:222`), which wraps for `mx = 2^63 - 1`, raised to `minlength` if that is larger. The result is the length and the counts, listed only for lengths up to `cap`.
-/
def bincount (l : List Int) (minlength : Int) (cap : Int) : Except BincountErr (Int × List Int) := do
  if minlength < 0 then throw .negMinlength
  if l.isEmpty then
    zerosCheck minlength
    return (minlength, if minlength ≤ cap then (List.range minlength.toNat).map fun _ => 0 else [])
  let mn := l.foldl min (l.headD 0)
  let mx := l.foldl max (l.headD 0)
  if mn < 0 then throw .negElement
  let size := max (wrap64 (mx + 1)) minlength
  zerosCheck size
  return (size, if size ≤ cap then (List.range size.toNat).map fun (i : Nat) => ((l.filter (· = (i : Int))).length : Int) else [])

/-! ## unique -/

/-- The four arrays that `_unique1d` computes for an integer array, with `return_index`, `return_inverse` and `return_counts` all set. -/
structure UniqueOut where
  values : List Int
  index : List Nat
  inverse : List Nat
  counts : List Nat
  deriving Repr, DecidableEq

/-- `ar.argsort(kind='mergesort')`, which is a stable sort of the positions by value (`_arraysetops_impl.py:379`). With `return_inverse` alone NumPy uses `quicksort` there, which is not stable, but then only the values and the counts depend on the permutation and they do not depend on how ties are ordered. -/
def argsortStable (ar : List Int) : List Nat :=
  (List.range ar.length).mergeSort (fun i j => decide (ar.getD i 0 ≤ ar.getD j 0))

/-- `x[mask]` for a list. -/
def selMask {α : Type} (l : List α) (mask : List Bool) : List α :=
  (l.zip mask).filterMap fun (x, m) => if m then some x else none

/--
`_unique1d` at `_arraysetops_impl.py:350-433` on the sort path, for an integer array, in the order of the source. `perm` sorts the array, `aux` is the sorted array, and `mask[k]` marks the first element of each run of equal values (`mask[:1] = True` and `mask[1:] = aux[1:] != aux[:-1]`). The values are `aux[mask]` and the first indices are `perm[mask]`. The inverse is `inv_idx[perm] = np.cumsum(mask) - 1`, and the counts are the differences of the positions of the marks followed by the size. The hash path that `unique_values` may take returns the same sorted values.
-/
def unique1d (ar : List Int) : UniqueOut :=
  let perm := argsortStable ar
  let aux := perm.map fun i => ar.getD i 0
  let n := aux.length
  let mask : List Bool := (List.range n).map fun k => k == 0 || aux.getD k 0 != aux.getD (k - 1) 0
  let imask : List Nat := (List.range n).map fun k => ((mask.take (k + 1)).filter id).length - 1
  let pos : List Nat := (List.range n).filter fun k => mask.getD k false
  let idx := pos ++ [n]
  { values := selMask aux mask
    index := selMask perm mask
    inverse := (List.range n).map fun i => imask.getD (perm.idxOf i) 0
    counts := (idx.zip idx.tail).map fun (a, b) => b - a }

/-! ## fill_diagonal -/

inductive FillDiagErr where
  /-- `ValueError` "array must be at least 2-d" at `_index_tricks_impl.py:906`. -/
  | tooFewDims
  /-- `ValueError` "All dimensions of input must be of equal length" at `_index_tricks_impl.py:919`. -/
  | unequalDims
  deriving Repr, DecidableEq

/-- The sum of `np.cumprod(shape[:-1])`. -/
def cumprodSum (shape : List Nat) : Nat :=
  let pre := shape.dropLast
  ((List.range pre.length).map fun k => ((pre.take (k + 1)).foldl (· * ·) 1)).foldl (· + ·) 0

/-- True when `np.diff(shape)` is zero everywhere. -/
def allEqual (shape : List Nat) : Bool :=
  (shape.zip shape.tail).all fun (a, b) => a == b

/--
`fill_diagonal` at `_index_tricks_impl.py:905-923`. It returns the flat indices that `a.flat[:end:step] = val` writes, in order. For two dimensions `step` is `shape[1] + 1` and `end` is `shape[1] ** 2` unless `wrap` is set. For more dimensions all lengths must agree and `step = 1 + cumprod(shape[:-1]).sum()`. The slice stops at `min(end, size)`.
-/
def fillDiagonal (shape : List Nat) (wrap : Bool) : Except FillDiagErr (List Nat) :=
  if shape.length < 2 then .error .tooFewDims
  else
    let size := shape.foldl (· * ·) 1
    if shape.length == 2 then
      let c := shape.getD 1 0
      let step := c + 1
      let stop := if wrap then size else min (c * c) size
      .ok ((List.range ((stop + step - 1) / step)).map (· * step))
    else if !allEqual shape then .error .unequalDims
    else
      let step := 1 + cumprodSum shape
      .ok ((List.range ((size + step - 1) / step)).map (· * step))

end NumpyLean.LibInt
