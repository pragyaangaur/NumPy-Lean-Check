import NumpyLean.Common.Intp

/-
Models of the integer and slice index paths of `numpy/_core/src/multiarray/mapping.c`, of `ravel_multi_index` and `unravel_index` in `compiled_base.c`, and of `take`, `put`, `repeat`, `choose`, `diagonal` and `searchsorted` in `item_selection.c` and `npysort/binsearch.cpp`, all at NumPy 2.5.4.

C signed overflow is undefined behaviour. Where a model applies `wrap64`, it assumes the two's complement wrap that the arm64 and x86-64 builds produce.
-/
namespace NumpyLean.Indexing

/-! ## check_and_adjust_index -/

inductive IndexErr where
  /-- "index %d is out of bounds for axis %d with size %d" -/
  | outOfBounds
  deriving Repr, DecidableEq

/--
`check_and_adjust_index` at `_core/src/multiarray/common.h:167-191`. `maxItem` is a dimension, so it is never negative and `-maxItem` cannot overflow.
-/
def checkAndAdjustIndex (index maxItem : Int) : Except IndexErr Int :=
  if index < -maxItem ∨ index ≥ maxItem then .error .outOfBounds
  else if index < 0 then .ok (index + maxItem)
  else .ok index

/-! ## A single Python integer as an index -/

inductive IntIndexErr where
  /-- `IndexError`, "index %d is out of bounds for axis %d with size %d" -/
  | outOfBounds
  /-- `OverflowError`, "Python int too large to convert to C long" -/
  | overflow
  /-- `IndexError`, "only integers, slices (`:`), ellipsis (`...`), numpy.newaxis (`None`) and integer or boolean arrays are valid indices" -/
  | notAnIndex
  deriving Repr, DecidableEq

/--
`a[i]` for a Python `int` `i` on an axis of length `n`.

`prepare_index` at `mapping.c:373-389` first tries `PyArray_PyIntAsIntp`. When the value does not fit in `npy_intp`, the error is cleared and the value goes through `PyArray_FROM_O` at `mapping.c:400`. A value in `[2**63, 2**64)` becomes a 0-d `uint64` array, and the conversion back to `npy_intp` at `mapping.c:587` raises `OverflowError`, which is not cleared. Any other value becomes a 0-d object array, which is not a valid index. A fitting value reaches `check_and_adjust_index` from `get_item_pointer` or `get_view_from_index` (`mapping.c:836`, `mapping.c:880`).
-/
def pyIntIndex (n i : Int) : Except IntIndexErr Int :=
  if inIntp i then
    match checkAndAdjustIndex i n with
    | .ok k => .ok k
    | .error .outOfBounds => .error .outOfBounds
  else if (2 : Int) ^ 63 ≤ i ∧ i < (2 : Int) ^ 64 then .error .overflow
  else .error .notAnIndex

/-! ## Slices -/

inductive SliceErr where
  /-- `ValueError`, "slice step cannot be zero" -/
  | zeroStep
  deriving Repr, DecidableEq

/-- `_PyEval_SliceIndex` in CPython clamps a Python `int` to the `Py_ssize_t` range through `PyNumber_AsSsize_t(v, NULL)`. -/
def clampSsize (x : Int) : Int := max intpMin (min intpMax x)

/--
`PySlice_Unpack` in CPython 3.13 (`Objects/sliceobject.c`). `none` stands for `None`. The result is `(start, stop, step)`.
-/
def sliceUnpack (start stop step : Option Int) : Except SliceErr (Int × Int × Int) := do
  let st ← match step with
    | none => pure 1
    | some s =>
      let s := clampSsize s
      if s = 0 then throw SliceErr.zeroStep
      -- A step of `PY_SSIZE_T_MIN` is replaced by `-PY_SSIZE_T_MAX`.
      else pure (if s < -intpMax then -intpMax else s)
  let a := match start with
    | none => if st < 0 then intpMax else 0
    | some v => clampSsize v
  let b := match stop with
    | none => if st < 0 then intpMin else intpMax
    | some v => clampSsize v
  return (a, b, st)

/-- One bound of `PySlice_AdjustIndices`. -/
def adjustBound (x length step : Int) : Int :=
  if x < 0 then
    let y := x + length
    if y < 0 then (if step < 0 then -1 else 0) else y
  else if x ≥ length then (if step < 0 then length - 1 else length)
  else x

/--
`PySlice_AdjustIndices` in CPython 3.13 (`Objects/sliceobject.c`). It returns the adjusted `(start, stop)` and the slice length. Both operands of the C division are non-negative here, so `Int.tdiv` and floor division agree.
-/
def adjustIndices (length start stop step : Int) : Int × Int × Int :=
  let a := adjustBound start length step
  let b := adjustBound stop length step
  let len :=
    if step < 0 then (if b < a then Int.tdiv (a - b - 1) (-step) + 1 else 0)
    else (if a < b then Int.tdiv (b - a - 1) step + 1 else 0)
  (a, b, len)

/--
The `HAS_SLICE` case of `get_view_from_index` at `mapping.c:898-915`. It calls `PySlice_GetIndicesEx` (unpack, then adjust) and replaces an empty slice by start 0 and step 1. The result is `(start, step, length)` of the view, in elements.
-/
def sliceView (n : Int) (start stop step : Option Int) : Except SliceErr (Int × Int × Int) := do
  let (a, b, st) ← sliceUnpack start stop step
  let (a', _, len) := adjustIndices n a b st
  if len ≤ 0 then return (0, 1, 0) else return (a', st, len)

/-! ## Clip modes -/

inductive ClipMode where
  | raise
  | wrap
  | clip
  deriving Repr, DecidableEq

/-! ## ravel_multi_index -/

inductive RavelErr where
  /-- "invalid dims: array size defined by dims is larger than the maximum possible size." -/
  | dimsTooLarge
  /-- "cannot unravel if shape has zero entries (is empty)." -/
  | zeroDim
  /-- "invalid entry in coordinates array" -/
  | invalidEntry
  deriving Repr, DecidableEq

/-- The stride loop at `compiled_base.c:1180-1206`, over the dimensions in the order the loop visits them. -/
def ravelStridesLoop : List Int → Int → Except RavelErr (List Int)
  | [], _ => .ok []
  | d :: rest, s =>
    let (ov, p) := mulSizesWithOverflow s d
    if ov then .error .dimsTooLarge
    else do
      let r ← ravelStridesLoop rest p
      return s :: r

/-- `ravel_strides` for order C (`fortran = false`) or F. -/
def ravelStrides (dims : List Int) (fortran : Bool) : Except RavelErr (List Int) :=
  if fortran then ravelStridesLoop dims 1
  else do
    let r ← ravelStridesLoop dims.reverse 1
    return r.reverse

/--
The per-coordinate switch of `ravel_multi_index_loop` at `compiled_base.c:1085-1117`. `none` means the raise mode found an invalid entry. C `%` truncates.
-/
def ravelCoord (mode : ClipMode) (m j : Int) : Option Int :=
  match mode with
  | .raise => if j < 0 ∨ j ≥ m then none else some j
  | .wrap =>
    if j < 0 then
      let j := wrap64 (j + m)
      if j < 0 then
        let j := Int.tmod j m
        some (if j ≠ 0 then wrap64 (j + m) else j)
      else some j
    else if j ≥ m then
      let j := wrap64 (j - m)
      if j ≥ m then some (Int.tmod j m) else some j
    else some j
  | .clip => if j < 0 then some 0 else if j ≥ m then some (m - 1) else some j

/-- The sum `raveled += j * ravel_strides[i]` at `compiled_base.c:1118`, with the C wrap. -/
def ravelLoop : List ClipMode → List Int → List Int → List Int → Int → Except RavelErr Int
  | mode :: ms, m :: ds, s :: ss, j :: js, acc =>
    match ravelCoord mode m j with
    | none => .error .invalidEntry
    | some j' => ravelLoop ms ds ss js (wrap64 (acc + wrap64 (j' * s)))
  | _, _, _, _, acc => .ok acc

/--
`arr_ravel_multi_index` at `compiled_base.c:1140` for one point. Each coordinate is converted by `astype_anyint`, which gives `int64` for a Python int that fits and `uint64` for one in `[2**63, 2**64)`. The iterator then casts to `intp` with `same_kind` casting, which wraps, so the model applies `wrap64`. The zero-dimension check at `compiled_base.c:1070` runs because the count is one.
-/
def ravelMultiIndex (coords dims : List Int) (modes : List ClipMode) (fortran : Bool) : Except RavelErr Int := do
  let strides ← ravelStrides dims fortran
  if dims.any (· == 0) then throw RavelErr.zeroDim
  ravelLoop modes dims strides (coords.map wrap64) 0

/-! ## unravel_index -/

inductive UnravelErr where
  /-- "dimensions are too large; arrays and shapes with a total size greater than 'intp' are not supported." -/
  | tooLarge
  /-- "index %d is out of bounds for array with size %d". The fields are the two numbers in the message. -/
  | outOfBounds (val size : Int)
  deriving Repr, DecidableEq

/-- `PyArray_OverflowMultiplyList` at `multiarraymodule.c:216-232`. It returns `-1` on overflow and stops at the first zero. -/
def overflowMultiplyList : List Int → Int → Int
  | [], prod => prod
  | d :: rest, prod =>
    if d = 0 then 0
    else
      let (ov, p) := mulSizesWithOverflow prod d
      if ov then -1 else overflowMultiplyList rest p

/-- The division loop of `unravel_index_loop` at `compiled_base.c:1309-1319`, over the dimensions in visit order. It returns the coordinates in visit order. -/
def unravelDigits : List Int → Int → List Int
  | [], _ => []
  | d :: rest, v => Int.tmod v d :: unravelDigits rest (Int.tdiv v d)

/--
`arr_unravel_index` at `compiled_base.c:1336` for one scalar index. The index goes through `astype_anyint` and a `same_kind` cast to `intp`, so a value in `[2**63, 2**64)` wraps. The bounds check is at `compiled_base.c:1303`.
-/
def unravelIndex (val : Int) (dims : List Int) (fortran : Bool) : Except UnravelErr (List Int) :=
  let size := overflowMultiplyList dims 1
  if size = -1 then .error .tooLarge
  else
    let v := wrap64 val
    if v < 0 ∨ v ≥ size then .error (.outOfBounds v size)
    else if fortran then .ok (unravelDigits dims v)
    else .ok (unravelDigits dims.reverse v).reverse

/-! ## The wrap loop of take, put and choose -/

/--
The `NPY_WRAP` loop shared by `npy_fasttake_impl` (`item_selection.c:97-108`), `PyArray_PutTo` (`item_selection.c:487-497`) and `PyArray_Choose` (`item_selection.c:1185-1196`). It adds or subtracts `maxItem` one step at a time. The result is the final index and the number of loop iterations, or `none` when the loop never ends, which happens when `maxItem` is zero and the loop is entered. For a positive `maxItem` the final index is the floor remainder.
-/
def wrapLoop (tmp maxItem : Int) : Option (Int × Nat) :=
  if tmp < 0 then
    if maxItem ≤ 0 then none
    else some (tmp % maxItem, ((-tmp + maxItem - 1) / maxItem).toNat)
  else if tmp ≥ maxItem then
    if maxItem ≤ 0 then none
    else some (tmp % maxItem, (tmp / maxItem).toNat)
  else some (tmp, 0)

/-- The `NPY_CLIP` branch shared by take, put and choose. -/
def clipIndex (tmp maxItem : Int) : Int :=
  if tmp < 0 then 0 else if tmp ≥ maxItem then maxItem - 1 else tmp

/-! ## take -/

inductive TakeErr where
  /-- `IndexError`, "index %d is out of bounds for axis %d with size %d" -/
  | outOfBounds
  /-- `IndexError`, "cannot do a non-empty take from an empty axes." -/
  | emptyAxis
  /-- The wrap loop never ends. -/
  | hang
  deriving Repr, DecidableEq

/--
`PyArray_TakeFrom` at `item_selection.c:234` and `npy_fasttake_impl` at `item_selection.c:41`, for a 1-D array of length `n` and one index. The result is the source position that is copied. Indices are converted to `intp` with `same_kind` casting (`item_selection.c:252`), so a `uint64` index wraps. The empty-axis check is at `item_selection.c:345`.
-/
def take1 (n idx : Int) (mode : ClipMode) : Except TakeErr Int :=
  let tmp := wrap64 idx
  if n = 0 then .error .emptyAxis
  else match mode with
    | .raise =>
      match checkAndAdjustIndex tmp n with
      | .ok k => .ok k
      | .error _ => .error .outOfBounds
    | .wrap =>
      match wrapLoop tmp n with
      | some (k, _) => .ok k
      | none => .error .hang
    | .clip => .ok (clipIndex tmp n)

/-! ## put -/

inductive PutErr where
  /-- `IndexError`, "cannot replace elements of an empty array" -/
  | emptyArray
  /-- `IndexError`, "index %d is out of bounds for axis %d with size %d" -/
  | outOfBounds
  /-- The wrap loop never ends. -/
  | hang
  deriving Repr, DecidableEq

/--
`PyArray_PutTo` at `item_selection.c:384` for a 1-D array of `n` elements, one index and `nv` values. The result is the position written, or `none` when nothing is written because `values` is empty (`item_selection.c:424`). The index is converted with `PyArray_ContiguousFromAny` to `intp`.
-/
def put1 (n idx nv : Int) (mode : ClipMode) : Except PutErr (Option Int) :=
  if n = 0 then .error .emptyArray
  else if nv ≤ 0 then .ok none
  else match mode with
    | .raise =>
      match checkAndAdjustIndex idx n with
      | .ok k => .ok (some k)
      | .error _ => .error .outOfBounds
    | .wrap =>
      match wrapLoop idx n with
      | some (k, _) => .ok (some k)
      | none => .error .hang
    | .clip => .ok (some (clipIndex idx n))

/-! ## choose -/

inductive ChooseErr where
  /-- `ValueError`, "invalid entry in choice array" -/
  | invalidEntry
  /-- The wrap loop never ends. -/
  | hang
  deriving Repr, DecidableEq

/-- The choice of `PyArray_Choose` at `item_selection.c:1176-1206` for one element, with `n` choices. -/
def choose1 (n mi : Int) (mode : ClipMode) : Except ChooseErr Int :=
  if mi < 0 ∨ mi ≥ n then
    match mode with
    | .raise => .error .invalidEntry
    | .wrap =>
      match wrapLoop mi n with
      | some (k, _) => .ok k
      | none => .error .hang
    | .clip => .ok (clipIndex mi n)
  else .ok mi

/-! ## repeat -/

inductive RepeatErr where
  /-- "operands could not be broadcast together with shape (%zd,) (%zd,)" -/
  | mismatch
  /-- "repeats may not contain negative values." -/
  | negativeCount
  /-- "negative dimensions are not allowed", from the array constructor -/
  | negativeDim
  /-- "array is too big; `arr.size * arr.dtype.itemsize` is larger than the maximum possible size.", from the array constructor -/
  | tooBig
  deriving Repr, DecidableEq

/-- The non-broadcast loop at `item_selection.c:937-945`. `total += counts[j]` has no overflow check. -/
def repeatSum : List Int → Int → Except RepeatErr Int
  | [], total => .ok total
  | c :: rest, total =>
    if c < 0 then .error .negativeCount else repeatSum rest (wrap64 (total + c))

/--
The length of the output axis of `PyArray_Repeat` at `item_selection.c:895`, for a 1-D array of length `n` and the given counts, followed by the size check of `PyArray_NewFromDescr_int` (`ctors.c:725-757`) for one dimension with item size `itemsize`. A single count broadcasts, and `total = counts[0] * n` at `item_selection.c:934` has no overflow check and no sign check.
-/
def repeatTotal (n : Int) (counts : List Int) (itemsize : Int) : Except RepeatErr Int := do
  let broadcast := counts.length = 1
  if !broadcast ∧ (counts.length : Int) ≠ n then throw RepeatErr.mismatch
  let total ← if broadcast then pure (wrap64 (counts.headD 0 * n)) else repeatSum counts 0
  if total < 0 then throw RepeatErr.negativeDim
  if total ≠ 0 ∧ (mulSizesWithOverflow itemsize total).1 then throw RepeatErr.tooBig
  return total

/-- The number of elements that `npy_fastrepeat_impl` (`item_selection.c:812-838`) copies into the output: the sum of the counts, without any wrap. -/
def repeatWrites (n : Int) (counts : List Int) : Int :=
  if counts.length = 1 then counts.headD 0 * n else counts.foldl (· + ·) 0

/-! ## diagonal -/

inductive DiagErr where
  /-- `OverflowError` from the conversion of `offset` to a C `int` -/
  | offsetOverflow
  deriving Repr, DecidableEq

/--
`PyArray_Diagonal` at `item_selection.c:2321` for a 2-D array of shape `(r, c)` with row stride `s1` and column stride `1` in elements, `axis1 = 0` and `axis2 = 1`. The result is `(size, start, step)` of the view in elements. When the size is negative it becomes zero and the data pointer is not moved, but a size of exactly zero still moves it. `offset` is a C `int`. The negation `offset = -offset` overflows for `INT_MIN`, but the build computes `dim1 -= offset` in 64 bits as if it had not, so the model uses the mathematical value.
-/
def diagonal2 (r c s1 offset : Int) : Except DiagErr (Int × Int × Int) :=
  if offset < -(2 : Int) ^ 31 ∨ offset ≥ (2 : Int) ^ 31 then .error .offsetOverflow
  else
    let (dim1, dim2, off, offStride) :=
      if offset ≥ 0 then (r, c - offset, offset, 1) else (r + offset, c, -offset, s1)
    let size := if dim2 < dim1 then dim2 else dim1
    if size < 0 then .ok (0, 0, s1 + 1) else .ok (size, off * offStride, s1 + 1)

/-! ## searchsorted -/

/-- The comparison of `side_to_cmp` in `npysort/binsearch.cpp`: `<` for side left and `<=` for side right. -/
def sideCmp (right : Bool) (a b : Int) : Bool := if right then decide (a ≤ b) else decide (a < b)

/-- The loop `while (interval_length > 1)` of `binsearch` and `argbinsearch` in `npysort/binsearch.cpp`. `get` returns the array value at a sorted position, or `none` when the sorter entry there is out of range. `fuel` bounds the recursion and is always enough because the interval halves. -/
def binLoop (get : Int → Option Int) (right : Bool) (key : Int) : Nat → Int → Int → Option Int
  | 0, _, base => some base
  | fuel + 1, il, base =>
    if il > 1 then
      let half := il / 2
      match get (base + half) with
      | none => none
      | some v => binLoop get right key fuel (il - half) (base + if sideCmp right v key then half else 0)
    else some base

/--
`binsearch` and `argbinsearch` in `npysort/binsearch.cpp` for one key. The first halving step is unrolled in the source but computes the same as one step of the loop from base 0. The last step adds one when the value at `base` compares true.
-/
def binsearch (len : Int) (get : Int → Option Int) (right : Bool) (key : Int) : Option Int :=
  if len ≤ 0 then some 0
  else
    let half := len / 2
    match get half with
    | none => none
    | some mid =>
      let base := if sideCmp right mid key then half else 0
      match binLoop get right key (len.toNat + 1) (len - half) base with
      | none => none
      | some b =>
        match get b with
        | none => none
        | some v => some (b + if sideCmp right v key then 1 else 0)

/-- The value lookup without a sorter. -/
def plainGet (arr : List Int) (i : Int) : Option Int :=
  if i < 0 then none else arr[i.toNat]?

/-- The value lookup through a sorter, with the range check `mid_idx < 0 || mid_idx >= arr_len` of `argbinsearch`. -/
def sorterGet (arr sorter : List Int) (i : Int) : Option Int :=
  match plainGet sorter i with
  | none => none
  | some s => if s < 0 ∨ s ≥ arr.length then none else plainGet arr s

inductive SearchErr where
  /-- "sorter.size must equal a.size" -/
  | sorterSize
  /-- "Sorter index out of range." -/
  | sorterRange
  deriving Repr, DecidableEq

/-- `PyArray_SearchSorted` at `item_selection.c:2141` for `int64` arrays and keys. -/
def searchsorted (arr keys : List Int) (right : Bool) (sorter : Option (List Int)) : Except SearchErr (List Int) :=
  match sorter with
  | none => .ok (keys.map fun k => (binsearch arr.length (plainGet arr) right k).getD 0)
  | some s =>
    if s.length ≠ arr.length then .error .sorterSize
    else
      let rs := keys.map (binsearch arr.length (sorterGet arr s) right)
      if rs.any (·.isNone) then .error .sorterRange else .ok (rs.map (·.getD 0))

end NumpyLean.Indexing
