import NumpyLean.Common.Intp

/-
Models of shape broadcasting, the no-copy reshape stride computation, the contiguity flags and axis normalisation at NumPy 2.5.4.

Sources, relative to `vendor/numpy/numpy/`:

- `_core/src/multiarray/iterators.c` for `PyArray_Broadcast`, which `np.broadcast` uses.
- `_core/src/multiarray/nditer_constr.c` for the shape logic of `np.nditer` with `itershape`, which `np.broadcast_to` uses.
- `lib/_stride_tricks_impl.py` for `broadcast_to` and `broadcast_shapes`.
- `_core/src/multiarray/ctors.c` for the size check and the stride fill of new arrays.
- `_core/src/multiarray/shape.c` for reshape and transpose.
- `_core/src/multiarray/flagsobject.c` for the contiguity flags.
- `_core/numeric.py` and `_core/src/multiarray/conversion_utils.c` for axis normalisation.

Every model assumes two's complement wrap where the C code multiplies `npy_intp` values without a check, which is what the arm64 and x86-64 builds do.
-/
namespace NumpyLean.Broadcast

/-- `NPY_MAXDIMS` and `NPY_MAXARGS`, both 64 in NumPy 2. -/
def maxDims : Nat := 64
def maxArgs : Nat := 64

def int32Min : Int := -2147483648
def int32Max : Int := 2147483647

/-! ## Errors -/

inductive BErr where
  /-- "shape mismatch: objects cannot be broadcast to a single shape. Mismatch is between arg i ... and arg j ..." (`iterators.c:1128`). -/
  | mismatch (i j : Nat)
  /-- "broadcast dimensions too large." (`iterators.c:1192`). -/
  | bcastTooLarge
  /-- "Need at least 0 and at most 64 array objects." (`iterators.c:1233`). -/
  | tooManyArgs
  /-- "maximum supported dimension for an ndarray is currently 64, found N" (`conversion_utils.c:179`). -/
  | maxDims
  /-- "Maximum allowed dimension exceeded", a shape entry outside `npy_intp` (`conversion_utils.c:98`). -/
  | conv
  /-- "negative dimensions are not allowed" (`ctors.c:740`), or in `broadcast_to` "all elements of broadcast shape must be non-negative" (`_stride_tricks_impl.py:453`). -/
  | negative
  /-- "array is too big; `arr.size * arr.dtype.itemsize` is larger than the maximum possible size." (`ctors.c:750`). -/
  | tooBig
  /-- "cannot broadcast a non-scalar to a scalar array" (`_stride_tricks_impl.py:451`). -/
  | scalar
  /-- "input operand has more dimensions than allowed by the axis remapping" (`nditer_constr.c:1515`). -/
  | opNdim
  /-- "operands could not be broadcast together with remapped shapes" (`nditer_constr.c:1722`). -/
  | iterBcast
  /-- RuntimeError "this function only supports up to 32 dimensions but the array has N." from `PyArray_IterNew` (`iterators.c:124-129`). -/
  | legacyDims
  /-- "iterator is too large" (`nditer_constr.c:1711`, raised later through `nditer_api.c:172` because `broadcast_to` asks for a multi index). -/
  | iterTooLarge
  deriving Repr, DecidableEq

/-! ## Size products -/

/--
`PyArray_OverflowMultiplyList` at `multiarraymodule.c:216-232`. It returns 0 at the first zero entry, so entries after a zero are never multiplied, and -1 when a product before that overflows.
-/
def overflowMultiplyList : List Int → Int → Int
  | [], prod => prod
  | d :: rest, prod =>
    if d == 0 then 0
    else
      let (overflow, p) := mulSizesWithOverflow prod d
      if overflow then -1 else overflowMultiplyList rest p

/--
The size loop of `PyArray_NewFromDescr_int` at `ctors.c:725-757`. `nbytes` starts at the item size. A zero entry is skipped and the other entries must still multiply without overflow.
-/
def ctorCheck : List Int → Int → Except BErr Unit
  | [], _ => .ok ()
  | d :: rest, nbytes =>
    if d == 0 then ctorCheck rest nbytes
    else if d < 0 then .error .negative
    else
      let (overflow, p) := mulSizesWithOverflow nbytes d
      if overflow then .error .tooBig else ctorCheck rest p

/--
`PyArray_IntpConverter` at `conversion_utils.c:115-206` for a tuple of Python ints. The length is checked first, then each entry in order.
-/
def intpConvert (dims : List Int) : Except BErr Unit :=
  if dims.length > maxDims then .error .maxDims
  else if dims.any (fun d => !(inIntp d)) then .error .conv
  else .ok ()

/-! ## PyArray_Broadcast -/

/--
The inner loop of `PyArray_Broadcast` at `iterators.c:1162-1180` for one output dimension `i`. The state is `mit->dimensions[i]` and `src_iter`. `src_iter` is a function-level variable in C, but it is only read after it was set for the same `i`, so the model starts it fresh at each `i`.
-/
def bcastDim (nd i : Nat) : List (List Int) → Nat → Int → Nat → Except BErr Int
  | [], _, dim, _ => .ok dim
  | s :: rest, j, dim, src =>
    -- iterators.c:1166, `k = i + PyArray_NDIM(it->ao) - nd`.
    if i + s.length ≥ nd then
      let tmp := s.getD (i + s.length - nd) 0
      if tmp == 1 then bcastDim nd i rest (j + 1) dim src
      else if dim == 1 then bcastDim nd i rest (j + 1) tmp j
      else if dim != tmp then .error (.mismatch src j)
      else bcastDim nd i rest (j + 1) dim src
    else bcastDim nd i rest (j + 1) dim src

/-- The outer loop of `iterators.c:1161`, over output dimensions in order from the first. -/
def bcastDims (shapes : List (List Int)) (nd : Nat) : Nat → Nat → Except BErr (List Int)
  | 0, _ => .ok []
  | fuel + 1, i =>
    if i < nd then do
      let d ← bcastDim nd i shapes 0 1 0
      let rest ← bcastDims shapes nd fuel (i + 1)
      .ok (d :: rest)
    else .ok []

def maxLen : List (List Int) → Nat
  | [] => 0
  | s :: rest => max s.length (maxLen rest)

/-- `PyArray_Broadcast` at `iterators.c:1147-1191`, the part that computes the shape. -/
def pyArrayBroadcast (shapes : List (List Int)) : Except BErr (List Int) := do
  let nd := maxLen shapes
  let dims ← bcastDims shapes nd nd 0
  if overflowMultiplyList dims 1 < 0 then .error .bcastTooLarge
  else .ok dims

/-- `NPY_MAXDIMS_LEGACY_ITERS`, the dimension limit of the old iterator. -/
def maxDimsLegacy : Nat := 32

/-- The argument loop of `multiiter_new_impl` at `iterators.c:1247-1285`. Each argument is checked in turn: the 65th argument fails the count check and an argument with more than 32 dimensions fails in `PyArray_IterNew`. -/
def multiIterArgs : List (List Int) → Nat → Except BErr Unit
  | [], _ => .ok ()
  | s :: rest, n =>
    if n < maxArgs then
      if s.length > maxDimsLegacy then .error .legacyDims else multiIterArgs rest (n + 1)
    else .error .tooManyArgs

/-- `np.broadcast(*arrays)` through `multiiter_new_impl` at `iterators.c:1240-1300`. -/
def npBroadcast (shapes : List (List Int)) : Except BErr (List Int) := do
  multiIterArgs shapes 0
  pyArrayBroadcast shapes

/-! ## New arrays and np.broadcast_to -/

/-- The C branch of `_array_fill_strides` at `ctors.c:4128-4136`, run from the last axis. The second component is the running item size. A zero dimension does not multiply it. -/
def fillStridesCAux : List Int → Int → List Int × Int
  | [], itemsize => ([], itemsize)
  | d :: rest, itemsize =>
    let (s, it) := fillStridesCAux rest itemsize
    (it :: s, if d != 0 then wrap64 (it * d) else it)

def fillStridesC (dims : List Int) (itemsize : Int) : List Int := (fillStridesCAux dims itemsize).1

/-- The Fortran branch of `_array_fill_strides` at `ctors.c:4110-4118`. -/
def fillStridesF : List Int → Int → List Int
  | [], _ => []
  | d :: rest, itemsize => itemsize :: fillStridesF rest (if d != 0 then wrap64 (itemsize * d) else itemsize)

/-- Strides of a freshly allocated C-ordered array. `ctors.c:825-831` sets every stride to 0 when the array has no bytes. -/
def freshStrides (dims : List Int) (itemsize : Int) : List Int :=
  if itemsize == 0 || dims.any (· == 0) then dims.map (fun _ => 0) else fillStridesC dims itemsize

/--
The broadcast part of `npyiter_fill_axisdata` at `nditer_constr.c:1487-1561` for one operand without `op_axes`. `bshape` starts as the requested shape, and `off` is `ndim - ondim`.
-/
def iterBroadcastOp : List Int → List Int → Nat → Nat → Except BErr (List Int)
  | bshape, [], _, _ => .ok bshape
  | bshape, o :: rest, off, idim =>
    let b := bshape.getD (idim + off) 0
    if b == 1 then iterBroadcastOp (bshape.set (idim + off) o) rest off (idim + 1)
    else if b != o && o != 1 then .error .iterBcast
    else iterBroadcastOp bshape rest off (idim + 1)

/-- The iterator size loop at `nditer_constr.c:1694-1716`. Unlike `PyArray_OverflowMultiplyList` it does not stop at a zero, but a zero keeps the product at zero. -/
def iterSizeOverflows : List Int → Int → Bool
  | [], _ => false
  | d :: rest, prod =>
    let (overflow, p) := mulSizesWithOverflow prod d
    if overflow then true else iterSizeOverflows rest p

/--
`np.broadcast_to(np.empty(opShape, dtype), shape)` through `_broadcast_to` at `_stride_tricks_impl.py:447-467`. The result is the shape and strides of the view, which `NpyIter_GetIterView` (`nditer_api.c:1174`) builds from the axis data.
-/
def broadcastTo (opShape : List Int) (itemsize : Int) (shape : List Int) : Except BErr (List Int × List Int) := do
  if shape.isEmpty && !opShape.isEmpty then throw .scalar
  if shape.any (· < 0) then throw .negative
  intpConvert shape
  let ndim := shape.length
  let ondim := opShape.length
  if ondim > ndim then throw .opNdim
  let bshape ← iterBroadcastOp shape opShape (ndim - ondim) 0
  -- nditer_constr.c:1568, an entry 1 of `itershape` must not have been expanded.
  if (shape.zip bshape).any (fun (s, b) => s == 1 && b != 1) then throw .iterBcast
  if iterSizeOverflows bshape 1 then throw .iterTooLarge
  let opStrides := freshStrides opShape itemsize
  -- nditer_constr.c:1592-1617, a broadcast or length-one axis gets stride 0.
  let strides := (List.range ndim).map fun p =>
    let b := bshape.getD p 0
    if b == 1 then 0
    else if p < ndim - ondim then 0
    else if opShape.getD (p - (ndim - ondim)) 0 == 1 then 0
    else opStrides.getD (p - (ndim - ondim)) 0
  ctorCheck bshape itemsize
  .ok (bshape, strides)

/-- `np.empty(shape, dtype=np.dtype([]))` as `broadcast_shapes` builds it at `_stride_tricks_impl.py:580`. The item size is 0, so the size loop never overflows. -/
def emptyVoid0 (shape : List Int) : Except BErr Unit := do
  intpConvert shape
  ctorCheck shape 0

/-- The chunk loop of `_broadcast_shape` at `_stride_tricks_impl.py:528-533`. `broadcast_to(0, b.shape)` uses a 0-d `int64` array, whose item size is 8. -/
def chunkLoop : Nat → List (List Int) → List Int → Except BErr (List Int)
  | 0, _, b => .ok b
  | _, [], b => .ok b
  | fuel + 1, rest, b => do
    let _ ← broadcastTo [] 8 b
    let b' ← npBroadcast (b :: rest.take 63)
    chunkLoop fuel (rest.drop 63) b'

/-- `np.broadcast_shapes(*shapes)` at `_stride_tricks_impl.py:541-581`, with every argument given as a tuple. -/
def broadcastShapes (shapes : List (List Int)) : Except BErr (List Int) := do
  let _ ← shapes.mapM emptyVoid0
  let b ← npBroadcast (shapes.take 64)
  chunkLoop (shapes.length) (shapes.drop 64) b

/-! ## Contiguity flags -/

/--
The C loop of `_UpdateContiguousFlags` at `flagsobject.c:123-138`, run on the reversed lists. It returns `none` when it meets a zero dimension, where C sets both flags and returns.
-/
def cScan : List (Int × Int) → Int → Bool → Option Bool
  | [], _, c => some c
  | (dim, st) :: rest, sd, c =>
    if dim == 0 then none
    else if dim != 1 then cScan rest (wrap64 (sd * dim)) (c && st == sd)
    else cScan rest sd c

/-- The Fortran loop at `flagsobject.c:147-158`. -/
def fScan : List (Int × Int) → Int → Bool
  | [], _ => true
  | (dim, st) :: rest, sd =>
    if dim != 1 then (if st != sd then false else fScan rest (wrap64 (sd * dim)))
    else fScan rest sd

/-- `_UpdateContiguousFlags` at `flagsobject.c:115-160`. The result is the C and the Fortran flag. -/
def contigFlags (dims strides : List Int) (itemsize : Int) : Bool × Bool :=
  match cScan (dims.zip strides).reverse itemsize true with
  | none => (true, true)
  | some c => (c, fScan (dims.zip strides) itemsize)

/-! ## No-copy reshape -/

inductive RErr where
  /-- "Unable to avoid creating a copy while reshaping." (`shape.c:298`). -/
  | copy
  /-- "cannot reshape array of size N into shape S" (`shape.c:517`). -/
  | mismatch
  /-- A state the C code cannot reach when the sizes agree and are not zero. The C code would read outside its arrays here. -/
  | unreachable
  deriving Repr, DecidableEq

/-- `newdims[i]` and `olddims[i]` with an out-of-range read made visible. -/
def at? (l : List Int) (i : Nat) : Option Int := l[i]?

/-- The inner `while (np != op)` loop at `shape.c:410-417`. Each step reads one more entry, so `fuel` equal to the total length is enough. -/
def growUntilEqual (newdims olddims : List Int) : Nat → Int → Int → Nat → Nat → Option (Nat × Nat)
  | 0, _, _, _, _ => none
  | fuel + 1, np, op, nj, oj =>
    if np == op then some (nj, oj)
    else if np < op then
      match at? newdims nj with
      | some d => growUntilEqual newdims olddims fuel (wrap64 (np * d)) op (nj + 1) oj
      | none => none
    else
      match at? olddims oj with
      | some d => growUntilEqual newdims olddims fuel np (wrap64 (op * d)) nj (oj + 1)
      | none => none

/-- The combine check at `shape.c:419-434` for axes `ok` from `oi` to `oj - 2`. -/
def canCombine (olddims oldstrides : List Int) (fOrder : Bool) (oi oj : Nat) : Bool :=
  (List.range (oj - 1 - oi)).all fun t =>
    let ok := oi + t
    if fOrder then oldstrides.getD (ok + 1) 0 == wrap64 (olddims.getD ok 0 * oldstrides.getD ok 0)
    else oldstrides.getD ok 0 == wrap64 (olddims.getD (ok + 1) 0 * oldstrides.getD (ok + 1) 0)

/-- The C-order stride block at `shape.c:443-449`: the last entry is `s` and each earlier one is the next stride times the next dimension. -/
def cBlock : List Int → Int → List Int
  | [], _ => []
  | [_], s => [s]
  | _ :: rest, s =>
    let r := cBlock rest s
    wrap64 (r.headD 0 * rest.headD 0) :: r

/-- The Fortran stride block at `shape.c:437-442`. -/
def fBlock : List Int → Int → List Int
  | [], _ => []
  | d :: rest, s => s :: fBlock rest (wrap64 (s * d))

/-- The outer `while` loop at `shape.c:406-453`. `acc` holds the new strides found so far, so `acc.length` is `ni`. -/
def nocopyLoop (newdims olddims oldstrides : List Int) (fOrder : Bool) : Nat → Nat → Nat → List Int → Except RErr (List Int)
  | 0, _, _, _ => .error .unreachable
  | fuel + 1, ni, oi, acc =>
    if ni < newdims.length && oi < olddims.length then
      match growUntilEqual newdims olddims (newdims.length + olddims.length) (newdims.getD ni 0) (olddims.getD oi 0) (ni + 1) (oi + 1) with
      | none => .error .unreachable
      | some (nj, oj) =>
        if !canCombine olddims oldstrides fOrder oi oj then .error .copy
        else
          let blk := (newdims.drop ni).take (nj - ni)
          let strides :=
            if fOrder then fBlock blk (oldstrides.getD oi 0)
            else cBlock blk (oldstrides.getD (oj - 1) 0)
          nocopyLoop newdims olddims oldstrides fOrder fuel nj oj (acc ++ strides)
    else .ok acc

/-- `_attempt_nocopy_reshape` at `shape.c:379-471`. Axes of length one are removed from the old array first (`shape.c:393-399`). -/
def attemptNocopyReshape (dims strides : List Int) (itemsize : Int) (newdims : List Int) (fOrder : Bool) : Except RErr (List Int) := do
  let kept := (dims.zip strides).filter (fun (d, _) => d != 1)
  let olddims := kept.map (·.1)
  let oldstrides := kept.map (·.2)
  let acc ← nocopyLoop newdims olddims oldstrides fOrder (newdims.length + 1) 0 0 []
  let ni := acc.length
  -- shape.c:455-468. In Fortran order with `ni == 0` the C code reads `newdims[-1]`.
  let last ← if ni ≥ 1 then .ok (acc.getD (ni - 1) 0) else if fOrder then .error .unreachable else .ok itemsize
  let last := if fOrder then wrap64 (last * newdims.getD (ni - 1) 0) else last
  .ok (acc ++ (List.range (newdims.length - ni)).map (fun _ => last))

/-- The size check of `_fix_unknown_dimension` (`shape.c:485-530`) when no entry is negative. -/
def sizesAgree (dims newdims : List Int) : Bool :=
  let (ov, s) := newdims.foldl (fun (o, p) d => let (o', q) := mulSizesWithOverflow p d; (o || o', q)) (false, 1)
  !ov && s == dims.foldl (· * ·) 1

/--
`a.reshape(newdims, order=..., copy=False)` through `_reshape_with_copy_arg` at `shape.c:225-334` for an array with shape `dims` and strides `strides`, and every entry of `newdims` non-negative. The result is the strides of the view.
-/
def reshapeNoCopy (dims strides : List Int) (itemsize : Int) (newdims : List Int) (fOrder : Bool) : Except RErr (List Int) :=
  -- shape.c:246-258, the same shape gives a plain view.
  if newdims == dims then .ok strides
  else if !sizesAgree dims newdims then .error .mismatch
  else
    let (c, f) := contigFlags dims strides itemsize
    if (!fOrder && !c) || (fOrder && !f) then
      attemptNocopyReshape dims strides itemsize newdims fOrder
    else
      -- shape.c:314-331, the strides are filled in the requested order. For one dimension or none both fills agree.
      .ok (if fOrder && newdims.length > 1 then fillStridesF newdims itemsize else fillStridesC newdims itemsize)

/-! ## Axis normalisation -/

inductive AErr where
  /-- An axis outside C `int`: "Python int too large to convert to C int" or "integer won't fit into a C int". -/
  | cint
  /-- `AxisError`, "axis a is out of bounds for array of dimension n" (`common.h:204`). -/
  | axis
  /-- "repeated axis" and "duplicate value in 'axis'" (`numeric.py:1478`, `conversion_utils.c:397`, `shape.c:709`). -/
  | repeated
  /-- "`source` and `destination` arguments must have the same number of elements" (`numeric.py:1547`). -/
  | lengths
  /-- "axes don't match array" (`shape.c:695`). -/
  | axesMismatch
  /-- "Maximum allowed dimension exceeded", an axis outside `npy_intp` in `transpose`. -/
  | conv
  /-- "cannot select an axis to squeeze out which has size not equal to one" (`shape.c:608`). -/
  | notOne
  deriving Repr, DecidableEq

def inInt32 (x : Int) : Bool := int32Min ≤ x && x ≤ int32Max

/-- `check_and_adjust_axis_msg` at `common.h:201-222`. -/
def checkAndAdjustAxis (axis ndim : Int) : Except AErr Int :=
  if axis < -ndim || axis ≥ ndim then .error .axis
  else if axis < 0 then .ok (axis + ndim) else .ok axis

/-- `normalize_axis_index` at `multiarraymodule.c:4333`, whose argument parser converts the axis to C `int`. -/
def normalizeAxisIndex (axis ndim : Int) : Except AErr Int :=
  if !inInt32 axis then .error .cint else checkAndAdjustAxis axis ndim

/-- Whether a list repeats an entry, which is `len(set(axis)) != len(axis)` in Python. -/
def hasDup : List Int → Bool
  | [] => false
  | x :: rest => rest.contains x || hasDup rest

/-- `normalize_axis_tuple` at `numeric.py:1428-1482` with `allow_duplicate=False`. -/
def normalizeAxisTuple (axes : List Int) (ndim : Int) : Except AErr (List Int) := do
  let r ← axes.mapM (normalizeAxisIndex · ndim)
  if hasDup r then throw .repeated
  .ok r

/-- Python `list.insert(i, x)` for `i ≥ 0`, which appends when `i` is past the end. -/
def pyInsert : List Int → Nat → Int → List Int
  | l, 0, x => x :: l
  | [], _, x => [x]
  | y :: rest, n + 1, x => y :: pyInsert rest n x

/-- Insert into a list of pairs kept sorted as Python sorts tuples. -/
def insertPair (p : Int × Int) : List (Int × Int) → List (Int × Int)
  | [] => [p]
  | q :: rest => if p.1 < q.1 || (p.1 == q.1 && p.2 ≤ q.2) then p :: q :: rest else q :: insertPair p rest

def sortPairs (l : List (Int × Int)) : List (Int × Int) := l.foldr insertPair []

/-- `np.moveaxis` at `numeric.py:1536-1556`. The result is the permutation passed to `transpose`. -/
def moveaxis (ndim : Nat) (source destination : List Int) : Except AErr (List Int) := do
  let src ← normalizeAxisTuple source ndim
  let dst ← normalizeAxisTuple destination ndim
  if src.length != dst.length then throw .lengths
  let order := ((List.range ndim).map Int.ofNat).filter (fun n => !(src.contains n))
  .ok ((sortPairs (dst.zip src)).foldl (fun o (d, s) => pyInsert o d.toNat s) order)

/-- The permutation loop of `PyArray_Transpose` at `shape.c:699-714`. `int axis = axes[i]` converts `npy_intp` to `int`, which keeps the low 32 bits. -/
def transposeLoop (ndim : Int) : List Int → List Int → Except AErr (List Int)
  | [], acc => .ok acc
  | a :: rest, acc => do
    let axis ← checkAndAdjustAxis (wrapSigned 32 a) ndim
    if acc.contains axis then throw .repeated
    transposeLoop ndim rest (acc ++ [axis])

/-- `np.transpose(a, axes)` through `PyArray_Transpose` at `shape.c:677-715`. The result is the permutation. -/
def transpose (ndim : Nat) (axes : List Int) : Except AErr (List Int) :=
  if axes.length > maxDims then .error .conv
  else if axes.any (fun a => !(inIntp a)) then .error .conv
  else if axes.length != ndim then .error .axesMismatch
  else transposeLoop ndim axes []

/-- The tuple branch of `PyArray_ConvertMultiAxis` at `conversion_utils.c:376-404`. The result is the list of flagged axes. -/
def multiAxisTuple (ndim : Int) : List Int → List Int → Except AErr (List Int)
  | [], acc => .ok acc
  | a :: rest, acc => do
    if !inInt32 a then throw .cint
    let axis ← checkAndAdjustAxis a ndim
    if acc.contains axis then throw .repeated
    multiAxisTuple ndim rest (acc ++ [axis])

/-- The integer branch at `conversion_utils.c:406-432`, which lets 0 and -1 through for a 0-d array. -/
def multiAxisInt (ndim : Int) (a : Int) : Except AErr (List Int) :=
  if !inInt32 a then .error .cint
  else if ndim == 0 && (a == 0 || a == -1) then .ok []
  else do
    let axis ← checkAndAdjustAxis a ndim
    .ok [axis]

/-- `PyArray_SqueezeSelected` at `shape.c:591-627`. The result is the new shape. -/
def squeezeSelected (shape : List Int) (flagged : List Int) : Except AErr (List Int) :=
  let idx := (List.range shape.length).map Int.ofNat
  if (idx.zip shape).any (fun (i, d) => flagged.contains i && d != 1) then .error .notOne
  else .ok ((idx.zip shape).filter (fun (i, _) => !(flagged.contains i))).unzip.2

/-- `a.squeeze(axis=...)` through `array_squeeze` at `methods.c:219-242`, with `isTuple` saying whether the axis argument is a tuple. -/
def squeeze (shape : List Int) (isTuple : Bool) (axes : List Int) : Except AErr (List Int) := do
  let ndim : Int := shape.length
  let flagged ← if isTuple then multiAxisTuple ndim axes [] else multiAxisInt ndim (axes.headD 0)
  squeezeSelected shape flagged

end NumpyLean.Broadcast
