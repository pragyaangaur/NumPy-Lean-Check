import NumpyLean.Common.Intp

/-
Models of `numpy/_core/src/multiarray/shape.c` at NumPy 2.5.4.
-/
namespace NumpyLean.Shape

inductive ReshapeErr where
  /-- "can only specify one unknown dimension" -/
  | multipleUnknown
  /-- "cannot reshape array of size N into shape S" -/
  | sizeMismatch
  deriving Repr, DecidableEq

/--
The loop at `shape.c:498-514`. The state is `s_known` and `i_unknown`, with `none` standing for the C value `-1`.
-/
def scanDims : List Int → Nat → Int → Option Nat → Except ReshapeErr (Int × Option Nat)
  | [], _, sKnown, iUnknown => .ok (sKnown, iUnknown)
  | d :: rest, i, sKnown, iUnknown =>
    -- shape.c:499 tests `dimensions[i] < 0`, so every negative entry counts as the unknown one.
    if d < 0 then
      match iUnknown with
      | none => scanDims rest (i + 1) sKnown (some i)
      | some _ => .error .multipleUnknown
    else
      let (overflow, prod) := mulSizesWithOverflow sKnown d
      if overflow then .error .sizeMismatch
      else scanDims rest (i + 1) prod iUnknown

/--
`_fix_unknown_dimension` at `shape.c:485-530`. `sOriginal` is `PyArray_SIZE(arr)`. On success the result is the shape with the unknown entry filled in.
-/
def fixUnknownDimension (dims : List Int) (sOriginal : Int) : Except ReshapeErr (List Int) := do
  let (sKnown, iUnknown) ← scanDims dims 0 1 none
  match iUnknown with
  | some i =>
    -- shape.c:517. C `%` and `/` truncate, and both operands are non-negative here.
    if sKnown == 0 || Int.tmod sOriginal sKnown != 0 then .error .sizeMismatch
    else .ok (dims.set i (Int.tdiv sOriginal sKnown))
  | none =>
    if sOriginal != sKnown then .error .sizeMismatch else .ok dims

/--
The size loop of `PyArray_NewFromDescr_int` at `ctors.c:725-757`. `nbytes` starts at the item size. A zero entry is skipped, so the other entries must still multiply without overflow. The result is `none` for "negative dimensions are not allowed", and otherwise says whether the size fits.
-/
def newArraySizeFits : List Int → Int → Option Bool
  | [], _ => some true
  | d :: rest, nbytes =>
    if d == 0 then newArraySizeFits rest nbytes
    else if d < 0 then none
    else
      let (overflow, prod) := mulSizesWithOverflow nbytes d
      if overflow then some false else newArraySizeFits rest prod

end NumpyLean.Shape
