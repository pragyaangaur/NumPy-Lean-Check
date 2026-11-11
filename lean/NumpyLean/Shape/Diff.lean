import NumpyLean.Shape.Model
import NumpyLean.Common.Wire

namespace NumpyLean.Shape
open NumpyLean.Wire

/--
`reshape_fix <dims> <size> <itemsize>` prints `OK <shape>`, `ERR multiple`, `ERR mismatch` or `ERR toobig`. The last one comes from the array constructor that `reshape` calls after the shape is fixed.
-/
def diffReshapeFix : Handler
  | [dims, size, itemsize] =>
    match fixUnknownDimension (parseInts dims) (parseInt size) with
    | .ok r => if newArraySizeFits r (parseInt itemsize) == some true then s!"OK {fmtInts r}" else "ERR toobig"
    | .error .multipleUnknown => "ERR multiple"
    | .error .sizeMismatch => "ERR mismatch"
  | _ => "BADARGS"

def handlers : List (String × Handler) := [("reshape_fix", diffReshapeFix)]

end NumpyLean.Shape
