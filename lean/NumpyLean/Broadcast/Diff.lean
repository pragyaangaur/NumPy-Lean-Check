import NumpyLean.Broadcast.Model
import NumpyLean.Common.Wire

namespace NumpyLean.Broadcast
open NumpyLean.Wire

def bErrStr : BErr → String
  | .mismatch i j => s!"ERR mismatch {i} {j}"
  | .bcastTooLarge => "ERR bcastlarge"
  | .tooManyArgs => "ERR toomany"
  | .maxDims => "ERR maxdims"
  | .conv => "ERR conv"
  | .negative => "ERR negative"
  | .tooBig => "ERR toobig"
  | .scalar => "ERR scalar"
  | .opNdim => "ERR opndim"
  | .iterBcast => "ERR iterbcast"
  | .iterTooLarge => "ERR iterlarge"

def rErrStr : RErr → String
  | .copy => "ERR copy"
  | .mismatch => "ERR mismatch"
  | .unreachable => "UNREACHABLE"

def aErrStr : AErr → String
  | .cint => "ERR cint"
  | .axis => "ERR axis"
  | .repeated => "ERR repeated"
  | .lengths => "ERR lengths"
  | .axesMismatch => "ERR axesmismatch"
  | .conv => "ERR conv"
  | .notOne => "ERR notone"

def fmtA : Except AErr (List Int) → String
  | .ok r => s!"OK {fmtInts r}"
  | .error e => aErrStr e

/-- `bshapes <shape> <shape> ...` runs `np.broadcast_shapes` on any number of tuples. -/
def diffBShapes : Handler
  | args =>
    match broadcastShapes (args.map parseInts) with
    | .ok r => s!"OK {fmtInts r}"
    | .error e => bErrStr e

/-- `bto <op shape> <itemsize> <shape>` runs `np.broadcast_to(np.empty(op shape), shape)` and prints the shape and strides of the view. -/
def diffBTo : Handler
  | [op, itemsize, shape] =>
    match broadcastTo (parseInts op) (parseInt itemsize) (parseInts shape) with
    | .ok (s, st) => s!"OK {fmtInts s} {fmtInts st}"
    | .error e => bErrStr e
  | _ => "BADARGS"

/-- `flags <dims> <strides> <itemsize>` prints the C and Fortran contiguity flags. -/
def diffFlags : Handler
  | [dims, strides, itemsize] =>
    let (c, f) := contigFlags (parseInts dims) (parseInts strides) (parseInt itemsize)
    s!"{fmtBool c} {fmtBool f}"
  | _ => "BADARGS"

/-- `reshape <dims> <strides> <itemsize> <newdims> <C|F>` prints the strides of `reshape(..., copy=False)`. -/
def diffReshape : Handler
  | [dims, strides, itemsize, newdims, order] =>
    match reshapeNoCopy (parseInts dims) (parseInts strides) (parseInt itemsize) (parseInts newdims) (order == "F") with
    | .ok r => s!"OK {fmtInts r}"
    | .error e => rErrStr e
  | _ => "BADARGS"

/-- `moveaxis <ndim> <source> <destination>` prints the permutation. -/
def diffMoveaxis : Handler
  | [ndim, src, dst] => fmtA (moveaxis (parseInt ndim).toNat (parseInts src) (parseInts dst))
  | _ => "BADARGS"

/-- `transpose <ndim> <axes>` prints the permutation. -/
def diffTranspose : Handler
  | [ndim, axes] => fmtA (transpose (parseInt ndim).toNat (parseInts axes))
  | _ => "BADARGS"

/-- `squeeze <shape> <t|i> <axes>` prints the new shape. With `i` the axis is the single integer in `axes`. -/
def diffSqueeze : Handler
  | [shape, kind, axes] => fmtA (squeeze (parseInts shape) (kind == "t") (parseInts axes))
  | _ => "BADARGS"

def handlers : List (String × Handler) :=
  [("bshapes", diffBShapes), ("bto", diffBTo), ("flags", diffFlags), ("reshape", diffReshape),
   ("moveaxis", diffMoveaxis), ("transpose", diffTranspose), ("squeeze", diffSqueeze)]

end NumpyLean.Broadcast
