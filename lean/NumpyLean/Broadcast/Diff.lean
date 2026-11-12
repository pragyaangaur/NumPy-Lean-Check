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
  | .legacyDims => "ERR legacydims"

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

def sErrStr : SplitErr → String
  | .index => "ERR index"
  | .sections => "ERR sections"
  | .notEqual => "ERR notequal"
  | .zeroDiv => "ERR zerodiv"

def iErrStr : IErr → String
  | .axis => "ERR axis"
  | .index => "ERR index"
  | .value => "ERR value"
  | .attr => "ERR attr"

def pErrStr : PErr → String
  | .type => "ERR type"
  | .negative => "ERR negative"
  | .broadcast => "ERR broadcast"
  | .conv => "ERR conv"
  | .tooBig => "ERR toobig"
  | .negDim => "ERR negdim"
  | .assign => "ERR assign"

/-- A section argument is `c:<n>` for an integer or `l:<ints>` for a list of indices. -/
def parseSections (s : String) : Sections :=
  match s.splitOn ":" with
  | ["c", n] => .count (parseInt n)
  | ["l", l] => .idx (parseInts l)
  | _ => .count 0

def fmtShapes (l : List (List Int)) : String := ";".intercalate (l.map fmtInts)

def diffSplitWith (f : List Int → Int → Sections → Except SplitErr (List (List Int))) : Handler
  | [shape, axis, secs] =>
    match f (parseInts shape) (parseInt axis) (parseSections secs) with
    | .ok r => s!"OK {fmtShapes r}"
    | .error e => sErrStr e
  | _ => "BADARGS"

/-- `asplit <shape> <axis> <sections>` prints the shape of every piece of `np.array_split`. -/
def diffASplit : Handler := diffSplitWith arraySplit

/-- `split <shape> <axis> <sections>` prints the shape of every piece of `np.split`. -/
def diffNpSplit : Handler := diffSplitWith npSplit

def parseOptInt (s : String) : Option Int := if s == "n" then none else some (parseInt s)

def parseBits (s : String) : List Bool := if s == "_" then [] else s.toList.map (· == '1')

/-- An `obj` argument is `i:<n>`, `s:<start>:<stop>:<step>` with `n` for `None`, `l:<ints>`, `m:<bits>` for a boolean array or `q:<bits>` for a Python list of booleans. -/
def parseObj (s : String) : Obj :=
  match s.splitOn ":" with
  | ["i", n] => .int (parseInt n)
  | ["s", a, b, c] => .slice (parseOptInt a) (parseOptInt b) (parseOptInt c)
  | ["l", l] => .list (parseInts l)
  | ["m", b] => .mask (parseBits b)
  | ["q", b] => .boolList (parseBits b)
  | _ => .list []

/-- The array of `np.arange(size)` with shape `[]` or `[N]`, after the axis handling of `delete` and `insert`. An axis of `none` ravels a 0-d array to one element. -/
def prepArray (shape : List Int) (axis : String) : Except IErr (List Int) :=
  let size : Int := shape.foldl (· * ·) 1
  let content := (List.range size.toNat).map Int.ofNat
  if axis == "none" then .ok content
  else
    let a := parseInt axis
    let nd : Int := shape.length
    if a < -nd || a ≥ nd then .error .axis else .ok content

/-- `delete <shape> <axis> <obj>` prints the elements left after `np.delete(np.arange(n), obj, axis)`. -/
def diffDelete : Handler
  | [shape, axis, obj] =>
    match prepArray (parseInts shape) axis with
    | .error e => iErrStr e
    | .ok arr =>
      match deleteObj arr (parseObj obj) with
      | .ok r => s!"OK {fmtInts r}"
      | .error e => iErrStr e
  | _ => "BADARGS"

/-- `insert <shape> <axis> <obj> <values>` prints `np.insert(np.arange(n), obj, values, axis)`. -/
def diffInsert : Handler
  | [shape, axis, obj, values] =>
    match prepArray (parseInts shape) axis with
    | .error e => iErrStr e
    | .ok arr =>
      match insertObj arr (parseObj obj) (parseInts values) with
      | .ok r => s!"OK {fmtInts r}"
      | .error e => iErrStr e
  | _ => "BADARGS"

/-- `pad <shape> <width shape> <width data>` prints the shape of `np.pad(np.zeros(shape), pad_width)` in constant mode. -/
def diffPad : Handler
  | [shape, ps, d] =>
    match padShape (parseInts shape) (parseInts ps) (parseInts d) with
    | .ok r => s!"OK {fmtInts r}"
    | .error e => pErrStr e
  | _ => "BADARGS"

def handlers : List (String × Handler) :=
  [("bshapes", diffBShapes), ("bto", diffBTo), ("flags", diffFlags), ("reshape", diffReshape),
   ("moveaxis", diffMoveaxis), ("transpose", diffTranspose), ("squeeze", diffSqueeze),
   ("asplit", diffASplit), ("split", diffNpSplit), ("delete", diffDelete), ("insert", diffInsert),
   ("pad", diffPad)]

end NumpyLean.Broadcast
