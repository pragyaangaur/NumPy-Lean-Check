import NumpyLean.Indexing.Model
import NumpyLean.Common.Wire

namespace NumpyLean.Indexing
open NumpyLean.Wire

/-- `N` stands for `None` and anything else is an integer. -/
def parseOptInt (s : String) : Option Int := if s == "N" then none else some (parseInt s)

/-- `r`, `w` and `c` stand for the clip modes raise, wrap and clip. -/
def parseMode (s : String) : ClipMode :=
  if s == "w" then .wrap else if s == "c" then .clip else .raise

def parseModes (s : String) : List ClipMode :=
  if s == "_" then [] else (s.splitOn ",").map parseMode

/-- `int_index <n> <i>` prints `OK <k>`, `ERR bounds`, `ERR overflow` or `ERR type`. -/
def diffIntIndex : Handler
  | [n, i] =>
    match pyIntIndex (parseInt n) (parseInt i) with
    | .ok k => s!"OK {k}"
    | .error .outOfBounds => "ERR bounds"
    | .error .overflow => "ERR overflow"
    | .error .notAnIndex => "ERR type"
  | _ => "BADARGS"

/-- `slice <n> <start> <stop> <step>` prints `OK <start> <step> <length>` or `ERR step0`. -/
def diffSlice : Handler
  | [n, a, b, s] =>
    match sliceView (parseInt n) (parseOptInt a) (parseOptInt b) (parseOptInt s) with
    | .ok (st, sp, len) => s!"OK {st} {sp} {len}"
    | .error .zeroStep => "ERR step0"
  | _ => "BADARGS"

/-- `ravel <coords> <dims> <modes> <C|F>` prints `OK <index>`, `ERR toolarge`, `ERR zero` or `ERR invalid`. -/
def diffRavel : Handler
  | [coords, dims, modes, order] =>
    match ravelMultiIndex (parseInts coords) (parseInts dims) (parseModes modes) (order == "F") with
    | .ok v => s!"OK {v}"
    | .error .dimsTooLarge => "ERR toolarge"
    | .error .zeroDim => "ERR zero"
    | .error .invalidEntry => "ERR invalid"
  | _ => "BADARGS"

/-- `unravel <index> <dims> <C|F>` prints `OK <coords>`, `ERR toolarge` or `ERR bounds <index> <size>`. -/
def diffUnravel : Handler
  | [v, dims, order] =>
    match unravelIndex (parseInt v) (parseInts dims) (order == "F") with
    | .ok cs => s!"OK {fmtInts cs}"
    | .error .tooLarge => "ERR toolarge"
    | .error (.outOfBounds a b) => s!"ERR bounds {a} {b}"
  | _ => "BADARGS"

/-- `take <n> <index> <mode>` prints `OK <k>`, `ERR bounds`, `ERR empty` or `HANG`. -/
def diffTake : Handler
  | [n, i, m] =>
    match take1 (parseInt n) (parseInt i) (parseMode m) with
    | .ok k => s!"OK {k}"
    | .error .outOfBounds => "ERR bounds"
    | .error .emptyAxis => "ERR empty"
    | .error .hang => "HANG"
  | _ => "BADARGS"

/-- `put <n> <index> <nvalues> <mode>` prints `OK <k>`, `OK none`, `ERR empty`, `ERR bounds` or `HANG`. -/
def diffPut : Handler
  | [n, i, nv, m] =>
    match put1 (parseInt n) (parseInt i) (parseInt nv) (parseMode m) with
    | .ok (some k) => s!"OK {k}"
    | .ok none => "OK none"
    | .error .emptyArray => "ERR empty"
    | .error .outOfBounds => "ERR bounds"
    | .error .hang => "HANG"
  | _ => "BADARGS"

/-- `choose <n> <index> <mode>` prints `OK <k>`, `ERR invalid` or `HANG`. -/
def diffChoose : Handler
  | [n, i, m] =>
    match choose1 (parseInt n) (parseInt i) (parseMode m) with
    | .ok k => s!"OK {k}"
    | .error .invalidEntry => "ERR invalid"
    | .error .hang => "HANG"
  | _ => "BADARGS"

/-- `repeat <n> <counts> <itemsize>` prints `OK <length>` or `ERR mismatch`, `ERR negcount`, `ERR negdim` or `ERR toobig`. -/
def diffRepeat : Handler
  | [n, counts, itemsize] =>
    match repeatTotal (parseInt n) (parseInts counts) (parseInt itemsize) with
    | .ok t => s!"OK {t}"
    | .error .mismatch => "ERR mismatch"
    | .error .negativeCount => "ERR negcount"
    | .error .negativeDim => "ERR negdim"
    | .error .tooBig => "ERR toobig"
  | _ => "BADARGS"

/-- `diag <rows> <cols> <offset>` prints `OK <size> <start> <step>` or `ERR overflow`. -/
def diffDiag : Handler
  | [r, c, k] =>
    match diagonal2 (parseInt r) (parseInt c) (parseInt k) with
    | .ok (size, start, step) => s!"OK {size} {start} {step}"
    | .error .offsetOverflow => "ERR overflow"
  | _ => "BADARGS"

/-- `searchsorted <arr> <keys> <L|R> <sorter|N>` prints `OK <indices>`, `ERR size` or `ERR range`. -/
def diffSearchsorted : Handler
  | [arr, keys, side, sorter] =>
    let s := if sorter == "N" then none else some (parseInts sorter)
    match searchsorted (parseInts arr) (parseInts keys) (side == "R") s with
    | .ok r => s!"OK {fmtInts r}"
    | .error .sorterSize => "ERR size"
    | .error .sorterRange => "ERR range"
  | _ => "BADARGS"

def handlers : List (String × Handler) :=
  [("int_index", diffIntIndex), ("slice", diffSlice), ("ravel", diffRavel), ("unravel", diffUnravel),
   ("take", diffTake), ("put", diffPut), ("choose", diffChoose), ("repeat", diffRepeat),
   ("diag", diffDiag), ("searchsorted", diffSearchsorted)]

end NumpyLean.Indexing
