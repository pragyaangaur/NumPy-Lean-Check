import NumpyLean.LibInt.Model
import NumpyLean.Common.Wire

namespace NumpyLean.LibInt
open NumpyLean.Wire

/-- `N` stands for `None` and anything else is an integer. -/
def parseOpt (s : String) : Option Int := if s == "N" then none else some (parseInt s)

/-- The dtype codes of the `arange` test: `b`, `i8` to `u64`, `f8` and `O`. `N` is no dtype. -/
def parseADType (s : String) : Option ADType :=
  match s with
  | "b" => some .bool
  | "i8" => some (.int 8 true) | "u8" => some (.int 8 false)
  | "i16" => some (.int 16 true) | "u16" => some (.int 16 false)
  | "i32" => some (.int 32 true) | "u32" => some (.int 32 false)
  | "i64" => some (.int 64 true) | "u64" => some (.int 64 false)
  | "f8" => some .float64
  | "O" => some .object
  | _ => none

def fmtADType : ADType → String
  | .bool => "b"
  | .int bits true => s!"i{bits}"
  | .int bits false => s!"u{bits}"
  | .float64 => "f8"
  | .object => "O"

/-- `arange <start> <stop> <step|N> <dtype|N>` prints `OK <dtype> <length> <values>`, with the values listed only for lengths up to 64 and `-` otherwise, or `ERR zerodiv`, `ERR maxsize`, `ERR toobig`, `ERR setitem` or `ERR boolfill`. -/
def diffArange : Handler
  | [a, b, s, d] =>
    match arangeObj (parseInt a) (parseInt b) (parseOpt s) (parseADType d) with
    | .ok o =>
      let vals := if o.length ≤ 64 then fmtInts o.values else "-"
      s!"OK {fmtADType o.dtype} {o.length} {vals}"
    | .error .zeroDivision => "ERR zerodiv"
    | .error .maxSize => "ERR maxsize"
    | .error .tooBig => "ERR toobig"
    | .error .setitem => "ERR setitem"
    | .error .boolFill => "ERR boolfill"
  | _ => "BADARGS"

/-- `binrepr <num> <width|N>` prints `OK '<string>'` or `ERR insufficient`. -/
def diffBinaryRepr : Handler
  | [n, w] =>
    match binaryRepr (parseInt n) (parseOpt w) with
    | .ok s => s!"OK '{s}'"
    | .error _ => "ERR insufficient"
  | _ => "BADARGS"

/-- `baserepr <num> <base> <padding>` prints `OK '<string>'`, `ERR big` or `ERR small`. -/
def diffBaseRepr : Handler
  | [n, b, p] =>
    match baseRepr (parseInt n) (parseInt b) (parseInt p) with
    | .ok s => s!"OK '{s}'"
    | .error .baseTooLarge => "ERR big"
    | .error .baseTooSmall => "ERR small"
    | .error _ => "ERR other"
  | _ => "BADARGS"

/-- Uninitialised output data is printed as `?`. -/
def fmtBits : Except BitsErr (List Int × Option (List Int)) → String
  | .ok (shape, some data) => s!"OK {fmtInts shape} {fmtInts data}"
  | .ok (shape, none) => s!"OK {fmtInts shape} ?"
  | .error .dtype => "ERR type"
  | .error .axis => "ERR axis"
  | .error .count => "ERR count"
  | .error .negDim => "ERR negdim"

/-- `pack <shape> <data> <int|float> <axis|N> <big|little>` prints `OK <shape> <data>` or an error. A shape of `S` stands for a 0-d array. -/
def diffPack : Handler
  | [shape, data, kind, axis, order] =>
    let shp := if shape == "S" then [] else parseInts shape
    fmtBits ((packbits shp (parseInts data) (kind == "int") (parseOpt axis) (order == "big")).map fun (sh, d) => (sh, some d))
  | _ => "BADARGS"

/-- `unpack <shape> <data> <u8|other> <axis|N> <count|N> <b|l>` prints `OK <shape> <data>`, with `?` for uninitialised data, or an error. -/
def diffUnpack : Handler
  | [shape, data, kind, axis, count, order] =>
    let shp := if shape == "S" then [] else parseInts shape
    fmtBits (unpackbits shp (parseInts data) (kind == "u8") (parseOpt axis) (parseOpt count) (order == "b"))
  | _ => "BADARGS"

def parseIDType (s : String) : IDType :=
  match s with
  | "i8" => .i8 | "u8" => .u8 | "u64" => .u64 | _ => .i64

def parseKind (s : String) : IsinKind :=
  match s with
  | "sort" => .sort | "table" => .table | _ => .auto

/-- `isin <a1> <d1> <a2> <d2> <kind> <invert>` prints `OK <flags>` with flags as 0 and 1, or `ERR table`. -/
def diffIsin : Handler
  | [a1, d1, a2, d2, k, inv] =>
    match isin (parseInts a1) (parseInts a2) (parseIDType d1) (parseIDType d2) (parseKind k) (inv == "1") with
    | .ok r => s!"OK {fmtInts (r.map fun b => if b then 1 else 0)}"
    | .error .tableRange => "ERR table"
  | _ => "BADARGS"

/-- `digitize <x> <bins> <right>` prints `OK <indices>` or `ERR mono`. -/
def diffDigitize : Handler
  | [x, bins, right] =>
    match digitize (parseInts x) (parseInts bins) (right == "1") with
    | .ok r => s!"OK {fmtInts r}"
    | .error .notMonotonic => "ERR mono"
  | _ => "BADARGS"

/-- `bincount <list> <minlength>` prints `OK <length> <counts>` with the counts listed only for lengths up to 64, or an error. -/
def diffBincount : Handler
  | [l, m] =>
    match bincount (parseInts l) (parseInt m) 64 with
    | .ok (n, cs) => s!"OK {n} {if n ≤ 64 then fmtInts cs else "-"}"
    | .error .negMinlength => "ERR minlength"
    | .error .negElement => "ERR negative"
    | .error .negDim => "ERR negdim"
    | .error .tooBig => "ERR toobig"
  | _ => "BADARGS"

/-- `unique <data>` prints `OK <values> <first indices> <inverse> <counts>` for the integer array `data`. -/
def diffUnique : Handler
  | [d] =>
    let r := unique1d (parseInts d)
    s!"OK {fmtInts r.values} {fmtInts (r.index.map Int.ofNat)} {fmtInts (r.inverse.map Int.ofNat)} {fmtInts (r.counts.map Int.ofNat)}"
  | _ => "BADARGS"

/-- `filldiag <shape> <wrap>` prints `OK <flat indices>` or an error. The shape of a 1-d or 0-d array is `_` for 0-d. -/
def diffFillDiag : Handler
  | [shape, wrap] =>
    match fillDiagonal ((parseInts shape).map Int.toNat) (wrap == "1") with
    | .ok l => s!"OK {fmtInts (l.map Int.ofNat)}"
    | .error .tooFewDims => "ERR ndim"
    | .error .unequalDims => "ERR dims"
  | _ => "BADARGS"

/-- An exact text form of a double: `0`, or the sign followed by `m@e` for `m * 2 ^ e` with `m` the 53-bit integer mantissa from `frexp`. -/
def fmtDouble (f : Float) : String :=
  if f == 0 then "0"
  else
    let (m, e) := (Float.abs f).frExp
    let mi := (m * 9007199254740992.0).toUInt64
    s!"{if f < 0 then "-" else ""}{mi}@{e - 53}"

def histErrName : HistErr → String
  | .bins => "bins" | .range => "range" | .tooMany => "toomany"
  | .overflow => "overflow" | .index => "index" | .negIndex => "negindex"

/-- `hist <data> <bins> <lo|N> <hi|N>` prints `OK <edges> <counts>`, `OK <edges> ERR <name>` when only `histogram` fails after `histogram_bin_edges` has succeeded, or `ERR <name>`. The edges are in the `fmtDouble` form. -/
def diffHist : Handler
  | [d, b, lo, hi] =>
    let data := parseInts d
    let rng : Option (Int × Int) := if lo == "N" then none else some (parseInt lo, parseInt hi)
    match histEdges data (parseInt b) rng with
    | .error e => s!"ERR {histErrName e}"
    | .ok (f, l, edges) =>
      let es := ",".intercalate (edges.map fmtDouble)
      match histCounts data rng (parseInt b).toNat f l edges with
      | .ok cs => s!"OK {es} {fmtInts cs}"
      | .error e => s!"OK {es} ERR {histErrName e}"
  | _ => "BADARGS"

def handlers : List (String × Handler) :=
  [("arange", diffArange), ("binrepr", diffBinaryRepr), ("baserepr", diffBaseRepr),
   ("pack", diffPack), ("unpack", diffUnpack), ("isin", diffIsin),
   ("digitize", diffDigitize), ("bincount", diffBincount),
   ("unique", diffUnique), ("filldiag", diffFillDiag), ("hist", diffHist)]

end NumpyLean.LibInt
