import NumpyLean.IntArith.Model
import NumpyLean.Common.Wire

/-
Handlers for the integer arithmetic models.

Every handler takes the dtype as `i8`, `i16`, `i32`, `i64`, `u8`, `u16`, `u32` or `u64` and a path. The path `scalar` is the Python operator on two NumPy scalars, `array` is the ufunc on two arrays of the same length, and `bcast` is the ufunc on an array and a zero-dimensional array, which gives the second operand stride 0. Flags are printed as `_` or a comma separated list of `divbyzero` and `overflow`.
-/
namespace NumpyLean.IntArith
open NumpyLean.Wire

def parseTy : String → Option IntTy
  | "i8" => some .i8
  | "i16" => some .i16
  | "i32" => some .i32
  | "i64" => some .i64
  | "u8" => some .u8
  | "u16" => some .u16
  | "u32" => some .u32
  | "u64" => some .u64
  | _ => none

def fmtFlags (f : Flags) : String :=
  let l := (if f.divbyzero then ["divbyzero"] else []) ++ (if f.overflow then ["overflow"] else [])
  if l.isEmpty then "_" else ",".intercalate l

/-- Pair the two operand lists according to the path. -/
def operands (path : String) (xs ys : List Int) : List (Int × Int) :=
  if path == "bcast" then xs.map fun x => (x, ys.headD 0) else xs.zip ys

def foldFlags (l : List Flags) : Flags := l.foldl Flags.union .clear

/-- `div <op> <ty> <path> <xs> <ys>` with `op` one of `floor_divide`, `remainder`, `divmod`. It prints `OK <values> <flags>`, or `OK <quotients> <remainders> <flags>` for divmod. -/
def diffDiv : Handler
  | [op, ty, path, xs, ys] =>
    match parseTy ty with
    | none => "BADTYPE"
    | some t =>
      let ps := operands path (parseInts xs) (parseInts ys)
      let sc := path == "scalar"
      match op with
      | "floor_divide" =>
        let rs := ps.map fun (a, b) => if sc then floorDivScalar t a b else floorDivArray t a b
        s!"OK {fmtInts (rs.map (·.1))} {fmtFlags (foldFlags (rs.map (·.2)))}"
      | "remainder" =>
        let rs := ps.map fun (a, b) => if sc then remainderScalar t a b else remainderArray t a b
        s!"OK {fmtInts (rs.map (·.1))} {fmtFlags (foldFlags (rs.map (·.2)))}"
      | "divmod" =>
        let rs := ps.map fun (a, b) => if sc then divmodScalar t a b else divmodArray t a b
        s!"OK {fmtInts (rs.map (·.1.1))} {fmtInts (rs.map (·.1.2))} {fmtFlags (foldFlags (rs.map (·.2)))}"
      | _ => "BADOP"
  | _ => "BADARGS"

/-- `pow <ty> <path> <xs> <ys>` prints `OK <values> <flags>` or `ERR negexp`. -/
def diffPow : Handler
  | [ty, path, xs, ys] =>
    match parseTy ty with
    | none => "BADTYPE"
    | some t =>
      let xs := parseInts xs
      let ys := parseInts ys
      let r : Except PowErr (List Int × Flags) :=
        if path == "scalar" then (powerScalar t (xs.headD 0) (ys.headD 0)).map fun (v, f) => ([v], f)
        else if path == "bcast" then (powerArrayBcast t xs (ys.headD 0)).map fun vs => (vs, .clear)
        else (powerArray t xs ys).map fun vs => (vs, .clear)
      match r with
      | .ok (vs, f) => s!"OK {fmtInts vs} {fmtFlags f}"
      | .error .negativeExponent => "ERR negexp"
  | _ => "BADARGS"

/-- `gl <op> <ty> <path> <xs> <ys>` with `op` one of `gcd`, `lcm`. It prints `OK <values> _`. -/
def diffGcdLcm : Handler
  | [op, ty, path, xs, ys] =>
    match parseTy ty with
    | none => "BADTYPE"
    | some t =>
      let ps := operands path (parseInts xs) (parseInts ys)
      match op with
      | "gcd" => s!"OK {fmtInts (ps.map fun (a, b) => gcdElem t a b)} _"
      | "lcm" => s!"OK {fmtInts (ps.map fun (a, b) => lcmElem t a b)} _"
      | _ => "BADOP"
  | _ => "BADARGS"

/-- `shift <op> <ty> <path> <xs> <ys>` with `op` one of `left_shift`, `right_shift`. It prints `OK <values> _`. -/
def diffShift : Handler
  | [op, ty, path, xs, ys] =>
    match parseTy ty with
    | none => "BADTYPE"
    | some t =>
      let ps := operands path (parseInts xs) (parseInts ys)
      match op with
      | "left_shift" => s!"OK {fmtInts (ps.map fun (a, b) => lshift t a b)} _"
      | "right_shift" => s!"OK {fmtInts (ps.map fun (a, b) => rshift t a b)} _"
      | _ => "BADOP"
  | _ => "BADARGS"

/-- `un <op> <ty> <path> <xs>` with `op` one of `absolute`, `sign`. The scalar path of `absolute` is the builtin `abs`. It prints `OK <values> <flags>`. -/
def diffUnary : Handler
  | [op, ty, path, xs] =>
    match parseTy ty with
    | none => "BADTYPE"
    | some t =>
      let xs := parseInts xs
      match op with
      | "absolute" =>
        if path == "scalar" then
          let rs := xs.map (absScalar t)
          s!"OK {fmtInts (rs.map (·.1))} {fmtFlags (foldFlags (rs.map (·.2)))}"
        else s!"OK {fmtInts (xs.map (absArray t))} _"
      | "sign" => s!"OK {fmtInts (xs.map (signElem t))} _"
      | _ => "BADOP"
  | _ => "BADARGS"

/-- `mul <ty> <path> <xs> <ys>` prints `OK <values> <flags>`. -/
def diffMul : Handler
  | [ty, path, xs, ys] =>
    match parseTy ty with
    | none => "BADTYPE"
    | some t =>
      let ps := operands path (parseInts xs) (parseInts ys)
      if path == "scalar" then
        let rs := ps.map fun (a, b) => multiplyScalar t a b
        s!"OK {fmtInts (rs.map (·.1))} {fmtFlags (foldFlags (rs.map (·.2)))}"
      else s!"OK {fmtInts (ps.map fun (a, b) => multiplyArray t a b)} _"
  | _ => "BADARGS"

def handlers : List (String × Handler) :=
  [("div", diffDiv), ("pow", diffPow), ("gl", diffGcdLcm), ("shift", diffShift), ("un", diffUnary), ("mul", diffMul)]

end NumpyLean.IntArith
