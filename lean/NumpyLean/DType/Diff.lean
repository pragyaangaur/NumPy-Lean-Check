import NumpyLean.DType.Model
import NumpyLean.Common.Wire

/-
Wire format of the dtype tests. A dtype is written as its type character (`?`, `b`, `B`, `h`, `H`, `i`, `I`, `l`, `L`, `q`, `Q`, `e`, `f`, `d`, `g`, `F`, `D`, `G`, `O`) or as `S<n>` or `U<n>` with the length in characters. A Python scalar argument of `np.result_type` is written `Pi`, `Pf` or `Pc`.
-/
namespace NumpyLean.DType
open NumpyLean.Wire

def typeChars : List (Char × Nat) :=
  [('?', 0), ('b', 1), ('B', 2), ('h', 3), ('H', 4), ('i', 5), ('I', 6), ('l', 7), ('L', 8),
   ('q', 9), ('Q', 10), ('f', 11), ('d', 12), ('g', 13), ('F', 14), ('D', 15), ('G', 16),
   ('O', 17), ('e', 23)]

def parseDescr (s : String) : Option Descr :=
  match s.toList with
  | ['S'] => some ⟨NPY_STRING, 0⟩
  | ['U'] => some ⟨NPY_UNICODE, 0⟩
  | 'S' :: rest => (String.ofList rest).toNat?.map (fun n => ⟨NPY_STRING, n⟩)
  | 'U' :: rest => (String.ofList rest).toNat?.map (fun n => ⟨NPY_UNICODE, n⟩)
  | [c] => (typeChars.lookup c).map (fun n => ⟨n, 0⟩)
  | _ => none

def fmtDescr (d : Descr) : String :=
  if d.num == NPY_STRING then s!"S{d.chars}"
  else if d.num == NPY_UNICODE then s!"U{d.chars}"
  else match typeChars.find? (fun p => p.2 == d.num) with
    | some (c, _) => c.toString
    | none => s!"#{d.num}"

def parseCasting (s : String) : Option Casting :=
  match s with
  | "no" => some .no | "equiv" => some .equiv | "safe" => some .safe
  | "same_kind" => some .sameKind | "unsafe" => some .«unsafe»
  | _ => none

def parseArg (s : String) : Option Arg :=
  match s with
  | "Pi" => some .pyInt | "Pf" => some .pyFloat | "Pc" => some .pyComplex
  | _ => (parseDescr s).map Arg.dtype

/-- `can_cast <from> <to>` prints five digits, one per casting level from `no` to `unsafe`. -/
def diffCanCast : Handler
  | [a, b] =>
    match parseDescr a, parseDescr b with
    | some f, some t =>
      let bits := [Casting.no, .equiv, .safe, .sameKind, .«unsafe»].map
        (fun c => if canCast f t c then "1" else "0")
      String.join bits
    | _, _ => "BADARGS"
  | _ => "BADARGS"

/-- `promote <a> <b>` prints `OK <dtype>` or `ERR promotion`. -/
def diffPromote : Handler
  | [a, b] =>
    match parseDescr a, parseDescr b with
    | some x, some y =>
      match promoteTypes x y with
      | some r => "OK " ++ fmtDescr r
      | none => "ERR promotion"
    | _, _ => "BADARGS"
  | _ => "BADARGS"

/-- `result_type <arg> ...` prints `OK <dtype>` or `ERR promotion`. -/
def diffResultType : Handler
  | args =>
    match args.mapM parseArg with
    | some l =>
      match resultType l with
      | some r => "OK " ++ fmtDescr r
      | none => "ERR promotion"
    | none => "BADARGS"

/-- `pyint_op <dtype> <int>` prints `OK <dtype>` for the result of adding the Python int, or `ERR overflow`. -/
def diffPyIntOp : Handler
  | [a, v] =>
    match parseDescr a, v.toInt? with
    | some d, some x =>
      match pyIntOp d.num x with
      | some r => "OK " ++ fmtDescr r
      | none => "ERR overflow"
    | _, _ => "BADARGS"
  | _ => "BADARGS"

def handlers : List (String × Handler) :=
  [("can_cast", diffCanCast), ("promote", diffPromote), ("result_type", diffResultType),
   ("pyint_op", diffPyIntOp)]

end NumpyLean.DType
