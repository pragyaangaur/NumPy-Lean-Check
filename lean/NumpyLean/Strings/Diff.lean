import NumpyLean.Strings.Model
import NumpyLean.Common.Wire

namespace NumpyLean.Strings
open NumpyLean.Wire

/-- The kind token is `S`, `U` or `T`. -/
def parseKind : String → Kind
  | "S" => .S
  | "U" => .U
  | _ => .T

/-- A string argument is its code units as comma separated integers, and `_` for the empty string. -/
def parseStr (s : String) : Str := parseInts s

def fmtStr (s : Str) : String := fmtInts s

/-- An integer result is printed with a class word first so that the outcome counts show which branches ran. -/
def fmtIntRes (n : Int) : String :=
  if n < 0 then s!"NEG {n}" else if n == 0 then "ZERO 0" else s!"POS {n}"

def errStr : SErr → String
  | .notFound => "ERR value"
  | .emptySep => "ERR value"
  | .fillLen => "ERR type"
  | .tooLong => "ERR overflow"
  | .stepZero => "ERR value"
  | .alloc => "ERR alloc"

def fmtIntExc : Except SErr Int → String
  | .ok n => fmtIntRes n
  | .error e => errStr e

/-- `find <kind> <a> <sub> <start> <end>`, and likewise `rfind`, `index`, `rindex`, `count`. -/
def diffFindLike (f : Kind → Str → Str → Int → Int → Except SErr Int) : Handler
  | [k, a, n, s, e] => fmtIntExc (f (parseKind k) (parseStr a) (parseStr n) (parseInt s) (parseInt e))
  | _ => "BADARGS"

/-- `startswith <kind> <a> <sub> <start> <end>` and `endswith`. -/
def diffTail (front : Bool) : Handler
  | [k, a, n, s, e] => fmtBool (tailmatchImpl (parseKind k) front (parseStr a) (parseStr n) (parseInt s) (parseInt e))
  | _ => "BADARGS"

/-- `str_len <kind> <a>`. -/
def diffStrLen : Handler
  | [k, a] => fmtIntRes (strLen (parseKind k) (parseStr a))
  | _ => "BADARGS"

def handlers : List (String × Handler) := [
  ("find", diffFindLike fun k a n s e => .ok (findImpl k a n s e)),
  ("rfind", diffFindLike fun k a n s e => .ok (rfindImpl k a n s e)),
  ("index", diffFindLike indexImpl),
  ("rindex", diffFindLike rindexImpl),
  ("count", diffFindLike fun k a n s e => .ok (countImpl k a n s e)),
  ("startswith", diffTail true),
  ("endswith", diffTail false),
  ("str_len", diffStrLen)]

end NumpyLean.Strings
