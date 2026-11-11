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
  | .dtype => "ERR type"
  | .overflow => "ERR overflow"
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

def fmtStrExc : Except SErr Str → String
  | .ok s => s!"OK {fmtStr s}"
  | .error e => errStr e

/-- `just <kind> <c|l|r> <a> <width> <fill>` runs `center`, `ljust` or `rjust`. -/
def diffJust : Handler
  | [k, p, a, w, f] =>
    let pos := if p == "c" then Pos.center else if p == "l" then Pos.left else Pos.right
    fmtStrExc (justImpl (parseKind k) pos (parseStr a) (parseInt w) (parseStr f))
  | _ => "BADARGS"

/-- `zfill <kind> <a> <width>`. -/
def diffZfill : Handler
  | [k, a, w] => fmtStrExc (zfillImpl (parseKind k) (parseStr a) (parseInt w))
  | _ => "BADARGS"

/-- `expandtabs <kind> <a> <tabsize>`. -/
def diffExpandtabs : Handler
  | [k, a, t] => fmtStrExc (expandtabsImpl (parseKind k) (parseStr a) (parseInt t))
  | _ => "BADARGS"

/-- `replace <kind> <a> <old> <new> <count>`. -/
def diffReplace : Handler
  | [k, a, o, n, c] => s!"OK {fmtStr (replaceImpl (parseKind k) (parseStr a) (parseStr o) (parseStr n) (parseInt c))}"
  | _ => "BADARGS"

/-- `partition <kind> <a> <sep>` and `rpartition`. The three parts are joined by `|`. -/
def diffPartition (front : Bool) : Handler
  | [k, a, s] =>
    match partitionImpl (parseKind k) front (parseStr a) (parseStr s) with
    | .ok (x, y, z) => s!"OK {fmtStr x}|{fmtStr y}|{fmtStr z}"
    | .error e => errStr e
  | _ => "BADARGS"

/-- `strip <kind> <l|r|b> <a> <chars>` where `chars` is `!` for whitespace. -/
def diffStrip : Handler
  | [k, m, a, c] =>
    let mode := if m == "l" then Strip.left else if m == "r" then Strip.right else Strip.both
    let chars := if c == "!" then none else some (parseStr c)
    s!"OK {fmtStr (stripImpl (parseKind k) mode (parseStr a) chars)}"
  | _ => "BADARGS"

/-- `slice <kind> <a> <start> <stop> <step>`. -/
def diffSlice : Handler
  | [k, a, s, e, st] => fmtStrExc (sliceImpl (parseKind k) (parseStr a) (parseInt s) (parseInt e) (parseInt st))
  | _ => "BADARGS"

/-- A long string is given as `unit:count` pieces joined by `;`, and `_` is empty. The unit is written with the letters `a`, `b` and `c`, which stand for the code units 97, 98 and 233. -/
def parseSpec (s : String) : Str :=
  if s == "_" then []
  else
    (s.splitOn ";").flatMap fun piece =>
      match piece.splitOn ":" with
      | [u, n] =>
        let unit : Str := u.toList.map fun ch => if ch == 'a' then 97 else if ch == 'b' then 98 else 233
        (List.replicate (parseInt n).toNat unit).flatten
      | _ => []

/-- `long <kind> <find|rfind|count> <hay spec> <needle spec> <start> <end>`. -/
def diffLong : Handler
  | [k, op, h, n, s, e] =>
    let kind := parseKind k
    let a := parseSpec h
    let nd := parseSpec n
    let st := parseInt s
    let en := parseInt e
    if op == "find" then fmtIntRes (findImpl kind a nd st en)
    else if op == "rfind" then fmtIntRes (rfindImpl kind a nd st en)
    else fmtIntRes (countImpl kind a nd st en)
  | _ => "BADARGS"

def handlers : List (String × Handler) := [
  ("find", diffFindLike fun k a n s e => .ok (findImpl k a n s e)),
  ("rfind", diffFindLike fun k a n s e => .ok (rfindImpl k a n s e)),
  ("index", diffFindLike indexImpl),
  ("rindex", diffFindLike rindexImpl),
  ("count", diffFindLike fun k a n s e => .ok (countImpl k a n s e)),
  ("startswith", diffTail true),
  ("endswith", diffTail false),
  ("str_len", diffStrLen),
  ("just", diffJust),
  ("zfill", diffZfill),
  ("expandtabs", diffExpandtabs),
  ("replace", diffReplace),
  ("partition", diffPartition true),
  ("rpartition", diffPartition false),
  ("strip", diffStrip),
  ("slice", diffSlice),
  ("long", diffLong)]

end NumpyLean.Strings
