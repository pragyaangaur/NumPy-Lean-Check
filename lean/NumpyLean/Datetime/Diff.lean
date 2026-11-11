import NumpyLean.Datetime.Model
import NumpyLean.Common.Wire

/-
Handlers for the datetime models.

A unit is written as its NumPy name (`Y`, `M`, `W`, `D`, `h`, `m`, `s`, `ms`, `us`, `ns`, `ps`, `fs`, `as`) followed by the multiplier as a separate token. A weekmask is seven characters `0` or `1` starting with Monday. A string for the parser is sent as the hexadecimal code of its ASCII bytes, or `_` for the empty string, so that spaces survive the line format.
-/
namespace NumpyLean.Datetime
open NumpyLean.Wire

def errName : Err → String
  | .genericUnits => "generic"
  | .scaleOverflow => "overflow"
  | .factorOverflow => "factor"
  | .toGeneric => "togeneric"
  | .gcdOverflow => "gcd"
  | .incompatibleUnits => "incompatible"

def parseMeta (u n : String) : Option Meta := (DUnit.ofName u).map fun b => ⟨b, parseInt n⟩

def hexVal (c : Char) : Nat :=
  if '0' ≤ c && c ≤ '9' then c.toNat - 48 else if 'a' ≤ c && c ≤ 'f' then c.toNat - 87 else 0

def unhex : List Char → List Char
  | a :: b :: rest => Char.ofNat (16 * hexVal a + hexVal b) :: unhex rest
  | _ => []

def parseMask (s : String) : List Bool := s.toList.map (· == '1')

/-- `tostr <unit> <num> <value> <printunit>` is `np.datetime_as_string` on a one element array. `printunit` is `_` for the default, `auto` or a unit name. It prints `OK <string>` or `ERR <kind>`. -/
def diffToStr : Handler
  | [u, n, v, pu] =>
    match parseMeta u n with
    | none => "BADUNIT"
    | some m =>
      let unit : Option (Option DUnit) := if pu == "_" then none else if pu == "auto" then some none else some (DUnit.ofName pu)
      match datetimeAsString m (parseInt v) unit with
      | .ok s => s!"OK {s}"
      | .error e => s!"ERR {errName e}"
  | _ => "BADARGS"

/-- `cast <u1> <n1> <u2> <n2> <value>` is `astype` between two datetime64 dtypes. It prints `OK <value>` or `ERR <kind>`. -/
def diffCast : Handler
  | [u1, n1, u2, n2, v] =>
    match parseMeta u1 n1, parseMeta u2 n2 with
    | some m1, some m2 =>
      match castDatetime m1 m2 (parseInt v) with
      | .ok r => s!"OK {r}"
      | .error e => s!"ERR {errName e}"
    | _, _ => "BADUNIT"
  | _ => "BADARGS"

/-- `cmp <u1> <n1> <v1> <u2> <n2> <v2>` prints the common dtype of the two datetimes and the results of `<` and `==`, as `OK <unit> <num> <lt> <eq>`, or `ERR <kind>`. -/
def diffCmp : Handler
  | [u1, n1, v1, u2, n2, v2] =>
    match parseMeta u1 n1, parseMeta u2 n2 with
    | some m1, some m2 =>
      match commonMeta m1 m2 with
      | .error e => s!"ERR {errName e}"
      | .ok c =>
        match compareDatetimes m1 (parseInt v1) m2 (parseInt v2) with
        | .ok (lt, eq) => s!"OK {c.base.name} {c.num} {fmtBool lt} {fmtBool eq}"
        | .error e => s!"ERR {errName e}"
    | _, _ => "BADUNIT"
  | _ => "BADARGS"

def perrName : PErr → String
  | .parse p => s!"parse {p}"
  | .month => "month"
  | .day => "day"
  | .hour => "hour"
  | .minute => "minute"
  | .second => "second"
  | .tzHour => "tzhour"
  | .tzMinute => "tzminute"
  | .special => "special"
  | .generic => "generic"

/-- `parse <unit|_> <num> <hex>` is `np.datetime64(s)` or `np.datetime64(s, f"{num}{unit}")`. It prints `OK <unit> <num> <value>` with NaT as the minimum int64, or `ERR <kind>`. -/
def diffParse : Handler
  | [u, n, hx] =>
    let s := if hx == "_" then [] else unhex hx.toList
    let md := if u == "_" then none else parseMeta u n
    match parseDatetime s md with
    | .ok (m, v) => s!"OK {m.base.name} {m.num} {v}"
    | .error e => s!"ERR {perrName e}"
  | _ => "BADARGS"

def parseRoll : String → Roll
  | "forward" => .forward
  | "following" => .following
  | "backward" => .backward
  | "preceding" => .preceding
  | "modifiedfollowing" => .modifiedfollowing
  | "modifiedpreceding" => .modifiedpreceding
  | "nat" => .nat
  | _ => .raise

def berrName : BErr → String
  | .natInput => "natinput"
  | .nonBusiness => "nonbusiness"
  | .emptyMask => "emptymask"
  | .natCount => "natcount"

/-- `busoff <date> <offset> <roll> <mask> <holidays>` is `np.busday_offset` on day values. It prints `OK <value>` or `ERR <kind>`. -/
def diffBusOff : Handler
  | [d, off, roll, mask, hs] =>
    let mask := parseMask mask
    match busdayOffset (parseInt d) (parseInt off) (parseRoll roll) mask (normalizeHolidays mask (parseInts hs)) with
    | .ok r => s!"OK {r}"
    | .error e => s!"ERR {berrName e}"
  | _ => "BADARGS"

/-- `buscount <begin> <end> <mask> <holidays>` is `np.busday_count`. It prints `OK <count>`, `ERR <kind>` or `HANG` when the remaining days loop would run more than a million steps. -/
def diffBusCount : Handler
  | [b, e, mask, hs] =>
    let mask := parseMask mask
    match busdayCount 1000000 (parseInt b) (parseInt e) mask (normalizeHolidays mask (parseInts hs)) with
    | .ok (some c) => s!"OK {c}"
    | .ok none => "HANG"
    | .error e => s!"ERR {berrName e}"
  | _ => "BADARGS"

/-- `isbus <date> <mask> <holidays>` is `np.is_busday`. It prints `OK True` or `OK False`, or `ERR emptymask`. -/
def diffIsBus : Handler
  | [d, mask, hs] =>
    let mask := parseMask mask
    if (mask.filter id).isEmpty then "ERR emptymask"
    else s!"OK {fmtBool (isBusday (parseInt d) mask (normalizeHolidays mask (parseInts hs)))}"
  | _ => "BADARGS"

def handlers : List (String × Handler) :=
  [("tostr", diffToStr), ("cast", diffCast), ("cmp", diffCmp), ("parse", diffParse),
   ("busoff", diffBusOff), ("buscount", diffBusCount), ("isbus", diffIsBus)]

end NumpyLean.Datetime
