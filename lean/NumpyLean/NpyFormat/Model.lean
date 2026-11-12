import NumpyLean.Common.Intp
import NumpyLean.Shape.Model

/-
Model of the `.npy` header code in `numpy/lib/_format_impl.py`: `_wrap_header`, `_wrap_header_guess_version` and `_write_array_header` on the writing side. All source lines cited below are relative to `vendor/numpy/numpy/`.
-/
namespace NumpyLean.NpyFormat
open NumpyLean

/-- `MAGIC_LEN`, `lib/_format_impl.py:179`: six magic bytes and two version bytes. -/
def magicLen : Nat := 8

/-- `ARRAY_ALIGN`, `lib/_format_impl.py:180`. -/
def arrayAlign : Nat := 64

/-- `GROWTH_AXIS_MAX_DIGITS`, `lib/_format_impl.py:183`. -/
def growthAxisMaxDigits : Nat := 21

/-- `_MAX_HEADER_SIZE`, `lib/_format_impl.py:196`. -/
def maxHeaderSize : Nat := 10000

/-- The three format versions of `_header_size_info`, `lib/_format_impl.py:185`. -/
inductive Version where
  | v1 | v2 | v3
  deriving DecidableEq, Repr

def Version.major : Version → Nat
  | .v1 => 1 | .v2 => 2 | .v3 => 3

/-- Width in bytes of the header length field: `<H` for 1.0 and `<I` for 2.0 and 3.0. -/
def Version.sizeBytes : Version → Nat
  | .v1 => 2 | _ => 4

/-- Versions 1.0 and 2.0 encode the header as latin1, version 3.0 as utf8. -/
def Version.latin1 : Version → Bool
  | .v3 => false | _ => true

/-- `header.encode(encoding)` (line 405) gives the number of bytes, or `none` when a latin1 header holds a character above U+00FF. -/
def encodedLength (v : Version) (s : String) : Option Nat :=
  if v.latin1 then (if s.toList.all (fun c => c.toNat < 256) then some s.length else none)
  else some s.utf8ByteSize

inductive WrapError where
  /-- `UnicodeEncodeError` from `header.encode('latin1')`. -/
  | unicode
  /-- `ValueError: Header length ... too big for version=...`, raised on `struct.error` at line 410. -/
  | tooBig
  deriving DecidableEq, Repr

/-- The result of `_wrap_header`: the version, the value stored in the length field, the total number of bytes and the number of padding spaces before the final newline. -/
structure Wrapped where
  version : Version
  hfield : Nat
  total : Nat
  padlen : Nat
  deriving DecidableEq, Repr

/--
`_wrap_header`, `lib/_format_impl.py:397`. The header is padded with `padlen` spaces and one newline so that magic, length field and header end on a multiple of `ARRAY_ALIGN`. Note that a header whose prefix is already aligned still gets a full `ARRAY_ALIGN` bytes of padding, because the modulus in line 408 is never subtracted from zero.
-/
def wrapHeader (v : Version) (hdr : String) : Except WrapError Wrapped :=
  match encodedLength v hdr with
  | none => .error .unicode
  | some n =>
    let hlen := n + 1
    let padlen := arrayAlign - ((magicLen + v.sizeBytes + hlen) % arrayAlign)
    let field := hlen + padlen
    if field < 256 ^ v.sizeBytes then
      .ok { version := v, hfield := field, total := magicLen + v.sizeBytes + field, padlen := padlen }
    else .error .tooBig

/--
`_wrap_header_guess_version`, `lib/_format_impl.py:421`. Version 1.0 is tried first and any `ValueError` sends it to 2.0. Only a `UnicodeEncodeError` sends version 2.0 on to 3.0, and any other error is raised.
-/
def wrapGuess (hdr : String) : Except WrapError Wrapped :=
  match wrapHeader .v1 hdr with
  | .ok w => .ok w
  | .error _ =>
    match wrapHeader .v2 hdr with
    | .error .unicode => wrapHeader .v3 hdr
    | r => r

/-- `repr(shape)` for a tuple of Python integers. -/
def reprShape : List Int → String
  | [] => "()"
  | [x] => s!"({x},)"
  | xs => "(" ++ ", ".intercalate (xs.map toString) ++ ")"

/-- The characters that the tests put into descriptor strings and that `repr` leaves alone or escapes in the simple way modelled here. -/
def reprChar (q : Char) (c : Char) : String :=
  if c == '\\' then "\\\\"
  else if c == q then "\\" ++ String.singleton q
  else String.singleton c

/-- `repr(str)` for strings made of printable characters. Python picks double quotes when the string holds a single quote and no double quote. -/
def reprPyStr (s : String) : String :=
  let q : Char := if s.contains '\'' && !s.contains '"' then '"' else '\''
  String.singleton q ++ String.join (s.toList.map (reprChar q)) ++ String.singleton q

/-- The dictionary text of `_write_array_header`, `lib/_format_impl.py:458`, without the spare growth space. Keys are sorted, so `descr`, `fortran_order`, `shape`. -/
def headerBase (descr : String) (fortran : Bool) (shape : List Int) : String :=
  "{'descr': " ++ reprPyStr descr ++ ", 'fortran_order': " ++ (if fortran then "True" else "False")
    ++ ", 'shape': " ++ reprShape shape ++ ", }"

/-- The number of spare spaces that `_write_array_header` adds at lines 469 to 473: the shape entry on the growth axis is padded to `GROWTH_AXIS_MAX_DIGITS` characters, and a longer entry gets none (`" " * negative` is empty). -/
def growthSpaces (fortran : Bool) (shape : List Int) : Nat :=
  match (if fortran then shape.getLast? else shape.head?) with
  | none => 0
  | some x => growthAxisMaxDigits - (toString x).length

def headerText (descr : String) (fortran : Bool) (shape : List Int) : String :=
  headerBase descr fortran shape ++ String.ofList (List.replicate (growthSpaces fortran shape) ' ')

/-- `_write_array_header`, `lib/_format_impl.py:445`, with `version = none` meaning automatic choice. -/
def writeHeader (ver : Option Version) (descr : String) (fortran : Bool) (shape : List Int) : Except WrapError Wrapped :=
  let h := headerText descr fortran shape
  match ver with
  | none => wrapGuess h
  | some v => wrapHeader v h

/-!
## Reading a header

`_read_array_header`, `lib/_format_impl.py:621`, evaluates the header with `ast.literal_eval`. The model below tokenizes and parses the small part of Python that the tests produce: dictionaries, tuples, lists, sets, integers, floats, booleans, `None`, strings without escapes, names, unary and binary plus and minus. Python that falls outside this part (calls, subscripts, attribute access, exponents, imaginary numbers, escapes in strings) is not modelled, and the tests leave such texts out.
-/

inductive Tok where
  | lbrace | rbrace | lpar | rpar | lbrack | rbrack | comma | colon | plus | minus
  | str (s : String)
  | int (n : Int)
  | flt
  | name (s : String)
  /-- A newline outside brackets. -/
  | nl
  /-- A character or number form that Python rejects. -/
  | bad
  deriving DecidableEq, Repr

def isDigitC (c : Char) : Bool := '0' ≤ c && c ≤ '9'
def isIdStartC (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_'
def isIdC (c : Char) : Bool := isIdStartC c || isDigitC c

def digitsToInt (ds : List Char) : Int := ds.foldl (fun a c => a * 10 + ((c.toNat - 48 : Nat) : Int)) 0

/--
The tokenizer. It returns the tokens and a flag that says whether `tokenize.generate_tokens` raises `TokenError`, which happens for an unterminated string and for a header that ends inside brackets (`lib/_format_impl.py:586`). A closing bracket without an opener does not raise.
-/
def tokenizeAux : Nat → Nat → List Tok → List Char → List Tok × Bool
  | 0, _, acc, _ => (acc.reverse, false)
  | _ + 1, depth, acc, [] => (acc.reverse, depth != 0)
  | n + 1, depth, acc, c :: cs =>
    if c == ' ' || c == '\t' then tokenizeAux n depth acc cs
    else if c == '\n' then
      (if depth == 0 then tokenizeAux n depth (.nl :: acc) cs else tokenizeAux n depth acc cs)
    else if c == '{' then tokenizeAux n (depth + 1) (.lbrace :: acc) cs
    else if c == '}' then tokenizeAux n (depth - 1) (.rbrace :: acc) cs
    else if c == '(' then tokenizeAux n (depth + 1) (.lpar :: acc) cs
    else if c == ')' then tokenizeAux n (depth - 1) (.rpar :: acc) cs
    else if c == '[' then tokenizeAux n (depth + 1) (.lbrack :: acc) cs
    else if c == ']' then tokenizeAux n (depth - 1) (.rbrack :: acc) cs
    else if c == ',' then tokenizeAux n depth (.comma :: acc) cs
    else if c == ':' then tokenizeAux n depth (.colon :: acc) cs
    else if c == '+' then tokenizeAux n depth (.plus :: acc) cs
    else if c == '-' then tokenizeAux n depth (.minus :: acc) cs
    else if c == '\'' || c == '"' then
      let (body, rest) := cs.span (· != c)
      match rest with
      | [] => ((Tok.bad :: acc).reverse, true)
      | _ :: rest' =>
        if body.contains '\n' then ((Tok.bad :: acc).reverse, true)
        else tokenizeAux n depth (.str (String.ofList body) :: acc) rest'
    else if isDigitC c then
      let (d1, r1) := (c :: cs).span isDigitC
      match r1 with
      | '.' :: r2 =>
        let (_, r3) := r2.span isDigitC
        tokenizeAux n depth (.flt :: acc) r3
      | _ =>
        -- A decimal integer with a leading zero is a syntax error unless it is all zeros.
        if d1.length > 1 && d1.head? == some '0' && d1.any (· != '0') then
          tokenizeAux n depth (.bad :: acc) r1
        else tokenizeAux n depth (.int (digitsToInt d1) :: acc) r1
    else if c == '.' then
      match cs with
      | d :: _ =>
        if isDigitC d then
          let (_, r3) := cs.span isDigitC
          tokenizeAux n depth (.flt :: acc) r3
        else tokenizeAux n depth (.bad :: acc) cs
      | [] => tokenizeAux n depth (.bad :: acc) cs
    else if isIdStartC c then
      let (nm, rest) := cs.span isIdC
      tokenizeAux n depth (.name (String.ofList (c :: nm)) :: acc) rest
    else tokenizeAux n depth (.bad :: acc) cs

def tokenize (s : String) : List Tok × Bool :=
  let cs := s.toList
  tokenizeAux (cs.length + 1) 0 [] cs

/-- `_filter_header`, `lib/_format_impl.py:586`: an `L` name that follows a number token is dropped, and a dropped token does not reset the memory of the last token. -/
def filterL : Bool → List Tok → List Tok
  | _, [] => []
  | last, t :: ts =>
    match t with
    | .name "L" => if last then filterL last ts else t :: filterL false ts
    | .int _ => t :: filterL true ts
    | .flt => t :: filterL true ts
    | _ => t :: filterL false ts

inductive Kind where
  | int | flt | bool | none | str | tuple | list | dict | set
  /-- A name, a binary operation or a bad unary operation: `ast.literal_eval` rejects these. -/
  | poison
  deriving DecidableEq, Repr

inductive EvalErr where
  /-- `ValueError: malformed node or string`. -/
  | malformed
  /-- `TypeError: unhashable type`. -/
  | unhashable
  deriving DecidableEq, Repr

/-- What `ast.literal_eval` builds for one node, with just enough detail for the checks of `_read_array_header`. `err` is the first error that the conversion of the node would raise. -/
structure Val where
  kind : Kind
  hashable : Bool := true
  intv : Int := 0
  strv : String := ""
  /-- For a tuple whose entries are all `int` or `bool`, their values. -/
  ints : Option (List Int) := none
  /-- The key and value pairs of a dictionary. -/
  entries : List (Val × Val) := []
  err : Option EvalErr := none
  /-- Whether the node is a plain `Constant`, as the operand of a unary sign must be. -/
  isConst : Bool := false

def firstErr (vs : List Val) : Option EvalErr := vs.findSome? (·.err)

def mkTuple (items : List Val) : Val :=
  { kind := .tuple, hashable := items.all (·.hashable),
    ints := if items.all (fun v => v.kind == .int || v.kind == .bool) then some (items.map (·.intv)) else none,
    err := firstErr items }

def mkList (items : List Val) : Val := { kind := .list, hashable := false, err := firstErr items }

/-- `dict(zip(map(_convert, keys), map(_convert, values)))`: pair by pair, key, then value, then the insertion that hashes the key. -/
def mkDict (pairs : List (Val × Val)) : Val :=
  let err := pairs.findSome? (fun (k, v) =>
    match k.err with
    | some e => some e
    | none => match v.err with
      | some e => some e
      | none => if k.hashable then none else some EvalErr.unhashable)
  { kind := .dict, hashable := false, entries := pairs, err := err }

/-- `set(map(_convert, elts))`. -/
def mkSet (items : List Val) : Val :=
  let err := items.findSome? (fun v =>
    match v.err with
    | some e => some e
    | none => if v.hashable then none else some EvalErr.unhashable)
  { kind := .set, hashable := false, err := err }

def poisonVal : Val := { kind := .poison, err := some .malformed }

/-- Adjacent string literals are joined, as in `'a' 'b'`. -/
def concatStrs : String → List Tok → String × List Tok
  | acc, [] => (acc, [])
  | acc, t :: r =>
    match t with
    | .str s => concatStrs (acc ++ s) r
    | _ => (acc, t :: r)

mutual
/-- One expression: unary operations joined by binary plus and minus. -/
def pExpr : Nat → List Tok → Option (Val × List Tok)
  | 0, _ => none
  | n + 1, ts => do
    let (u, r) ← pUnary n ts
    pSum n u r

/-- Any binary plus or minus makes the node a `BinOp`, which `literal_eval` accepts only for complex numbers. -/
def pSum : Nat → Val → List Tok → Option (Val × List Tok)
  | 0, _, _ => none
  | n + 1, acc, ts =>
    match ts with
    | .plus :: r => do let (_, r') ← pUnary n r; pSum n poisonVal r'
    | .minus :: r => do let (_, r') ← pUnary n r; pSum n poisonVal r'
    | _ => some (acc, ts)

def pUnary : Nat → List Tok → Option (Val × List Tok)
  | 0, _ => none
  | n + 1, ts =>
    match ts with
    | .plus :: r => do
      let (v, r') ← pUnary n r
      let ok := v.isConst && (v.kind == .int || v.kind == .flt)
      some (if ok then { v with isConst := false } else poisonVal, r')
    | .minus :: r => do
      let (v, r') ← pUnary n r
      let ok := v.isConst && (v.kind == .int || v.kind == .flt)
      some (if ok then { v with intv := -v.intv, isConst := false } else poisonVal, r')
    | _ => pAtom n ts

def pAtom : Nat → List Tok → Option (Val × List Tok)
  | 0, _ => none
  | n + 1, ts =>
    match ts with
    | .int k :: r => some ({ kind := .int, intv := k, isConst := true }, r)
    | .flt :: r => some ({ kind := .flt, isConst := true }, r)
    | .str s :: r => let (s', r') := concatStrs s r; some ({ kind := .str, strv := s', isConst := true }, r')
    | .name "True" :: r => some ({ kind := .bool, intv := 1, isConst := true }, r)
    | .name "False" :: r => some ({ kind := .bool, intv := 0, isConst := true }, r)
    | .name "None" :: r => some ({ kind := .none, isConst := true }, r)
    | .name _ :: r => some (poisonVal, r)
    | .lpar :: .rpar :: r => some (mkTuple [], r)
    | .lpar :: r => do
      let (e, r1) ← pExpr n r
      match r1 with
      | .rpar :: r2 => some (e, r2)
      | .comma :: r2 => do
        let (items, r3) ← pItems n .rpar r2 [e]
        some (mkTuple items, r3)
      | _ => none
    | .lbrack :: .rbrack :: r => some (mkList [], r)
    | .lbrack :: r => do
      let (e, r1) ← pExpr n r
      match r1 with
      | .rbrack :: r2 => some (mkList [e], r2)
      | .comma :: r2 => do
        let (items, r3) ← pItems n .rbrack r2 [e]
        some (mkList items, r3)
      | _ => none
    | .lbrace :: .rbrace :: r => some (mkDict [], r)
    | .lbrace :: r => do
      let (e, r1) ← pExpr n r
      match r1 with
      | .colon :: r2 => do
        let (v, r3) ← pExpr n r2
        match r3 with
        | .rbrace :: r4 => some (mkDict [(e, v)], r4)
        | .comma :: r4 => do
          let (pairs, r5) ← pPairs n r4 [(e, v)]
          some (mkDict pairs, r5)
        | _ => none
      | .rbrace :: r2 => some (mkSet [e], r2)
      | .comma :: r2 => do
        let (items, r3) ← pItems n .rbrace r2 [e]
        some (mkSet items, r3)
      | _ => none
    | _ => none

/-- Items after a comma, up to the closing token. A trailing comma is allowed. `acc` holds the items read so far in order. -/
def pItems : Nat → Tok → List Tok → List Val → Option (List Val × List Tok)
  | 0, _, _, _ => none
  | n + 1, close, ts, acc =>
    match ts with
    | t :: r =>
      if t == close then some (acc, r)
      else do
        let (e, r1) ← pExpr n ts
        match r1 with
        | .comma :: r2 => pItems n close r2 (acc ++ [e])
        | t' :: r2 => if t' == close then some (acc ++ [e], r2) else none
        | [] => none
    | [] => none

/-- Dictionary pairs after a comma, up to the closing brace. -/
def pPairs : Nat → List Tok → List (Val × Val) → Option (List (Val × Val) × List Tok)
  | 0, _, _ => none
  | n + 1, ts, acc =>
    match ts with
    | .rbrace :: r => some (acc, r)
    | [] => none
    | _ => do
      let (k, r1) ← pExpr n ts
      match r1 with
      | .colon :: r2 => do
        let (v, r3) ← pExpr n r2
        match r3 with
        | .comma :: r4 => pPairs n r4 (acc ++ [(k, v)])
        | .rbrace :: r4 => some (acc ++ [(k, v)], r4)
        | _ => none
      | _ => none
end

/-- Top-level items of an unparenthesised tuple such as `1, 2,`, up to the end of the input. -/
def pTopItems : Nat → List Tok → List Val → Option (List Val)
  | 0, _, _ => none
  | n + 1, ts, acc =>
    match ts with
    | [] => some acc
    | _ => do
      let (e, r1) ← pExpr n ts
      match r1 with
      | [] => some (acc ++ [e])
      | .comma :: r2 => pTopItems n r2 (acc ++ [e])
      | _ => none

def trimNl (ts : List Tok) : List Tok :=
  ((ts.dropWhile (· == .nl)).reverse.dropWhile (· == .nl)).reverse

/-- The parse of a whole header in eval mode: leading and trailing newlines are allowed, and a comma at the top level makes a tuple. `none` is a `SyntaxError`. -/
def parseTokens (ts : List Tok) : Option Val :=
  let ts := trimNl ts
  if ts.any (· == .bad) then none else
  let fuel := 8 * ts.length + 8
  match pExpr fuel ts with
  | some (e, []) => some e
  | some (e, .comma :: r) => (pTopItems fuel r [e]).map mkTuple
  | _ => none

inductive ReadError where
  /-- `EOF: reading array header length`. -/
  | eofLen
  /-- `EOF: reading array header`. -/
  | eofHeader
  /-- `Header info length ... is large and may not be safe to load securely`. -/
  | tooLarge
  /-- `Cannot parse header`. -/
  | syntax
  /-- `tokenize.TokenError`, which is not a `ValueError`. -/
  | tokenError
  /-- `malformed node or string`. -/
  | malformed
  /-- `TypeError: unhashable type`. -/
  | unhashable
  /-- `Header is not a dictionary`. -/
  | notDict
  /-- `TypeError` from `sorted(d.keys())` in the message of the key error, when the keys cannot be compared. -/
  | keySort
  /-- `Header does not contain the correct keys`. -/
  | keys
  /-- `shape is not valid`. -/
  | shape
  /-- `fortran_order is not a valid bool`. -/
  | fortran
  /-- `descr is not a valid dtype descriptor`. -/
  | descr
  /-- `Invalid version`. -/
  | version
  /-- `UnicodeDecodeError` from the utf8 header of version 3.0. -/
  | decode
  deriving DecidableEq, Repr

/-- The accepted outcome of `_read_array_header`: the shape, `fortran_order` and `dtype.str`. -/
structure Header where
  shape : List Int
  fortran : Bool
  dtype : String
  deriving DecidableEq, Repr

/-- The units of datetime64 and timedelta64 that `np.dtype` accepts inside square brackets. -/
def datetimeUnits : List String := ["Y", "M", "W", "D", "h", "m", "s", "ms", "us", "ns", "ps", "fs", "as"]

/-- The unit part of a datetime descriptor, `[10us]` and the like, as `numpy.dtype` prints it. The count `1` is dropped, `generic` means no unit and a count must fit a C `int`. -/
def unitText (s : String) : Option String :=
  let cs := s.toList
  let (d, u) := cs.span isDigitC
  let name := String.ofList u
  let n := digitsToInt d
  if name == "generic" then (if d.isEmpty then some "" else none)
  else if datetimeUnits.contains name && n ≤ 2147483647 then
    some ("[" ++ (if d.isEmpty || n == 1 then "" else toString n) ++ name ++ "]")
  else none

/--
`numpy.dtype(descr)` for a string, reduced to the descriptors the tests use, returning `dtype.str`. A byte order character is optional, and one byte types always print `|`, all others `<` unless `>` was given. Sizes are read as numbers, so `S05` is `|S5`. Platform note: `f16` and `c32` need an 80 bit `long double` and do not exist on arm64 macOS, so they are rejected here.
-/
def dtypeStr (s : String) : Option String :=
  let cs := s.toList
  let (bo, rest) : Option Char × List Char :=
    match cs with
    | c :: r => if c == '<' || c == '>' || c == '=' || c == '|' then (some c, r) else (none, cs)
    | [] => (none, [])
  let order : String := if bo == some '>' then ">" else "<"
  match rest with
  | [] => none
  | k :: tail =>
    let isNum := !tail.isEmpty && tail.all isDigitC
    let n := (digitsToInt tail).toNat
    let sized (valid : List Nat) : Option String :=
      if isNum && valid.contains n then some ((if n == 1 then "|" else order) ++ String.singleton k ++ toString n) else none
    let flex (pre : String) : Option String :=
      if tail.isEmpty then some (pre ++ "0") else if isNum && n ≤ 2147483647 then some (pre ++ toString n) else none
    match k with
    | 'b' => if tail.isEmpty then some "|i1" else if isNum && n == 1 then some "|b1" else none
    | '?' => if tail.isEmpty then some "|b1" else none
    | 'i' => if tail.isEmpty then some (order ++ "i4") else sized [1, 2, 4, 8]
    | 'u' => sized [1, 2, 4, 8]
    | 'f' => if tail.isEmpty then some (order ++ "f4") else sized [2, 4, 8]
    | 'e' => if tail.isEmpty then some (order ++ "f2") else none
    | 'c' => if tail.isEmpty then some "|S1" else sized [8, 16]
    | 'S' => flex "|S"
    | 'V' => flex "|V"
    | 'U' => flex (order ++ "U")
    | 'O' => if tail.isEmpty || tail == ['4'] || tail == ['8'] then some "|O" else none
    | 'M' | 'm' =>
      let base := order ++ String.singleton k ++ "8"
      match tail with
      | [] => some base
      | ['8'] => some base
      | '8' :: '[' :: r =>
        match r.reverse with
        | ']' :: u => (unitText (String.ofList u.reverse)).map (base ++ ·)
        | _ => none
      | _ => none
    | _ => none

/-- `read_magic` and `_check_version`, `lib/_format_impl.py:230` and `199`, on the start of a file: the major version, or an error. A short file is `eofLen`, a wrong prefix is `syntax`, and a version other than 1.0, 2.0 and 3.0 is `version`. -/
def openMagic (data : List Nat) : Except ReadError Nat :=
  if data.length < magicLen then .error .eofLen
  else if data.take 6 != [0x93, 0x4e, 0x55, 0x4d, 0x50, 0x59] then .error .syntax
  else
    match data[6]?, data[7]? with
    | some maj, some mnr => if mnr == 0 && (maj == 1 || maj == 2 || maj == 3) then .ok maj else .error .version
    | _, _ => .error .eofLen

/-- Whether `sorted` of the keys raises `TypeError`: two distinct keys of kinds that Python cannot order. Strings order with strings, numbers with numbers, and nothing else is modelled. -/
def sortFails (ks : List Val) : Bool :=
  let group (k : Val) : Nat :=
    if k.kind == .str then 1 else if k.kind == .int || k.kind == .flt || k.kind == .bool then 2 else 0
  let repr (k : Val) : Nat × String × Int := (if k.kind == .str then 1 else 0, k.strv, k.intv)
  let distinct := ks.map repr |>.eraseDups
  let gs := ks.map group
  distinct.length ≥ 2 && (gs.contains 0 || (gs.contains 1 && gs.contains 2))

/-- The checks that follow a successful `literal_eval`, `lib/_format_impl.py:665` to `689`. -/
def checkHeader (d : Val) : Except ReadError Header :=
  if d.kind != .dict then .error .notDict
  else
    let keyStrs := d.entries.map (fun (k, _) => if k.kind == .str then some k.strv else none)
    let expected := ["descr", "fortran_order", "shape"]
    let keysOk := keyStrs.all (·.isSome) && expected.all (fun e => keyStrs.contains (some e))
      && keyStrs.all (fun k => match k with | some s => expected.contains s | none => false)
    if !keysOk then (if sortFails (d.entries.map (·.1)) then .error .keySort else .error .keys)
    else
      -- A repeated key keeps its last value.
      let look (key : String) : Option Val :=
        (d.entries.filter (fun (k, _) => k.kind == .str && k.strv == key)).getLast?.map (·.2)
      match look "shape", look "fortran_order", look "descr" with
      | some sh, some fo, some de =>
        match sh.kind, sh.ints with
        | .tuple, some ints =>
          if fo.kind != .bool then .error .fortran
          else
            match de.kind with
            | .str =>
              match dtypeStr de.strv with
              | some t => .ok { shape := ints, fortran := fo.intv != 0, dtype := t }
              | none => .error .descr
            | _ => .error .descr
        | _, _ => .error .shape
      | _, _, _ => .error .keys

/-- The three steps after the text is decoded: the `literal_eval` of the text, the retry after `_filter_header` for versions up to 2.0, and the checks. -/
def parseHeaderText (v : Version) (text : String) : Except ReadError Header :=
  let (toks, tokErr) := tokenize text
  let evalIt (val : Val) : Except ReadError Header :=
    match val.err with
    | some .malformed => .error .malformed
    | some .unhashable => .error .unhashable
    | none => checkHeader val
  match parseTokens toks with
  | some val => evalIt val
  | none =>
    if v == .v3 then .error .syntax
    else if tokErr then .error .tokenError
    else
      match parseTokens (filterL false toks) with
      | some val => evalIt val
      | none => .error .syntax

/-- Decode the header bytes: latin1 for 1.0 and 2.0, strict utf8 for 3.0. -/
def decodeHeader (v : Version) (bs : List Nat) : Option String :=
  if v.latin1 then some (String.ofList (bs.map Char.ofNat))
  else String.fromUTF8? (ByteArray.mk (bs.map (·.toUInt8)).toArray)

/-- Little endian value of a list of bytes. -/
def leValue (bs : List Nat) : Nat := bs.foldr (fun b acc => b + 256 * acc) 0

/--
`_read_array_header`, `lib/_format_impl.py:621`, on the bytes that follow the magic string. `ver` is the version tuple's first entry, and the minor version is always 0.
-/
def readHeader (ver : Nat) (data : List Nat) : Except ReadError Header :=
  let v? : Option Version := match ver with | 1 => some .v1 | 2 => some .v2 | 3 => some .v3 | _ => none
  match v? with
  | none => .error .version
  | some v =>
    let nb := v.sizeBytes
    if data.length < nb then .error .eofLen
    else
      let hlength := leValue (data.take nb)
      let body := data.drop nb
      if body.length < hlength then .error .eofHeader
      else
        match decodeHeader v (body.take hlength) with
        | none => .error .decode
        | some text =>
          if text.length > maxHeaderSize then .error .tooLarge
          else parseHeaderText v text

/-!
## What `read_array` does with the shape

`read_array`, `lib/_format_impl.py:781`, turns the shape of the header into an element count with `numpy.multiply.reduce(shape, dtype=numpy.int64)` (line 827), allocates `numpy.ndarray(count, dtype=dtype)` (line 862) and finally reshapes to the shape (lines 884 and 887). The model covers the part that does not depend on the data: a descriptor of itemsize zero such as `|V0`, for which nothing is read and the checks on the count and the reshape are all that is left.
-/

inductive ReadArrayErr where
  /-- `ValueError: negative dimensions are not allowed`, from `numpy.ndarray(count)`. -/
  | negative
  /-- `OverflowError: Python int too large to convert to C long`. -/
  | overflow
  /-- `ValueError: Maximum allowed dimension exceeded`, from converting a dimension above `2**63 - 1` in `reshape`. -/
  | maxDim
  /-- `ValueError: can only specify one unknown dimension`. -/
  | multiple
  /-- `ValueError: cannot reshape array of size N into shape S`. -/
  | mismatch
  /-- The shape mixes entries above `2**63 - 1` with smaller ones, so NumPy builds a float64 array in `multiply.reduce`. The result then depends on the float to integer cast of the platform and is not modelled. -/
  | floatPath
  deriving DecidableEq, Repr

/-- Whether `numpy.array(shape)` has dtype `uint64`, `float64` or an object array, for entries outside `int64`. -/
def shapeCount (shape : List Int) : Except ReadArrayErr Int :=
  if shape.isEmpty then .ok 1
  else if shape.any (fun d => d < intpMin || d > 18446744073709551615) then .error .overflow
  else if shape.any (· > intpMax) && !shape.all (· > intpMax) then .error .floatPath
  else
    -- The product is taken in `int64` (or `uint64` and then cast), so it wraps. This is the same as `wrap64` of the exact product.
    .ok (wrap64 (shape.foldl (· * ·) 1))

/-- `read_array` for an itemsize zero dtype. The result is the shape of the array that comes back. -/
def readArrayShape (shape : List Int) (fortran : Bool) : Except ReadArrayErr (List Int) := do
  let count ← shapeCount shape
  if count < 0 then throw .negative
  let dims := if fortran then shape.reverse else shape
  if dims.any (· > intpMax) then throw .maxDim
  match Shape.fixUnknownDimension dims count with
  | .error .multipleUnknown => throw .multiple
  | .error .sizeMismatch => throw .mismatch
  | .ok r => pure (if fortran then r.reverse else r)

/-!
## `np.frombuffer`

`PyArray_FromBuffer`, `_core/src/multiarray/ctors.c:3714`, with the arguments of `array_frombuffer`, `_core/src/multiarray/multiarraymodule.c:2485`.
-/

inductive FromBufferErr where
  /-- `count` or `offset` does not fit a `Py_ssize_t`: `OverflowError`, from the argument parser. -/
  | overflow
  /-- `cannot create an OBJECT array from memory buffer`, ctors.c:3727. -/
  | object
  /-- `itemsize cannot be zero in type`, ctors.c:3733. -/
  | unsized
  /-- `offset must be non-negative and no greater than buffer length`, ctors.c:3777. -/
  | offset
  /-- `cannot determine count if itemsize is 0`, ctors.c:3793. Unreachable, because an unsized type is rejected first. -/
  | countUnknown
  /-- `buffer size must be a multiple of element size`, ctors.c:3800. -/
  | multiple
  /-- `buffer is smaller than requested size`, ctors.c:3811. -/
  | small
  /-- `array is too big`, from the array constructor. -/
  | tooBig
  deriving DecidableEq, Repr

/-- The item size of a dtype code of the tests, or `none` for the object dtype. `S0`, `U0` and `V0` give size zero. -/
def itemsizeOf (code : String) : Option Nat :=
  match code.toList with
  | 'O' :: _ => none
  | 'b' :: _ => some 1
  | 'M' :: _ => some 8
  | 'm' :: _ => some 8
  | 'U' :: ds => some (4 * (digitsToInt ds).toNat)
  | _ :: ds => some (digitsToInt ds).toNat
  | [] => some 0

/--
`frombuffer(buf, dtype, count, offset)` for a buffer of `len` bytes. The result is the length of the 1-d array. The multiplication `n*itemsize` at ctors.c:3809 is a signed C product and is modelled with `wrap64`, which is what GCC and Clang do on arm64 and x86-64, although the C standard calls it undefined.
-/
def frombuffer (len : Nat) (code : String) (count offset : Int) : Except FromBufferErr Int :=
  if count < intpMin || count > intpMax || offset < intpMin || offset > intpMax then .error .overflow
  else
    match itemsizeOf code with
    | none => .error .object
    | some 0 => .error .unsized
    | some itemsize =>
      if offset < 0 || offset > (len : Int) then .error .offset
      else
        let s : Int := (len : Int) - offset
        let isz : Int := itemsize
        if count < 0 then
          if Int.tmod s isz != 0 then .error .multiple else .ok (Int.tdiv s isz)
        else
          if s < wrap64 (count * isz) then .error .small
          else
            -- The array constructor then checks the size without wrapping, `ctors.c:725` to `757`.
            if Shape.newArraySizeFits [count] isz == some true then .ok count else .error .tooBig

/-!
## Integer fields of `np.loadtxt`

`str_to_int64` and `str_to_uint64`, `_core/src/multiarray/textreading/str_to_int.h:20` and `:98`, which `npy_to_int8` to `npy_to_uint64` call with the limits of the type (`str_to_int.c:13`).
-/

/-- `Py_UNICODE_ISSPACE`: the Unicode white space characters, which include U+001C to U+001F. -/
def isSpaceU (c : Char) : Bool :=
  let n := c.toNat
  (9 ≤ n && n ≤ 13) || (0x1c ≤ n && n ≤ 0x20) || n == 0x85 || n == 0xa0 || n == 0x1680
    || (0x2000 ≤ n && n ≤ 0x200a) || n == 0x2028 || n == 0x2029 || n == 0x202f || n == 0x205f || n == 0x3000

/-- Digits are those of C `isdigit`, ASCII only. -/
def isAsciiDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/--
The digit loop shared by the two C functions. For a negative number the digits accumulate downwards and the limit is `lim = -min`, so that `number` stays inside `[min, 0]`. Here the accumulation is on the magnitude, which gives the same accept set as the C tests `number > pre_min`, `d - '0' <= dig_pre_min` and their positive twins.
-/
def accumDigits (limit : Nat) : Nat → List Char → Option (Nat × List Char)
  | acc, [] => some (acc, [])
  | acc, c :: rest =>
    if isAsciiDigit c then
      let d := c.toNat - 48
      let next := acc * 10 + d
      if next ≤ limit then accumDigits limit next rest else none
    else some (acc, c :: rest)

/-- `str_to_int64` with the limits `intMin ≤ x ≤ intMax` (a signed type) or `str_to_uint64` (`signed = false`, `intMin = 0`). Returns the value, or `none` for the return value -1. -/
def loadtxtInt (signed : Bool) (intMin : Int) (intMax : Nat) (s : List Char) : Option Int :=
  let p0 := s.dropWhile isSpaceU
  let (neg, p1) : Bool × List Char :=
    match p0 with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | _ => (false, p0)
  if !signed && neg then none
  else
    match p1 with
    | c :: _ =>
      if !isAsciiDigit c then none
      else
        match accumDigits (if neg then intMin.natAbs else intMax) 0 p1 with
        | none => none
        | some (m, rest) =>
          if (rest.dropWhile isSpaceU).isEmpty then some (if neg then -(m : Int) else m) else none
    | [] => none

/-- The conversion for a dtype code `i1` to `i8` or `u1` to `u8`. -/
def loadtxtIntTyped (code : String) (s : List Char) : Option Int :=
  match code.toList with
  | k :: ds =>
    let bytes := (digitsToInt ds).toNat
    let bits := 8 * bytes
    if k == 'i' then loadtxtInt true (-(2 : Int) ^ (bits - 1)) (2 ^ (bits - 1) - 1) s
    else loadtxtInt false 0 (2 ^ bits - 1) s
  | [] => none

/-! ## PEP 3118 buffer format strings

The writing side is `_buffer_format_string`, `_core/src/multiarray/buffer.c:191`. The reading side is `_dtype_from_pep3118`, `_core/_internal.py:627`, preceded by the C fast path `_descriptor_from_pep3118_format_fast`, `_core/src/multiarray/buffer.c:1002`, and followed by the item size check of `_array_from_buffer_3118`, `_core/src/multiarray/ctors.c:1247`. All of it is what `memoryview(np.zeros(n, dtype)).format` and `np.array(memoryview(...))` run.

The model assumes the platform of the reference runs: little-endian, `long` of 8 bytes, `long double` of 8 bytes (macOS arm64, where `long double` is `double` but still its own NumPy type) and a freshly allocated array whose data pointer is aligned to 16 bytes. The alignments in `codeAlign` come from `np.dtype(...).alignment` on that platform.
-/
namespace Pep3118

/-- A dtype as the buffer code sees it. `scalar order code size` has the byte order character of `descr->byteorder` (`=`, `<`, `>` or `|`), the NumPy type character and the item size in bytes. A subarray keeps its base, and a structured dtype keeps its item size and its fields with their offsets. Subarrays can be nested, because `np.dtype((np.dtype(('i4', (3,))), (2,)))` does not merge the shapes. -/
inductive D where
  | scalar (order : Char) (code : Char) (size : Nat)
  | sub (shape : List Nat) (base : D)
  | struct (itemsize : Nat) (fields : List (String × Nat × D))
  deriving BEq, Repr

def prod (l : List Nat) : Nat := l.foldl (· * ·) 1

/-- Item size in bytes of a fixed size type character. -/
def codeSize : Char → Nat
  | '?' | 'b' | 'B' => 1
  | 'h' | 'H' | 'e' => 2
  | 'i' | 'I' | 'f' => 4
  | 'l' | 'L' | 'q' | 'Q' | 'd' | 'g' | 'F' | 'M' | 'm' | 'O' => 8
  | 'D' | 'G' => 16
  | _ => 0

/-- `descr->alignment` on arm64: `F` aligns like `float`, `G` like a pointer, `U` like `int`. -/
def codeAlign : Char → Nat
  | '?' | 'b' | 'B' | 'S' | 'V' => 1
  | 'h' | 'H' | 'e' => 2
  | 'i' | 'I' | 'f' | 'F' | 'U' => 4
  | _ => 8

/-- `dtype.kind`. -/
def codeKind : Char → Char
  | '?' => 'b'
  | 'b' | 'h' | 'i' | 'l' | 'q' => 'i'
  | 'B' | 'H' | 'I' | 'L' | 'Q' => 'u'
  | 'e' | 'f' | 'd' | 'g' => 'f'
  | 'F' | 'D' | 'G' => 'c'
  | c => c

/-- `dtype.byteorder` as NumPy normalises it: one byte types, bool, bytes, void and object are `|`, and `<` is `=` on a little-endian host. -/
def canonOrder (order code : Char) (size : Nat) : Char :=
  let k := codeKind code
  if k == 'b' || k == 'S' || k == 'V' || k == 'O' || size == 1 then '|'
  else if order == '<' || order == '|' then '=' else order

/-- The scalar with the item size of its type character, or `n` characters for `S`, `U` and `V`. -/
def mkScalar (order code : Char) (n : Nat) : D :=
  .scalar order code (if code == 'S' || code == 'V' then n else if code == 'U' then 4 * n else codeSize code)

def D.size : D → Nat
  | .scalar _ _ s => s
  | .sub sh b => prod sh * b.size
  | .struct n _ => n

def hexc (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'

def hexName (s : String) : String :=
  String.ofList (s.toUTF8.toList.flatMap fun b => [hexc (b.toNat / 16), hexc (b.toNat % 16)])

/-- A canonical text for a dtype, equal to the text the Python side builds from `dtype.kind`, `dtype.byteorder`, `dtype.itemsize`, `dtype.subdtype` and `dtype.fields`. -/
def canon : D → String
  | .scalar o c s => String.ofList [canonOrder o c s, codeKind c] ++ toString s
  | .sub sh b => "A" ++ "x".intercalate (sh.map toString) ++ "(" ++ canon b ++ ")"
  | .struct n fs => "T" ++ toString n ++ "{" ++ ";".intercalate (canonFields fs) ++ "}"
where
  canonFields : List (String × Nat × D) → List String
    | [] => []
    | (nm, off, d) :: r => (hexName nm ++ "@" ++ toString off ++ "@" ++ canon d) :: canonFields r

/-! ### Writing the format string -/

inductive FErr where
  /-- `ValueError: cannot include dtype 'M' in a buffer`, the `default` of the switch at `buffer.c:421`. -/
  | notInBuffer
  /-- `ValueError: cannot expose native-only dtype 'g' in non-native byte order '>' via buffer interface`, `buffer.c:359`. -/
  | nativeOnly
  /-- `ValueError: dtypes with overlapping or out-of-order fields are not representable as buffers`, `buffer.c:285`. -/
  | overlap
  /-- `ValueError: ':' is not an allowed character in buffer field names`, `buffer.c:116`. -/
  | colon
  deriving DecidableEq, Repr

/-- The running state of `_buffer_format_string`: the text so far, `*offset` and `*active_byteorder`. -/
structure FS where
  out : String
  off : Nat
  active : Char

/-- `_is_natively_aligned_at`, `buffer.c:141`. The array is one dimensional of length `n` with item size `stride`. For the descriptor of the array itself (`top`) only the array flag is read, and a fresh array is aligned. For others the code checks the data pointer (assumed aligned), the offset, the item size of the leaf and the stride when the length is above one. It never looks at the item size of the enclosing structure. -/
def isNativelyAligned (top : Bool) (n stride : Nat) (c : Char) (size off : Nat) : Bool :=
  if top then true
  else
    let a := codeAlign c
    off % a == 0 && size % a == 0 && (n ≤ 1 || stride % a == 0)

/-- The switch of `buffer.c:367`. `std` is `is_standard_size`, which only picks `q` over `l`. -/
def typeStr (c : Char) (std : Bool) (size : Nat) : Option String :=
  match c with
  | '?' => some "?" | 'b' => some "b" | 'B' => some "B" | 'h' => some "h" | 'H' => some "H"
  | 'i' => some "i" | 'I' => some "I"
  | 'l' => some (if std then "q" else "l")
  | 'L' => some (if std then "Q" else "L")
  | 'q' => some "q" | 'Q' => some "Q" | 'e' => some "e" | 'f' => some "f" | 'd' => some "d" | 'g' => some "g"
  | 'F' => some "Zf" | 'D' => some "Zd" | 'G' => some "Zg"
  | 'O' => some "O"
  | 'S' => some (toString size ++ "s")
  | 'U' => some (toString (size / 4) ++ "w")
  | 'V' => some (toString size ++ "x")
  | _ => none

/-- The leaf branch, `buffer.c:312` to `buffer.c:434`. -/
def scalarFormat (top : Bool) (n stride : Nat) (st : FS) (order c : Char) (size : Nat) : Except FErr FS :=
  let nativeOnly := c == 'g' || c == 'G'
  let aligned := isNativelyAligned top n stride c size st.off
  let r : Except FErr (Bool × String × Char) :=
    if order == '=' && aligned then
      .ok (false, if st.active != '@' then "@" else "", '@')
    else if order == '=' && nativeOnly then
      .ok (false, if st.active != '^' then "^" else "", '^')
    else if order == '<' || order == '>' || order == '=' then
      if nativeOnly then .error .nativeOnly
      else .ok (true, if st.active != order then order.toString else "", order)
    else .ok (true, "", st.active)
  match r with
  | .error e => .error e
  | .ok (std, pre, act) =>
    match typeStr c std size with
    | none => .error .notInBuffer
    | some t => .ok { out := st.out ++ pre ++ t, off := st.off + size, active := act }

/-- `_buffer_format_string`, `buffer.c:191`. -/
def fmtD (top : Bool) (n stride : Nat) : D → FS → Except FErr FS
  | .sub sh b, st =>
    let old := st.off
    match fmtD false n stride b { st with out := st.out ++ "(" ++ ",".intercalate (sh.map toString) ++ ")" } with
    | .error e => .error e
    | .ok st' => .ok { st' with off := old + (st'.off - old) * prod sh }
  | .struct _ fs, st =>
    match fmtFields n stride st.off fs { st with out := st.out ++ "T{" } with
    | .error e => .error e
    | .ok st' => .ok { st' with out := st'.out ++ "}" }
  | .scalar o c s, st => scalarFormat top n stride st o c s
where
  fmtFields (n stride base : Nat) : List (String × Nat × D) → FS → Except FErr FS
    | [], st => .ok st
    | (nm, foff, d) :: rest, st =>
      let newOff := foff + base
      if st.off > newOff then .error .overlap
      else
        let st1 := { st with out := st.out ++ String.ofList (List.replicate (newOff - st.off) 'x'), off := newOff }
        match fmtD false n stride d st1 with
        | .error e => .error e
        | .ok st2 =>
          if nm.toList.contains ':' then .error .colon
          else fmtFields n stride base rest { st2 with out := st2.out ++ ":" ++ nm ++ ":" }

/-- The format string of `memoryview(np.zeros(n, dtype))`, `_buffer_info_new`, `buffer.c:463`. -/
def bufferFormat (n : Nat) (d : D) : Except FErr String :=
  match fmtD true n d.size d { out := "", off := 0, active := '@' } with
  | .ok st => .ok st.out
  | .error e => .error e

/-! ### Reading it back -/

/-- The exception types of `_dtype_from_pep3118` that the tests tell apart. -/
inductive PErr where
  /-- `ValueError`: unknown specifier, a missing closing bracket or colon, a bad integer or a bad shape. -/
  | value
  /-- `NotImplementedError` for `u`, `&`, `t` and `X`. -/
  | notImpl
  /-- `RuntimeError` for a duplicate field name. -/
  | runtime
  /-- `IndexError` from `stream.next` on an empty stream. -/
  | index
  /-- `KeyError` for `Z` followed by a character that makes no complex type. -/
  | key
  deriving DecidableEq, Repr

/-- The stream: the rest of the string and `stream.byteorder`. -/
structure PS where
  s : List Char
  bo : Char

/-- The lists of `field_spec`, with `offset` and `common_alignment`. -/
structure Acc where
  names : List (Option String)
  formats : List D
  offsets : List Nat
  itemsize : Nat
  offset : Nat
  common : Nat

def Acc.init : Acc := { names := [], formats := [], offsets := [], itemsize := 0, offset := 0, common := 1 }

/-- `Stream.consume_until(c)` for a character: the text before it and the rest after it, or `none` for the `ValueError` of `str.index`. -/
def splitAtChar (c : Char) : List Char → Option (List Char × List Char)
  | [] => none
  | x :: r => if x == c then some ([], r) else (splitAtChar c r).map fun (a, b) => (x :: a, b)

def digitsNat (l : List Char) : Nat := l.foldl (fun a c => a * 10 + (c.toNat - 48)) 0

/-- `int(text)` for ASCII text: an optional sign and at least one digit. -/
def pyInt (l : List Char) : Option Int :=
  let ds (r : List Char) : Option Nat := if !r.isEmpty && r.all Char.isDigit then some (digitsNat r) else none
  match l with
  | '-' :: r => (ds r).map fun n => -(n : Int)
  | '+' :: r => (ds r).map fun n => (n : Int)
  | _ => (ds l).map fun n => (n : Int)

/-- `str.split(',')` on characters. -/
def splitComma : List Char → List (List Char)
  | [] => [[]]
  | c :: r =>
    match splitComma r with
    | [] => [[c]]
    | h :: rest => if c == ',' then [] :: h :: rest else (c :: h) :: rest

/-- `tuple(map(int, shape.split(',')))`. -/
def parseShape (l : List Char) : Option (List Int) :=
  (splitComma l).mapM pyInt

/-- The characters of `type_map_chars`: `g` is only there for the native map. -/
def typeChars (native : Bool) : List Char :=
  "?cbBhHiIlLqQefdZswOx".toList ++ (if native then ['g'] else [])

/-- `_pep3118_native_map` and `_pep3118_standard_map`, `_internal.py:532` and `_internal.py:559`, as the NumPy type character of the result. The standard `l` is a 4 byte integer, so it maps to `i`. -/
def lookupType (native : Bool) (tc : String) : Option Char :=
  match tc with
  | "?" => some '?' | "c" => some 'S' | "b" => some 'b' | "B" => some 'B'
  | "h" => some 'h' | "H" => some 'H' | "i" => some 'i' | "I" => some 'I'
  | "l" => some (if native then 'l' else 'i')
  | "L" => some (if native then 'L' else 'I')
  | "q" => some 'q' | "Q" => some 'Q' | "e" => some 'e' | "f" => some 'f' | "d" => some 'd'
  | "g" => if native then some 'g' else none
  | "Zf" => some 'F' | "Zd" => some 'D'
  | "Zg" => if native then some 'G' else none
  | "s" => some 'S' | "w" => some 'U' | "O" => some 'O' | "x" => some 'V'
  | _ => none

/-- `_add_trailing_padding`, `_internal.py:794`. A structured value keeps its fields, any other value becomes the field `f0`. -/
def addTrailingPadding (v : D) (pad : Nat) : D :=
  match v with
  | .struct n fs => .struct (n + pad) fs
  | _ => .struct (v.size + pad) [("f0", 0, v)]

/-- `np.dtype((value, shape))`. A negative dimension raises `ValueError` ("dimension smaller then zero"). So does a base that is not structured and has item size zero, because `np.dtype(('V0', (2,)))` takes the tuple as the form `(type, itemsize)` and finds no valid item size ("invalid itemsize in generic type tuple"); a structured base of size zero is fine. -/
def mkSub (shape : List Int) (value : D) : Except PErr D :=
  if shape.any (· < 0) then throw PErr.value
  else match value with
    | .struct _ _ => pure (D.sub (shape.map Int.toNat) value)
    | _ => if value.size == 0 then throw PErr.value else pure (D.sub (shape.map Int.toNat) value)

/-- `_fix_names`, `_internal.py:779`. -/
def fixNames : List String → List (Option String) → List String
  | done, [] => done
  | done, none :: rest =>
    let taken := done ++ rest.filterMap id
    let j := ((List.range (taken.length + 1)).find? fun j => !taken.contains ("f" ++ toString j)).getD 0
    fixNames (done ++ ["f" ++ toString j]) rest
  | done, some n :: rest => fixNames (done ++ [n]) rest

def zipFields : List String → List Nat → List D → List (String × Nat × D)
  | n :: ns, o :: os, f :: fs => (n, o, f) :: zipFields ns os fs
  | _, _, _ => []

/-- The end of `__dtype_from_pep3118`, `_internal.py:762` to `_internal.py:777`. -/
def finishParse (ps : PS) (acc : Acc) (isSub : Bool) : D × Nat × PS :=
  let itemsize := if ps.bo == '@' then acc.itemsize + (acc.common - acc.offset % acc.common) % acc.common else acc.itemsize
  match acc.names, acc.offsets, acc.formats with
  | [none], 0 :: _, f :: _ =>
    if itemsize == f.size && !isSub then (f, acc.common, ps)
    else (.struct itemsize (zipFields (fixNames [] acc.names) acc.offsets acc.formats), acc.common, ps)
  | _, _, _ => (.struct itemsize (zipFields (fixNames [] acc.names) acc.offsets acc.formats), acc.common, ps)

/-- `__dtype_from_pep3118`, `_internal.py:632`. The fuel only bounds the recursion, because every loop turn consumes a character. -/
def parseLoop : Nat → PS → Acc → Bool → Except PErr (D × Nat × PS)
  | 0, _, _, _ => .error .value
  | f + 1, ps, acc, isSub =>
    match ps.s with
    | [] => .ok (finishParse ps acc isSub)
    | '}' :: rest => .ok (finishParse { ps with s := rest } acc isSub)
    | _ => do
      -- sub-arrays (1)
      let (shape, ps) ← (match ps.s with
        | '(' :: rest =>
          match splitAtChar ')' rest with
          | none => throw PErr.value
          | some (sh, rest') =>
            match parseShape sh with
            | none => throw PErr.value
            | some l => pure (some l, { ps with s := rest' })
        | _ => pure (none, ps))
      -- byte order
      let ps ← (match ps.s with
        | [] => throw PErr.index
        | c :: rest =>
          if c == '@' || c == '=' || c == '<' || c == '>' || c == '^' || c == '!' then
            pure { s := rest, bo := if c == '!' then '>' else c }
          else pure ps)
      let native := ps.bo == '@' || ps.bo == '^'
      -- item sizes
      let digs := ps.s.takeWhile Char.isDigit
      let ps := { ps with s := ps.s.dropWhile Char.isDigit }
      let itemsize := if digs.isEmpty then 1 else digitsNat digs
      -- data types
      let (value, align, isPadding, ps, itemsize) ← (match ps.s with
        | 'T' :: '{' :: rest => do
          let (v, a, ps') ← parseLoop f { ps with s := rest } Acc.init true
          pure (v, a, false, ps', itemsize)
        | [] => throw PErr.index
        | c :: rest =>
          if (typeChars native).contains c then
            let (tc, rest') : String × List Char :=
              if c == 'Z' then
                (match rest with
                  | [] => ("Z", [])
                  | d :: r => (String.ofList [c, d], r))
              else (c.toString, rest)
            match lookupType native tc with
            | none => throw PErr.key
            | some code =>
              let flex := tc == "s" || tc == "w" || tc == "x"
              let sz := if tc == "s" || tc == "x" then itemsize else if tc == "w" then 4 * itemsize
                else if tc == "c" then 1 else codeSize code
              let order := if native then '=' else ps.bo
              pure (D.scalar order code sz, codeAlign code, tc == "x", { ps with s := rest' }, if flex then 1 else itemsize)
          else if c == 'u' || c == '&' || c == 't' || c == 'X' then throw PErr.notImpl
          else throw PErr.value)
      -- native alignment may require padding
      let (offset, value, extra, common) :=
        if ps.bo == '@' then
          let startPad := (align - acc.offset % align) % align
          let intra := (align - value.size % align) % align
          let off := acc.offset + startPad
          let common := Nat.lcm align acc.common
          if intra != 0 then
            let bigShape := match shape with
              | some l => (l.foldl (· * ·) (1 : Int)) > 1
              | none => false
            if itemsize > 1 || bigShape then (off, addTrailingPadding value intra, 0, common)
            else (off, value, intra, common)
          else (off, value, 0, common)
        else (acc.offset, value, 0, acc.common)
      -- convert itemsize to sub-array, then sub-arrays (2)
      let value ← if itemsize != 1 then mkSub [(itemsize : Int)] value else pure value
      let value ← (match shape with
        | none => pure value
        | some l => mkSub l value)
      -- field name
      let (name, ps) ← (match ps.s with
        | ':' :: rest =>
          match splitAtChar ':' rest with
          | none => throw PErr.value
          | some (nm, r) => pure (some (String.ofList nm), { ps with s := r })
        | _ => pure (none, ps))
      let acc' ←
        if isPadding && name.isNone then
          pure { acc with offset := offset + value.size + extra, itemsize := offset + value.size + extra, common := common }
        else
          if name.isSome && acc.names.contains name then throw PErr.runtime
          else pure { names := acc.names ++ [name], formats := acc.formats ++ [value], offsets := acc.offsets ++ [offset],
                      itemsize := offset + value.size + extra, offset := offset + value.size + extra, common := common }
      parseLoop f ps acc' isSub

/-- `_dtype_from_pep3118`, `_internal.py:627`. -/
def parseFormat (spec : List Char) : Except PErr D :=
  match parseLoop (spec.length + 2) { s := spec, bo := '@' } Acc.init false with
  | .ok (d, _, _) => .ok d
  | .error e => .error e

/-- `_pep3118_letter_to_type`, `buffer.c:1077`, as a type character and an item size. -/
def fastLetter (native complex : Bool) : Char → Option (Char × Nat)
  | '?' => some ('?', 1) | 'b' => some ('b', 1) | 'B' => some ('B', 1)
  | 'h' => some ('h', 2) | 'H' => some ('H', 2)
  | 'i' => some ('i', 4) | 'I' => some ('I', 4)
  | 'l' => some (if native then ('l', 8) else ('i', 4))
  | 'L' => some (if native then ('L', 8) else ('I', 4))
  | 'q' => some ('q', 8) | 'Q' => some ('Q', 8)
  | 'n' => if native then some ('l', 8) else none
  | 'N' => if native then some ('L', 8) else none
  | 'e' => some ('e', 2)
  | 'f' => some (if complex then ('F', 8) else ('f', 4))
  | 'd' => some (if complex then ('D', 16) else ('d', 8))
  | 'g' => if native then some (if complex then ('G', 16) else ('g', 8)) else none
  | _ => none

/-- `_descriptor_from_pep3118_format_fast`, `buffer.c:1002`: one item, with byte order characters in front of it or behind it. -/
def fastLoop (order : Char) (std : Bool) (seen : Option (Char × Nat)) : List Char → Option D
  | [] => seen.map fun (c, s) => .scalar order c s
  | '@' :: r => fastLoop '=' false seen r
  | '^' :: r => fastLoop '=' false seen r
  | '<' :: r => fastLoop '<' true seen r
  | '>' :: r => fastLoop '>' true seen r
  | '!' :: r => fastLoop '>' true seen r
  | '=' :: r => fastLoop '=' true seen r
  | 'Z' :: r =>
    match r with
    | [] => none
    | c :: r' =>
      if seen.isSome then none
      else match fastLetter (!std) true c with
        | none => none
        | some t => fastLoop order std (some t) r'
  | c :: r =>
    if seen.isSome then none
    else match fastLetter (!std) false c with
      | none => none
      | some t => fastLoop order std (some t) r

/-- `NumPyOS_ascii_isspace`. -/
def isSpaceC (c : Char) : Bool := c == ' ' || (9 ≤ c.toNat && c.toNat ≤ 13)

/-- Whitespace is stripped except inside `:name:`, `buffer.c:936`. -/
def stripWs : Bool → List Char → List Char
  | _, [] => []
  | inName, c :: r =>
    if c == ':' then c :: stripWs (!inName) r
    else if inName || !isSpaceC c then c :: stripWs inName r
    else stripWs inName r

inductive RErr where
  | format (e : FErr)
  /-- `ValueError: '...' is not a valid PEP 3118 buffer format string`, wrapping any error of the parser. -/
  | parse
  /-- `RuntimeError: Item size ... for PEP 3118 buffer format string ... does not match the dtype ... item size`, `ctors.c:1262`. -/
  | itemsize
  deriving DecidableEq, Repr

/-- `_descriptor_from_pep3118_format`, `buffer.c:917`: the fast path, and when it gives up, the whitespace stripping and the Python parser. -/
def parseBuffer (f : String) : Except RErr D :=
  match fastLoop '=' false none f.toList with
  | some x => .ok x
  | none =>
    match parseFormat (stripWs false f.toList) with
    | .ok x => .ok x
    | .error _ => .error .parse

/-- The dtype of `np.array(memoryview(np.zeros(n, dtype)))`: the format string of the writer, `parseBuffer`, and then the check of `_array_from_buffer_3118`. -/
def roundTrip (n : Nat) (d : D) : Except RErr D :=
  match bufferFormat n d with
  | .error e => .error (.format e)
  | .ok f =>
    match parseBuffer f with
    | .ok x => if x.size == d.size then .ok x else .error .itemsize
    | .error e => .error e

end Pep3118

end NumpyLean.NpyFormat
