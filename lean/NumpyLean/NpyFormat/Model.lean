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

`read_array`, `lib/_format_impl.py:781`, turns the shape of the header into an element count with `numpy.multiply.reduce(shape, dtype=numpy.int64)` (line 837), allocates `numpy.ndarray(count, dtype=dtype)` (line 866) and finally reshapes to the shape (lines 893 and 894). The model covers the part that does not depend on the data: a descriptor of itemsize zero such as `|V0`, for which nothing is read and the checks on the count and the reshape are all that is left.
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

end NumpyLean.NpyFormat
