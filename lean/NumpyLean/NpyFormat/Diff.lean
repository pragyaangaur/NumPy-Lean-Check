import NumpyLean.NpyFormat.Model
import NumpyLean.Common.Wire

namespace NumpyLean.NpyFormat
open NumpyLean.Wire

/-- The value of one hexadecimal digit. -/
def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else none

/-- Decode a hexadecimal string into bytes. `_` stands for the empty string. -/
def hexToBytes (s : String) : List Nat :=
  if s == "_" then [] else
  let rec go : List Char → List Nat
    | a :: b :: rest => (match hexVal a, hexVal b with
        | some x, some y => (x * 16 + y) :: go rest
        | _, _ => 0 :: go rest)
    | _ => []
  go s.toList

def hexDigit (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'

def bytesToHex (bs : List Nat) : String :=
  if bs.isEmpty then "_" else
  String.ofList (bs.flatMap (fun b => [hexDigit (b / 16), hexDigit (b % 16)]))

/-- The utf8 bytes of a string. -/
def utf8Bytes (s : String) : List Nat := s.toUTF8.toList.map (·.toNat)

/-- Decode utf8 bytes as the tests send text over the wire. Invalid input gives the empty string, and the tests never send any. -/
def textOfHex (s : String) : String :=
  if s == "_" then "" else
  match String.fromUTF8? (ByteArray.mk ((hexToBytes s).map (·.toUInt8)).toArray) with
  | some t => t
  | none => ""

def parseVersion? (s : String) : Option (Option Version) :=
  match s with
  | "auto" => some none
  | "1" => some (some .v1)
  | "2" => some (some .v2)
  | "3" => some (some .v3)
  | _ => none

def fmtWrapError : WrapError → String
  | .unicode => "ERR unicode"
  | .tooBig => "ERR toobig"

/-- The bytes of a header body in the encoding of its version. -/
def encodeBody (v : Version) (s : String) : List Nat :=
  if v.latin1 then s.toList.map (·.toNat) else utf8Bytes s

/--
`npy_wrap <ver|auto> <hex of header text> <fill>` runs `_wrap_header` or `_wrap_header_guess_version` on the header text followed by `fill` spaces. It prints `OK <major> <minor> <length field> <total bytes> <padding spaces>` or `ERR unicode` or `ERR toobig`.
-/
def diffWrap : Handler
  | [ver, hdr, fill] =>
    match parseVersion? ver with
    | none => "BADARGS"
    | some v =>
      let h := textOfHex hdr ++ String.ofList (List.replicate (parseInt fill).toNat ' ')
      let r := match v with | none => wrapGuess h | some v => wrapHeader v h
      match r with
      | .ok w => s!"OK {w.version.major} 0 {w.hfield} {w.total} {w.padlen}"
      | .error e => fmtWrapError e
  | _ => "BADARGS"

/--
`npy_write <ver|auto> <fortran 0|1> <shape> <hex of descr>` runs `_write_array_header` on the dictionary with that descriptor string. It prints `OK <major> <minor> <length field> <total bytes> <hex of the header text without padding>` or an error.
-/
def diffWrite : Handler
  | [ver, f, shape, descr] =>
    match parseVersion? ver with
    | none => "BADARGS"
    | some v =>
      let fortran := f == "1"
      let d := textOfHex descr
      let sh := parseInts shape
      match writeHeader v d fortran sh with
      | .ok w => s!"OK {w.version.major} 0 {w.hfield} {w.total} {bytesToHex (encodeBody w.version (headerBase d fortran sh))}"
      | .error e => fmtWrapError e
  | _ => "BADARGS"

def fmtReadError : ReadError → String
  | .eofLen => "ERR eoflen"
  | .eofHeader => "ERR eofheader"
  | .tooLarge => "ERR toolarge"
  | .syntax => "ERR syntax"
  | .tokenError => "ERR tokenerror"
  | .malformed => "ERR malformed"
  | .unhashable => "ERR unhashable"
  | .notDict => "ERR notdict"
  | .keys => "ERR keys"
  | .keySort => "ERR keysort"
  | .shape => "ERR shape"
  | .fortran => "ERR fortran"
  | .descr => "ERR descr"
  | .version => "ERR version"
  | .decode => "ERR decode"

/--
`npy_read <version> <hex of bytes>` runs `_read_array_header` on a `BytesIO` that holds the bytes after the magic string. It prints `OK <shape> <True|False> <dtype.str>` or `ERR <kind>`.
-/
def diffRead : Handler
  | [ver, hex] =>
    match readHeader (parseInt ver).toNat (hexToBytes hex) with
    | .ok h => s!"OK {fmtInts h.shape} {fmtBool h.fortran} {h.dtype}"
    | .error e => fmtReadError e
  | _ => "BADARGS"

/-- `npy_open <hex of bytes>` runs `read_magic` and `_check_version` and prints `OK <major>` or `ERR <kind>`. -/
def diffOpen : Handler
  | [hex] =>
    match openMagic (hexToBytes hex) with
    | .ok m => s!"OK {m}"
    | .error e => fmtReadError e
  | _ => "BADARGS"

/-- `npy_array <fortran 0|1> <shape>` runs `read_array` on a file whose header declares that shape and the descriptor `|V0`. It prints `OK <shape>` or `ERR neg`, `ERR overflow`, `ERR maxdim`, `ERR multiple`, `ERR mismatch`, `ERR float`. -/
def diffArray : Handler
  | [f, shape] =>
    match readArrayShape (parseInts shape) (f == "1") with
    | .ok r => s!"OK {fmtInts r}"
    | .error .negative => "ERR neg"
    | .error .overflow => "ERR overflow"
    | .error .maxDim => "ERR maxdim"
    | .error .multiple => "ERR multiple"
    | .error .mismatch => "ERR mismatch"
    | .error .floatPath => "ERR float"
  | _ => "BADARGS"

/-- `frombuffer <buffer length> <dtype code> <count> <offset>` prints `OK <n>` or `ERR overflow|object|unsized|offset|multiple|small|toobig`. -/
def diffFromBuffer : Handler
  | [len, code, count, offset] =>
    match frombuffer (parseInt len).toNat code (parseInt count) (parseInt offset) with
    | .ok n => s!"OK {n}"
    | .error .overflow => "ERR overflow"
    | .error .object => "ERR object"
    | .error .unsized => "ERR unsized"
    | .error .offset => "ERR offset"
    | .error .countUnknown => "ERR countunknown"
    | .error .multiple => "ERR multiple"
    | .error .small => "ERR small"
    | .error .tooBig => "ERR toobig"
  | _ => "BADARGS"

/-- `loadtxt_int <code> <hex of utf8 text>` prints `OK <value>` or `ERR`. -/
def diffLoadtxtInt : Handler
  | [code, hex] =>
    match loadtxtIntTyped code (textOfHex hex).toList with
    | some v => s!"OK {v}"
    | none => "ERR"
  | _ => "BADARGS"

/-! ### PEP 3118 -/

open Pep3118 in
/-- The dtypes of the PEP 3118 tests. A scalar is its byte order character, its NumPy type character and, for `S`, `U` and `V`, its length in characters (`=i`, `>f`, `|S3`, `=U2`, `|V4`). A subarray is `A<dim>x<dim>(<base>)`. A structured dtype is `T<item size>{<hex name>@<offset>@<dtype>;...}`. -/
def wireD : Nat → List Char → Option (D × List Char)
  | 0, _ => none
  | f + 1, 'A' :: cs => do
    let (dims, cs) ← wireDims (cs.length + 1) cs
    match cs with
    | '(' :: cs => do
      let (b, cs) ← wireD f cs
      match cs with
      | ')' :: cs => some (D.sub dims b, cs)
      | _ => none
    | _ => none
  | f + 1, 'T' :: cs => do
    let n := cs.takeWhile Char.isDigit
    match cs.dropWhile Char.isDigit with
    | '{' :: cs => do
      let (fs, cs) ← wireFields f cs
      some (D.struct (digitsNat n) fs, cs)
    | _ => none
  | _ + 1, o :: c :: cs =>
    if c == 'S' || c == 'U' || c == 'V' then
      some (mkScalar o c (digitsNat (cs.takeWhile Char.isDigit)), cs.dropWhile Char.isDigit)
    else some (mkScalar o c 0, cs)
  | _ + 1, _ => none
where
  wireDims : Nat → List Char → Option (List Nat × List Char)
    | 0, _ => none
    | k + 1, cs =>
      let n := cs.takeWhile Char.isDigit
      if n.isEmpty then none
      else match cs.dropWhile Char.isDigit with
        | 'x' :: r => (wireDims k r).map fun (l, r') => (digitsNat n :: l, r')
        | r => some ([digitsNat n], r)
  wireFields : Nat → List Char → Option (List (String × Nat × D) × List Char)
    | 0, _ => none
    | _ + 1, '}' :: cs => some ([], cs)
    | f + 1, cs => do
      let hexs := cs.takeWhile (· != '@')
      match cs.dropWhile (· != '@') with
      | '@' :: r =>
        let off := r.takeWhile Char.isDigit
        match r.dropWhile Char.isDigit with
        | '@' :: r' => do
          let (d, r'') ← wireD f r'
          match r'' with
          | ';' :: r3 => do
            let (rest, r4) ← wireFields f r3
            some ((textOfHex (String.ofList hexs), digitsNat off, d) :: rest, r4)
          | '}' :: r3 => some ([(textOfHex (String.ofList hexs), digitsNat off, d)], r3)
          | _ => none
        | _ => none
      | _ => none

open Pep3118 in
def parseWireD (s : String) : Option D :=
  match wireD (s.length + 1) s.toList with
  | some (d, []) => some d
  | _ => none

def fmtFErr : Pep3118.FErr → String
  | .notInBuffer => "ERR notinbuffer"
  | .nativeOnly => "ERR nativeonly"
  | .overlap => "ERR overlap"
  | .colon => "ERR colon"

def fmtPErr : Pep3118.PErr → String
  | .value => "ERR value"
  | .notImpl => "ERR notimpl"
  | .runtime => "ERR runtime"
  | .index => "ERR index"
  | .key => "ERR key"

/-- `pep3118_format <n> <dtype>` prints `OK <hex of the format string>` for `memoryview(np.zeros(n, dtype)).format` or `ERR notinbuffer|nativeonly|overlap|colon`. -/
def diffPep3118Format : Handler
  | [n, w] =>
    match parseWireD w with
    | none => "BADARGS"
    | some d =>
      match Pep3118.bufferFormat (parseInt n).toNat d with
      | .ok f => "OK " ++ bytesToHex (utf8Bytes f)
      | .error e => fmtFErr e
  | _ => "BADARGS"

/-- `pep3118_roundtrip <n> <dtype>` prints `OK <canonical dtype>` for `np.array(memoryview(np.zeros(n, dtype))).dtype` or `ERR parse|itemsize` or one of the errors of `pep3118_format`. -/
def diffPep3118Roundtrip : Handler
  | [n, w] =>
    match parseWireD w with
    | none => "BADARGS"
    | some d =>
      match Pep3118.roundTrip (parseInt n).toNat d with
      | .ok r => "OK " ++ Pep3118.canon r
      | .error (.format e) => fmtFErr e
      | .error .parse => "ERR parse"
      | .error .itemsize => "ERR itemsize"
  | _ => "BADARGS"

/-- `pep3118_parse <hex of the format string>` prints `OK <canonical dtype>` or `ERR value|notimpl|runtime|index|key` for `_dtype_from_pep3118`. -/
def diffPep3118Parse : Handler
  | [hex] =>
    match Pep3118.parseFormat (textOfHex hex).toList with
    | .ok d => "OK " ++ Pep3118.canon d
    | .error e => fmtPErr e
  | _ => "BADARGS"

def handlers : List (String × Handler) :=
  [("loadtxt_int", diffLoadtxtInt), ("frombuffer", diffFromBuffer), ("npy_array", diffArray), ("npy_wrap", diffWrap), ("npy_write", diffWrite), ("npy_read", diffRead), ("npy_open", diffOpen),
   ("pep3118_format", diffPep3118Format), ("pep3118_roundtrip", diffPep3118Roundtrip), ("pep3118_parse", diffPep3118Parse)]

end NumpyLean.NpyFormat
