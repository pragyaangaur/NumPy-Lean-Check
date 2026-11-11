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

def handlers : List (String × Handler) := [("npy_wrap", diffWrap), ("npy_write", diffWrite)]

end NumpyLean.NpyFormat
