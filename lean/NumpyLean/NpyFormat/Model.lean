import NumpyLean.Common.Intp

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

end NumpyLean.NpyFormat
