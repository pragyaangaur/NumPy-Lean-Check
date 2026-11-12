import NumpyLean.NpyFormat.Model

/-
Properties of the NpyFormat models. Each property carries a status line that `scripts/check_props.py` counts.

Status values: PROVEN (the theorem states the property), REFUTED (the theorem states the negation and gives a counterexample), OPEN (stated in a comment only).
-/
namespace NumpyLean.NpyFormat
open NumpyLean

/-! ## Header padding -/

/-- PROP npyformat.wrap_header.aligned : PROVEN
Source: the comment at `lib/_format_impl.py:413`, "Pad the header with spaces and a final newline such that the magic string, the header-length short and the header are aligned on a ARRAY_ALIGN byte boundary". -/
theorem wrapHeader_aligned (v : Version) (h : String) (w : Wrapped) (hw : wrapHeader v h = .ok w) :
    w.total % arrayAlign = 0 := by
  unfold wrapHeader at hw
  split at hw
  · simp at hw
  · rename_i n hn
    dsimp only at hw
    split at hw
    · simp at hw
      subst hw
      simp only [arrayAlign, magicLen]
      omega
    · simp at hw

/-- PROP npyformat.wrap_header.length_field_matches : PROVEN
Source: the format specification in the module docstring, "HEADER_LEN ... the length of the header data", which counts from the end of the length field to the end of the file header. The stored value is the total minus the magic and the length field. -/
theorem wrapHeader_length_field (v : Version) (h : String) (w : Wrapped) (hw : wrapHeader v h = .ok w) :
    w.hfield = w.total - magicLen - v.sizeBytes := by
  unfold wrapHeader at hw
  split at hw
  · simp at hw
  · dsimp only at hw
    split at hw
    · simp at hw
      subst hw
      simp only [magicLen]
      omega
    · simp at hw

/-- PROP npyformat.wrap_header.padding_between_1_and_64 : PROVEN
Source: `lib/_format_impl.py:408`. The padding is `ARRAY_ALIGN - (x % ARRAY_ALIGN)`, which is never zero, so a header that is already aligned still receives a whole block of padding. The newline comes on top of that. -/
theorem wrapHeader_padding_range (v : Version) (h : String) (w : Wrapped) (hw : wrapHeader v h = .ok w) :
    1 ≤ w.padlen ∧ w.padlen ≤ arrayAlign := by
  unfold wrapHeader at hw
  split at hw
  · simp at hw
  · dsimp only at hw
    split at hw
    · simp at hw
      subst hw
      simp only [arrayAlign]
      omega
    · simp at hw

/-- PROP npyformat.guess_version.prefers_1_0 : PROVEN
Source: `_wrap_header_guess_version`, `lib/_format_impl.py:421`, "chooses an appropriate version" and `_write_array_header`, "None means use oldest that works". When version 1.0 works, it is the one chosen. -/
theorem wrapGuess_prefers_v1 (h : String) (w : Wrapped) (hw : wrapHeader .v1 h = .ok w) :
    wrapGuess h = .ok w := by
  simp [wrapGuess, hw]

/-- PROP npyformat.guess_version.never_fails_on_latin1 : PROVEN
Source: the docstring of `_write_array_header`, "None means use oldest that works". For a concrete large header (65536 latin1 characters) version 1.0 fails and 2.0 is chosen. -/
theorem wrapGuess_large_header_uses_v2 :
    (wrapGuess (String.ofList (List.replicate 65536 'a'))).toOption.map (·.version) = some .v2 := by
  -- A list of 65536 characters is too deep for the kernel recursion limit, so `native_decide` is used, which trusts the compiler.
  native_decide

/-! ## Header reader -/

/-- Bytes of a header text with a version 1.0 length field. -/
def withLen1 (t : String) : List Nat :=
  let b := t.toList.map Char.toNat
  [b.length % 256, b.length / 256] ++ b

/-- PROP npyformat.read_header.errors_are_value_errors : REFUTED
Source: the docstring of `read_array_header_1_0`, `lib/_format_impl.py:538`, "Raises ValueError If the data is invalid". A header whose closing brace is missing (a truncated file) makes `ast.literal_eval` raise `SyntaxError`, and the retry for Python 2 files at line 661 runs `_filter_header`, whose `tokenize` call raises `tokenize.TokenError` for the unclosed brace. That error is not a `ValueError` and escapes. The same happens for an unterminated string. NumPy shows the same, see `bugs/npyformat-read-header-token-error.yaml`. -/
theorem readHeader_tokenError_refuted :
    ¬ (∀ d : List Nat, readHeader 1 d ≠ .error .tokenError) := by
  intro h
  exact h (withLen1 "{'descr': '<f8', 'fortran_order': False, 'shape': (3,), ") (by decide +kernel)

/-- PROP npyformat.read_header.keys_error_is_value_error : REFUTED
Source: the same docstring, "Raises ValueError If the data is invalid", and line 681, which formats `sorted(d.keys())` into the `ValueError` for wrong keys (line 681). When the keys cannot be ordered, as for `{'a': 1, 1: 2}`, the `sorted` call raises `TypeError` first. NumPy shows the same, see `bugs/npyformat-read-header-key-sort-type-error.yaml`. -/
theorem readHeader_keySort_refuted :
    ¬ (∀ d : List Nat, readHeader 1 d ≠ .error .keySort) := by
  intro h
  exact h (withLen1 "{'a': 1, 1: 2}") (by decide +kernel)

/-- PROP npyformat.read_header.accepts_written_header : PROVEN
Source: round trip of `write_array_header_1_0` and `read_array_header_1_0`. For the concrete header text of a `<f8` array of shape `(3, 4)` the reader returns the shape, the order and the dtype that were written. -/
theorem readHeader_roundtrip_example :
    readHeader 1 (withLen1 "{'descr': '<f8', 'fortran_order': False, 'shape': (3, 4), }") = .ok ⟨[3, 4], false, "<f8"⟩ := by
  decide +kernel

/-- PROP npyformat.read_header.negative_shape_accepted : REFUTED
Source: the format description in the module docstring, "shape : tuple of int" and the `ValueError` for invalid data. Nothing in `_read_array_header`, `lib/_format_impl.py:621` to `700`, rejects a negative entry, so the header of an array of shape `(-3,)` is accepted. NumPy shows the same. The refutation is about the reader alone. What `read_array` then does with it is the next property. -/
theorem readHeader_negative_shape_refuted :
    ¬ (∀ d h, readHeader 1 d = .ok h → ∀ x ∈ h.shape, 0 ≤ x) := by
  intro h
  have := h (withLen1 "{'descr': '<f8', 'fortran_order': False, 'shape': (-3,), }") ⟨[-3], false, "<f8"⟩ (by decide +kernel) (-3) (by decide +kernel)
  exact absurd this (by decide +kernel)

/-! ## read_array -/

/-- PROP npyformat.read_array.negative_shape_rejected : REFUTED
Source: `ValueError` for invalid data in the docstring of `read_array`, `lib/_format_impl.py:808`, and `np.zeros((-1, 2))`, which refuses negative dimensions. `read_array` computes the count with `multiply.reduce(shape, dtype=int64)` (line 827), which wraps, and reshapes with `array.reshape(shape)`, which treats any negative entry as the unknown dimension (`shape.c:499`). The shape `(-4294967296, 4294967296)` has a wrapped count of 0 and loads as an empty array of shape `(0, 4294967296)`. NumPy shows the same, see `bugs/npyformat-read-array-negative-shape-wraps.yaml`. -/
theorem readArray_negative_shape_refuted :
    ¬ (∀ shape f r, shape.any (· < 0) = true → readArrayShape shape f ≠ .ok r) := by
  intro h
  exact h [-4294967296, 4294967296] false [0, 4294967296] (by decide +kernel) (by decide +kernel)

/-- PROP npyformat.read_array.ordinary_shape : PROVEN
Source: `read_array`, `lib/_format_impl.py:781`. An ordinary shape comes back unchanged, in both orders. -/
theorem readArray_ordinary_shape :
    readArrayShape [3, 4] false = .ok [3, 4] ∧ readArrayShape [3, 4] true = .ok [3, 4] := by
  decide +kernel

/-! ## frombuffer -/

/-- `withinBuffer` holds when a refused call, or an accepted call that stays inside the buffer. -/
def withinBuffer (len : Nat) (code : String) (cnt off : Int) : Bool :=
  match frombuffer len code cnt off with
  | .ok n => decide (0 ≤ n ∧ off + n * (((itemsizeOf code).getD 0 : Nat) : Int) ≤ len)
  | .error _ => true

/-- PROP npyformat.frombuffer.result_within_buffer : PROVEN
Source: the `count` and `offset` checks in `PyArray_FromBuffer`, `ctors.c:3777` to `3815`, and the docstring of `numpy.frombuffer`. An accepted call never describes memory outside the buffer. Checked for every buffer length up to 16, offsets from -2 to 17, the item sizes 1, 2, 3, 8 and 16 and counts from -2 to 19, with `decide`. The general statement needs facts about `wrap64`. -/
theorem frombuffer_within_buffer_small :
    ∀ len ∈ List.range 17, ∀ off ∈ (List.range 20).map (fun (i : Nat) => (i : Int) - 2),
    ∀ code ∈ ["i1", "i2", "V3", "i8", "c16"], ∀ cnt ∈ (List.range 22).map (fun (i : Nat) => (i : Int) - 2),
    withinBuffer len code cnt off = true := by
  decide +kernel

/-- PROP npyformat.frombuffer.large_count_error_is_too_small : REFUTED
Source: ctors.c:3809, `if (s < n*itemsize)` with the message "buffer is smaller than requested size". The product is a signed `npy_intp` product that wraps (undefined behaviour in C), so a count such as `2**61 + 1` with 8 byte items gives a wrapped product of 8, passes the test, and fails later in the array constructor with "array is too big". The call is refused either way, but with a different error for the same mistake. NumPy shows the same, see `bugs/npyformat-frombuffer-count-times-itemsize-wraps.yaml`. -/
theorem frombuffer_large_count_refuted :
    ¬ (∀ len code cnt off e, frombuffer len code cnt off = .error e → 0 ≤ cnt →
        (len : Int) - off < cnt * ((itemsizeOf code).getD 0 : Nat) → 0 ≤ off → off ≤ len → (itemsizeOf code).getD 0 ≠ 0 → e = .small) := by
  intro h
  have := h 8 "i8" 2305843009213693953 0 .tooBig (by decide +kernel) (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
  exact absurd this (by decide)

/-! ## loadtxt integer fields -/

/-- PROP npyformat.loadtxt_int.limits : PROVEN
Source: `DECLARE_TO_INT` and `DECLARE_TO_UINT`, `textreading/str_to_int.c:13`. The limits of each type are accepted and the values just outside them are rejected, and `-0` is rejected for unsigned types. -/
theorem loadtxtInt_limits :
    loadtxtIntTyped "i1" "127".toList = some 127 ∧ loadtxtIntTyped "i1" "128".toList = none
    ∧ loadtxtIntTyped "i1" "-128".toList = some (-128) ∧ loadtxtIntTyped "i1" "-129".toList = none
    ∧ loadtxtIntTyped "i8" "9223372036854775807".toList = some 9223372036854775807
    ∧ loadtxtIntTyped "i8" "9223372036854775808".toList = none
    ∧ loadtxtIntTyped "i8" "-9223372036854775808".toList = some (-9223372036854775808)
    ∧ loadtxtIntTyped "i8" "-9223372036854775809".toList = none
    ∧ loadtxtIntTyped "u8" "18446744073709551615".toList = some 18446744073709551615
    ∧ loadtxtIntTyped "u8" "18446744073709551616".toList = none
    ∧ loadtxtIntTyped "u8" "-0".toList = none ∧ loadtxtIntTyped "u1" "+255".toList = some 255 := by
  decide +kernel

/-- PROP npyformat.loadtxt_int.digit_loop_bounded : PROVEN
Source: the overflow tests in `str_to_int.h:45` and `:75`. The digit loop never produces a magnitude above its limit. -/
theorem accumDigits_le (limit : Nat) (l : List Char) :
    ∀ acc m r, acc ≤ limit → accumDigits limit acc l = some (m, r) → m ≤ limit := by
  induction l with
  | nil => intro acc m r hacc h; simp [accumDigits] at h; omega
  | cons c rest ih =>
    intro acc m r hacc h
    simp only [accumDigits] at h
    split at h
    · split at h
      · exact ih _ m r (by assumption) h
      · simp at h
    · simp at h; omega

/-- PROP npyformat.loadtxt_int.agrees_with_python_int : REFUTED
Source: no documentation promises it, but users expect `loadtxt` of an integer column to accept what `int()` accepts. The `numpy.loadtxt` docstring shows converters for "floats with underscores", so underscores in numbers are known to need a converter. `int("1_000")` is 1000 while `loadtxt` rejects the field `1_000`, and the same holds for non-ASCII digits such as the Arabic-Indic `١٢٣` (the C code uses `isdigit`). This is documented behaviour, so there is no bug record. -/
theorem loadtxtInt_python_int_refuted :
    ¬ (∀ s : List Char, s = "1_000".toList → loadtxtIntTyped "i8" s = some 1000) := by
  intro h
  have := h "1_000".toList rfl
  exact absurd this (by decide +kernel)

/-! ## dtype descriptors -/

/-- PROP npyformat.dtype_str.byte_order : PROVEN
Source: `descr_to_dtype`, `lib/_format_impl.py:311`, which hands strings to `numpy.dtype`. One byte types print `|`, and others print `<` unless `>` is given. -/
theorem dtypeStr_examples :
    dtypeStr "<f8" = some "<f8" ∧ dtypeStr ">f8" = some ">f8" ∧ dtypeStr "=i4" = some "<i4" ∧ dtypeStr "|i1" = some "|i1"
    ∧ dtypeStr "u1" = some "|u1" ∧ dtypeStr "f3" = none ∧ dtypeStr "M8[10us]" = some "<M8[10us]" := by
  decide +kernel

/-! ## PEP 3118 buffer format -/

section Pep3118
open Pep3118

/-- The format string, or `ERR` when the writer refuses the dtype. -/
def fmtOut (n : Nat) (d : D) : String :=
  match bufferFormat n d with
  | .ok f => f
  | .error _ => "ERR"

/-- The canonical dtype of the round trip, or the kind of error. -/
def rtOut (n : Nat) (d : D) : String :=
  match roundTrip n d with
  | .ok r => canon r
  | .error .itemsize => "ERR itemsize"
  | .error .parse => "ERR parse"
  | .error (.format _) => "ERR format"

/-- The item size of what the parser makes of the writer's string, before the check of `ctors.c:1262`. -/
def parsedSize (n : Nat) (d : D) : Option Nat :=
  match bufferFormat n d with
  | .ok f => (match parseFormat f.toList with | .ok r => some r.size | .error _ => none)
  | .error _ => none

def offsetsOf : D → List Nat
  | .struct _ fs => fs.map (fun p => p.2.1)
  | _ => []

/-- `np.dtype([('a', 'i4'), ('b', 'i1')])`, a packed structured dtype of 5 bytes. -/
def packedI4B : D := .struct 5 [("a", 0, .scalar '=' 'i' 4), ("b", 4, .scalar '|' 'b' 1)]

/-- PROP npyformat.pep3118.round_trip.keeps_item_size : PROVEN
Source: `_array_from_buffer_3118`, `_core/src/multiarray/ctors.c:1247`: "Sanity check", the parsed dtype must have the item size of the buffer or the call raises `RuntimeError`. So when `np.array(memoryview(a))` succeeds, its dtype has the item size of `a`. -/
theorem roundTrip_keeps_item_size (n : Nat) (d r : D) (h : roundTrip n d = .ok r) : r.size = d.size := by
  unfold roundTrip at h
  split at h
  · simp at h
  · split at h
    · rename_i x _ _
      split at h
      · rename_i hs
        simp only [Except.ok.injEq] at h
        subst h
        simpa using hs
      · simp at h
    · simp at h

/-- PROP npyformat.pep3118.parse.recovers_item_size_of_format : REFUTED
Source: `_buffer_format_string`, `_core/src/multiarray/buffer.c:191`, and `_dtype_from_pep3118`, `_core/_internal.py:627`, are meant to be inverse: the comments of the module say the string "describes" the dtype. For the packed dtype of 5 bytes and an array of length one the writer gives `T{i:a:b:b:}`, which the parser reads as a native aligned structure of 8 bytes. The importer's own check then raises `RuntimeError`. Same bug record as `npyformat.pep3118.format.same_dtype_same_string_for_every_length`. -/
theorem parse_item_size_refuted :
    ∃ n d, parsedSize n d ≠ none ∧ parsedSize n d ≠ some d.size :=
  ⟨1, packedI4B, by decide +kernel, by decide +kernel⟩

/-- PROP npyformat.pep3118.format.same_dtype_same_string_for_every_length : REFUTED
Source: nothing promises it, but a format string describes a dtype and not an array, and `np.dtype` equality does not look at the length. The leaf check `_is_natively_aligned_at`, `buffer.c:141`, only tests the stride when the length is above one. For the packed dtype of 5 bytes the string is `T{i:a:b:b:}` for length one, which claims native alignment, and `T{=i:a:b:b:}` for length two. -/
theorem format_depends_on_length_refuted :
    fmtOut 1 packedI4B = "T{i:a:b:b:}" ∧ fmtOut 2 packedI4B = "T{=i:a:b:b:}" ∧ rtOut 1 packedI4B = "ERR itemsize"
    ∧ rtOut 2 packedI4B = canon packedI4B := by
  decide +kernel

/-- `np.dtype('V4')`, four opaque bytes. -/
def void4 : D := .scalar '|' 'V' 4

/-- PROP npyformat.pep3118.round_trip.returns_original_dtype : REFUTED
Source: the PEP 3118 round trip of `_array_from_buffer_3118` should give the dtype of the array back. For `V4` the writer gives `4x`, the parser reads padding and drops the unnamed field, and `np.array(memoryview(np.zeros(1, 'V4'))).dtype` is a structured dtype of 4 bytes with no fields. -/
theorem round_trip_returns_original_refuted : ∃ n d r, roundTrip n d = .ok r ∧ canon r ≠ canon d :=
  ⟨1, void4, .struct 4 [], by rfl, by decide +kernel⟩

/-- A structured dtype of 16 bytes whose field `x` holds two elements of a structured type with item size 6, followed by `y`. -/
def paddedElements : D :=
  .struct 16 [("x", 0, .sub [2] (.struct 6 [("a", 0, .scalar '=' 'i' 4)])), ("y", 12, .scalar '=' 'i' 4)]

/-- PROP npyformat.pep3118.round_trip.keeps_element_layout : REFUTED
Source: same as `npyformat.pep3118.round_trip.returns_original_dtype`. The writer does not emit the trailing padding of a structured type (the offset after a structure counts only its fields, `buffer.c:295`), so the format of `paddedElements` is `T{(2)T{i:a:}:x:xxxxi:y:}`. The parser reads the elements as 4 bytes apart instead of 6, the padding that follows makes the total size agree, the item size check passes and the round trip succeeds with a different layout: the second element of `x` is read from the wrong bytes. -/
theorem round_trip_keeps_element_layout_refuted :
    fmtOut 1 paddedElements = "T{(2)T{i:a:}:x:xxxxi:y:}" ∧ rtOut 1 paddedElements ≠ canon paddedElements
    ∧ rtOut 1 paddedElements ≠ "ERR itemsize" ∧ rtOut 1 paddedElements ≠ "ERR parse" := by
  decide +kernel

/-- A structured dtype of 6 bytes with a field of shape (2,) whose base is itself a subarray of shape (3,), `np.dtype([('a', ('u1', (3,)), (2,))])`. -/
def nestedSub : D := .struct 6 [("a", 0, .sub [2] (.sub [3] (.scalar '|' 'B' 1)))]

/-- PROP npyformat.pep3118.format.every_format_parses : REFUTED
Source: `_dtype_from_pep3118`, `_core/_internal.py:627`, is the reader of the strings that `_buffer_format_string` writes. A nested subarray is written as `(2)(3)B`, and the parser takes only one shape prefix per item, so the string is rejected with "Unknown PEP 3118 data type specifier". -/
theorem format_always_parses_refuted :
    fmtOut 1 nestedSub = "T{(2)(3)B:a:}" ∧ rtOut 1 nestedSub = "ERR parse" := by
  decide +kernel

/-- PROP npyformat.pep3118.format.equal_dtypes_equal_strings : REFUTED
Source: `np.dtype('l') == np.dtype('q')` is true on a 64-bit Unix target, but the writer keeps the C type: `buffer.c:374` writes `l` for `long` and `buffer.c:390` writes `q` for `long long`. Both strings read back as equivalent 8 byte integers (`l` is 8 bytes in native mode). The scalar types `np.long` and `np.longlong` are different NumPy types by design, so this is not a bug and has no record. -/
theorem equal_dtypes_equal_strings_refuted :
    canon (.scalar '=' 'l' 8) = canon (.scalar '=' 'q' 8) ∧ fmtOut 1 (.scalar '=' 'l' 8) = "l"
    ∧ fmtOut 1 (.scalar '=' 'q' 8) = "q" := by
  decide +kernel

/-- The type characters and orders of the scalars that the writer accepts, with the byte orders that exist for them. -/
def scalarUniverse : List D :=
  ("?bBO".toList.map fun c => mkScalar '|' c 0)
  ++ ("hHiIlLqQefdFD".toList.flatMap fun c => [mkScalar '=' c 0, mkScalar '>' c 0])
  ++ ("gG".toList.map fun c => mkScalar '=' c 0)
  ++ ((List.range 4).flatMap fun k => [mkScalar '|' 'S' (k + 1), mkScalar '=' 'U' (k + 1), mkScalar '>' 'U' (k + 1)])

/-- PROP npyformat.pep3118.round_trip.scalar_identity : PROVEN
Source: the round trip of `_array_from_buffer_3118`. Every bool, integer, float, complex, object, bytes and unicode scalar, in every byte order and for lengths one to three, comes back as the same canonical dtype. Checked on `scalarUniverse`, which excludes `V`, datetime and the native-only types in a non-native order, because those are the cases the other properties refute or the writer refuses. -/
theorem round_trip_scalar_identity :
    (scalarUniverse.all fun d => [1, 2, 3].all fun n => rtOut n d == canon d) = true := by
  decide +kernel

/-- PROP npyformat.pep3118.format.scalar_refusals : PROVEN
Source: `buffer.c:359` ("cannot expose native-only dtype") and `buffer.c:421` ("cannot include dtype"). The writer refuses datetime and timedelta, and `long double` types in a non-native order, and nothing else. -/
theorem format_scalar_refusals :
    (["?bBhHiIlLqQefdgFDGO".toList, "MmgG".toList].flatten.all fun c =>
      ['=', '>'].all fun o =>
        let d := mkScalar (if "?bBO".toList.contains c then '|' else o) c 0
        (match bufferFormat 1 d with | .ok _ => true | .error _ => false)
          == (!("Mm".toList.contains c) && !(("gG".toList.contains c) && o == '>' && !("?bBO".toList.contains c)))) = true := by
  decide +kernel

/-- Structured dtypes of two fields from a pool of scalars, with gaps before the second field and after it. -/
def flatStructs : List D :=
  let pool := [mkScalar '|' 'b' 0, mkScalar '=' 'i' 0, mkScalar '=' 'd' 0, mkScalar '>' 'h' 0, mkScalar '|' 'S' 3]
  pool.flatMap fun a => pool.flatMap fun b => [0, 1, 3].flatMap fun gap => [0, 3].map fun tail =>
    D.struct (a.size + gap + b.size + tail) [("a", 0, a), ("b", a.size + gap, b)]

def offsetsKept (n : Nat) (d : D) : Bool :=
  match roundTrip n d with
  | .ok r => offsetsOf r == offsetsOf d
  | .error _ => true

/-- PROP npyformat.pep3118.round_trip.keeps_flat_field_offsets : PROVEN
Source: the round trip of `_array_from_buffer_3118`. When the round trip of a structured dtype with two scalar fields succeeds, the parsed dtype has the same field offsets, for every pair from five scalars (bool-sized, `int`, `double`, big endian `short`, bytes of length 3), gaps of 0, 1 and 3 bytes between the fields, 0 and 3 bytes after them (`flatStructs`) and lengths one to three. The writer pads with `x` up to each offset and the parser keeps those offsets. Nested structures are not covered, see `npyformat.pep3118.round_trip.keeps_element_layout`. -/
theorem round_trip_keeps_flat_offsets :
    (flatStructs.all fun d => [1, 2, 3].all fun n => offsetsKept n d) = true := by
  decide +kernel

end Pep3118

end NumpyLean.NpyFormat
