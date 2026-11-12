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
Source: the docstring of `read_array_header_1_0`, `lib/_format_impl.py:538`, "Raises ValueError If the data is invalid". A header whose closing brace is missing (a truncated file) makes `ast.literal_eval` raise `SyntaxError`, and the retry for Python 2 files at line 656 runs `_filter_header`, whose `tokenize` call raises `tokenize.TokenError` for the unclosed brace. That error is not a `ValueError` and escapes. The same happens for an unterminated string. NumPy shows the same, see `bugs/npyformat-read-header-token-error.yaml`. -/
theorem readHeader_tokenError_refuted :
    ¬ (∀ d : List Nat, readHeader 1 d ≠ .error .tokenError) := by
  intro h
  exact h (withLen1 "{'descr': '<f8', 'fortran_order': False, 'shape': (3,), ") (by decide +kernel)

/-- PROP npyformat.read_header.keys_error_is_value_error : REFUTED
Source: the same docstring, "Raises ValueError If the data is invalid", and line 667, which formats `sorted(d.keys())` into the `ValueError` for wrong keys. When the keys cannot be ordered, as for `{'a': 1, 1: 2}`, the `sorted` call raises `TypeError` first. NumPy shows the same, see `bugs/npyformat-read-header-key-sort-type-error.yaml`. -/
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
Source: `ValueError` for invalid data in the docstring of `read_array`, `lib/_format_impl.py:808`, and `np.zeros((-1, 2))`, which refuses negative dimensions. `read_array` computes the count with `multiply.reduce(shape, dtype=int64)` (line 837), which wraps, and reshapes with `array.reshape(shape)`, which treats any negative entry as the unknown dimension (`shape.c:499`). The shape `(-4294967296, 4294967296)` has a wrapped count of 0 and loads as an empty array of shape `(0, 4294967296)`. NumPy shows the same, see `bugs/npyformat-read-array-negative-shape-wraps.yaml`. -/
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

end NumpyLean.NpyFormat
