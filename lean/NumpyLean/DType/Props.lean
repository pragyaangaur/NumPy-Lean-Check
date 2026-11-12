import NumpyLean.DType.Model

/-
Properties of the casting and promotion models. Each property carries a status line that `scripts/check_props.py` counts.

The dtype tables are finite, so most properties are stated over a finite universe and proved by evaluation. `numerics` holds every numeric legacy type including bool, half, `long` and `long long`. `univ` adds object and a sample of byte and unicode strings whose lengths sit on the edges where casting changes (0 is the unsized `S` or `U`, and 3, 4, 5 and 21 are the lengths of `uint8`, `int8`, `bool` and `int64`).
-/
namespace NumpyLean.DType

def numericNums : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 23]

def numerics : List Descr := numericNums.map (fun n => ⟨n, 0⟩)

def strSample : List Descr :=
  [⟨18, 0⟩, ⟨18, 1⟩, ⟨18, 3⟩, ⟨18, 4⟩, ⟨18, 5⟩, ⟨18, 21⟩, ⟨18, 96⟩,
   ⟨19, 0⟩, ⟨19, 1⟩, ⟨19, 3⟩, ⟨19, 4⟩, ⟨19, 21⟩, ⟨19, 96⟩]

def univ : List Descr := numerics ++ [⟨NPY_OBJECT, 0⟩] ++ strSample

def argUniv : List Arg := univ.map Arg.dtype ++ [.pyInt, .pyFloat, .pyComplex]

def allCastings : List Casting := [.no, .equiv, .safe, .sameKind, .«unsafe»]

def bool' : Descr := ⟨NPY_BOOL, 0⟩
def int8 : Descr := ⟨NPY_BYTE, 0⟩
def uint8 : Descr := ⟨NPY_UBYTE, 0⟩
def half : Descr := ⟨NPY_HALF, 0⟩
def float32 : Descr := ⟨NPY_FLOAT, 0⟩
def float64 : Descr := ⟨NPY_DOUBLE, 0⟩
def longdouble : Descr := ⟨NPY_LONGDOUBLE, 0⟩
def object' : Descr := ⟨NPY_OBJECT, 0⟩
def bytesN (n : Nat) : Descr := ⟨NPY_STRING, n⟩

/-! ## promote_types -/

/-- PROP dtype.promote_types.commutative : PROVEN
Source: `numpy.promote_types` docstring, "This function is symmetric". Checked on every pair of `univ`. -/
theorem promote_types_commutative :
    (univ.all fun a => univ.all fun b => promoteTypes a b == promoteTypes b a) = true := by
  decide

/-- PROP dtype.promote_types.idempotent : PROVEN
Source: algebraic law expected of a join. `promote_types(a, a)` is `a` for every dtype of `univ`, including the unsized strings. -/
theorem promote_types_idempotent :
    (univ.all fun a => promoteTypes a a == some a) = true := by
  decide

/-- PROP dtype.promote_types.total : PROVEN
Source: `doc/source/reference/arrays.promotion.rst`, numbers promote with strings and everything promotes with object. No pair of `univ` raises. -/
theorem promote_types_total :
    (univ.all fun a => univ.all fun b => (promoteTypes a b).isSome) = true := by
  decide

/-- PROP dtype.promote_types.associative : REFUTED
Source: algebraic law. The `numpy.promote_types` docstring already says "This function is symmetric, but rarely associative", so this is documented behaviour and has no bug record. A numeric counterexample: `p(p(int8, uint8), float16)` is `float32` but `p(int8, p(uint8, float16))` is `float16`. -/
theorem promote_types_associative_refuted :
    ¬ (∀ a b c : Descr, ((promoteTypes a b).bind fun ab => promoteTypes ab c) =
        ((promoteTypes b c).bind fun bc => promoteTypes a bc)) := by
  intro h
  have := h int8 uint8 half
  exact absurd this (by decide)

/-- PROP dtype.promote_types.associative_on_strings_example : REFUTED
Source: the example in the `numpy.promote_types` docstring, `p('S', p('i1', 'u1'))` is `S6` and `p(p('S', 'i1'), 'u1')` is `S4`. The model reproduces the documented example. -/
theorem promote_types_docstring_example :
    ¬ (((promoteTypes int8 uint8).bind fun x => promoteTypes (bytesN 0) x) =
        ((promoteTypes (bytesN 0) int8).bind fun x => promoteTypes x uint8)) := by
  decide

/-- PROP dtype.promote_types.upper_bound : PROVEN
Source: `numpy.promote_types` docstring, "the data type ... to which both type1 and type2 may be safely cast". For every pair of `univ`, both inputs cast safely to the result. -/
theorem promote_types_upper_bound :
    (univ.all fun a => univ.all fun b =>
      match promoteTypes a b with
      | some p => canCast a p .safe && canCast b p .safe
      | none => false) = true := by
  decide

/-- PROP dtype.promote_types.least_numeric_upper_bound : REFUTED
Source: `numpy.promote_types` docstring, "the data type with the smallest size and smallest scalar kind to which both type1 and type2 may be safely cast". Read as a join of the safe casting order, every common safe target of `a` and `b` would also be a safe target of the result. It is not: `int8` and `uint8` both cast safely to `float16`, but their promotion `int16` does not. The docstring orders by size and then by kind, and `int16` is first in that order, so this is not a bug. It is the same cause as the documented non-associativity. -/
theorem promote_types_least_numeric_upper_bound_refuted :
    ¬ (∀ a b c : Descr, canCast a c .safe = true → canCast b c .safe = true →
        ∃ p, promoteTypes a b = some p ∧ canCast p c .safe = true) := by
  intro h
  obtain ⟨p, hp, hc⟩ := h int8 uint8 half (by decide) (by decide)
  have : p = ⟨NPY_SHORT, 0⟩ := by
    have h2 : promoteTypes int8 uint8 = some ⟨NPY_SHORT, 0⟩ := by decide
    rw [h2] at hp
    exact (Option.some.inj hp).symm
  subst this
  exact absurd hc (by decide)

/-- PROP dtype.promote_types.string_length_is_minimal : PROVEN
Source: `numpy.promote_types` notes, the result "returns a valid string length when given an integer or float dtype as one argument and a string dtype as another argument". For each numeric type the length chosen by `promote_types(t, 'S')` is the smallest length that `t` casts to safely, checked for every length up to 120. -/
theorem promote_types_string_length_is_minimal :
    (numerics.all fun a =>
      match promoteTypes a (bytesN 0) with
      | some p => (List.range 121).all fun w =>
          canCast a (bytesN (w + 1)) .safe == decide (p.chars ≤ w + 1)
      | none => false) = true := by
  decide

/-! ## can_cast -/

/-- PROP dtype.can_cast.levels_are_monotone : PROVEN
Source: `numpy.can_cast` docstring, the casting levels are ordered from 'no' to 'unsafe'. A cast allowed at one level is allowed at every less strict level. -/
theorem can_cast_levels_monotone :
    (univ.all fun a => univ.all fun b =>
      allCastings.all fun c => allCastings.all fun c' =>
        !(canCast a b c && c.toNat ≤ c'.toNat) || canCast a b c') = true := by
  decide

/-- PROP dtype.can_cast.unsafe_always : PROVEN
Source: `numpy.can_cast` docstring, "'unsafe' means any data conversions may be done". Every pair of `univ` is castable under 'unsafe'. -/
theorem can_cast_unsafe_always :
    (univ.all fun a => univ.all fun b => canCast a b .«unsafe») = true := by
  decide

/-- PROP dtype.can_cast.safe_reflexive : PROVEN
Source: preorder law for safe casting. Every dtype of `univ` casts to itself under 'no', hence under 'safe'. -/
theorem can_cast_reflexive :
    (univ.all fun a => canCast a a .no) = true := by
  decide

/-- PROP dtype.can_cast.safe_transitive : REFUTED
Source: preorder law for safe casting. `bool` casts safely to `int8` and `int8` casts safely to `S4`, but `bool` does not cast safely to `S4`, because the string form of a bool is `True` or `False` and needs five characters (`convert_datatype.c:2455-2458`). Each answer alone preserves values, so this is not recorded as a bug. On the sized dtypes of `univ` these bool, `int8` or `uint8` and short string chains are the only failures. -/
theorem can_cast_safe_transitive_refuted :
    ¬ (∀ a b c : Descr, canCast a b .safe = true → canCast b c .safe = true → canCast a c .safe = true) := by
  intro h
  have := h bool' int8 (bytesN 4) (by decide) (by decide)
  exact absurd this (by decide)

/-- PROP dtype.can_cast.no_means_same_dtype : REFUTED
Source: `numpy.can_cast` docstring, "'no' means the data types should not be cast at all". `can_cast(float64, longdouble, 'no')` is True on platforms where `long double` is `double`, because `add_numeric_cast` (`convert_datatype.c:2359`) gives every pair of the same kind and item size the byte swap cast with "no" casting. The source comment there calls these "equivalent C-types", so this is intended and has no bug record. -/
theorem can_cast_no_means_same_dtype_refuted :
    ¬ (∀ a b : Descr, canCast a b .no = true → a = b) := by
  intro h
  have := h float64 longdouble (by decide)
  exact absurd this (by decide)

/-! ## result_type -/

/-- PROP dtype.result_type.agrees_with_promote_types : PROVEN
Source: `numpy.result_type` and `numpy.promote_types` docs, both apply the same promotion rules. For two dtype arguments of `univ` the results are equal. -/
theorem result_type_agrees_with_promote_types :
    (univ.all fun a => univ.all fun b =>
      resultType [.dtype a, .dtype b] == promoteTypes a b) = true := by
  decide

/-- PROP dtype.result_type.commutative_two_args : PROVEN
Source: `PyArray_PromoteDTypeSequence` comment at `common_dtype.c:157`, the reduction "should guarantee stable results even when changing the order". For two arguments of `argUniv`, including the Python scalars, the order does not matter. -/
theorem result_type_commutative_two_args :
    (argUniv.all fun a => argUniv.all fun b =>
      resultType [a, b] == resultType [b, a]) = true := by
  decide

/-- PROP dtype.result_type.python_int_is_weak : PROVEN
Source: NEP 50, a Python int does not change the result dtype of a NumPy integer, float or complex dtype, and bool with a Python int gives the default integer. -/
theorem result_type_python_int_is_weak :
    (numerics.all fun a =>
      resultType [.dtype a, .pyInt] ==
        some (if a.num == NPY_BOOL then ⟨NPY_INTP, 0⟩ else a)) = true := by
  decide

/-- PROP dtype.result_type.order_independent_with_python_int : REFUTED
Source: `PyArray_PromoteDTypeSequence` comment at `common_dtype.c:157`, the reduction "should guarantee stable results even when changing the order". `np.result_type(np.int8, 'S3', 1)` is `S4`, but `np.result_type('S3', np.int8, 1)` raises `DTypePromotionError`. Real NumPy 2.5.4 does the same. -/
theorem result_type_order_independent_with_python_int_refuted :
    ¬ (∀ a b : Arg, ∀ rest : List Arg, resultType (a :: b :: rest) = resultType (b :: a :: rest)) := by
  intro h
  have := h (.dtype int8) (.dtype (bytesN 3)) [.pyInt]
  exact absurd this (by decide)

/-- PROP dtype.result_type.order_independent_with_half : REFUTED
Source: as above, `common_dtype.c:157`. `np.result_type(np.float16, 'S3', object)` raises `DTypePromotionError`, while `np.result_type(np.float16, object, 'S3')` and every other order give `object`. Real NumPy 2.5.4 does the same. -/
theorem result_type_order_independent_with_half_refuted :
    ¬ (∀ a b c : Arg, resultType [a, b, c] = resultType [a, c, b]) := by
  intro h
  have := h (.dtype half) (.dtype (bytesN 3)) (.dtype object')
  exact absurd this (by decide)

/-! ## NEP 50 Python int operands -/

/-- PROP dtype.pyint_op.overflow_iff_out_of_range : PROVEN
Source: NEP 50, "Python integers that are out of bounds for the NumPy dtype raise an OverflowError". Checked for every integer type and every value at the edges of the eight integer ranges, from `-2**64 - 1` to `2**64 + 1`. -/
theorem pyint_op_overflow_iff_out_of_range :
    let edges : List Int := [0, 1, -1, 127, 128, -128, -129, 255, 256, 32767, 32768, -32768, -32769,
      65535, 65536, 2147483647, 2147483648, -2147483648, -2147483649, 4294967295, 4294967296,
      9223372036854775807, 9223372036854775808, -9223372036854775808, -9223372036854775809,
      18446744073709551615, 18446744073709551616, -18446744073709551616, -18446744073709551617]
    let range (n : Nat) : Int × Int :=
      let bits := 8 * npySizeof n
      if isSigned n then (-(2 : Int) ^ (bits - 1), (2 : Int) ^ (bits - 1) - 1) else (0, (2 : Int) ^ bits - 1)
    ((List.range 10).all fun k => edges.all fun v =>
      let n := k + 1
      (pyIntOp n v).isNone == !(decide ((range n).1 ≤ v) && decide (v ≤ (range n).2))) = true := by
  decide

/-! ## Python ints of any size with floating point and complex dtypes -/

/-- The floating point and complex dtypes of the tests. -/
def floatNums : List Nat := [NPY_HALF, NPY_FLOAT, NPY_DOUBLE, NPY_LONGDOUBLE, NPY_CFLOAT, NPY_CDOUBLE, NPY_CLONGDOUBLE]

/-- Python ints at the limits where the outcome changes, and their negatives are added by `bigEdges`. -/
def bigEdgesPos : List Int :=
  [0, 1, 65504, 65519, 65520, 65535, 65536, 2 ^ 24, 2 ^ 53, 2 ^ 63 - 1, 2 ^ 63, 2 ^ 64, 2 ^ 127,
   2 ^ 128 - 2 ^ 104, 2 ^ 128 - 2 ^ 103 - 2 ^ 74 - 1, 2 ^ 128 - 2 ^ 103 - 2 ^ 74, 2 ^ 128 - 2 ^ 103 - 2 ^ 73,
   2 ^ 128 - 2 ^ 103 - 1, 2 ^ 128 - 2 ^ 103, 2 ^ 128, 2 ^ 1023, 2 ^ 1024 - 2 ^ 970 - 1, 2 ^ 1024 - 2 ^ 970,
   2 ^ 1024 - 1, 2 ^ 1024, 10 ^ 400]

def bigEdges : List Int := bigEdgesPos ++ bigEdgesPos.map (fun v => -v)

/-- PROP dtype.pyint_to_float.scalar_equals_array : PROVEN
Source: `convert_to_@name@`, `umath/scalarmath.c.src:973-1001`. `np.float32(1) + v` sends a Python int that does not fit a `long` or is not safe to cast from `long` to the `setitem` of the dtype, which is also what `np.asarray(v, dtype)` and an array operand run. A `long` that is safe to cast is converted with a C cast, which for `double`, `longdouble` and their complex types gives the same finite value without a warning as the `setitem`. Checked on `bigEdges` for every floating point and complex dtype. -/
theorem pyint_to_float_scalar_equals_array :
    (floatNums.all fun n => bigEdges.all fun v => pyIntScalarConv n v == pyIntToFloat n v) = true := by
  decide +kernel

/-- PROP dtype.pyint_to_float.complex_matches_real_float : PROVEN
Source: `FLOAT_setitem` and `CFLOAT_setitem`, `DOUBLE_setitem` and `CDOUBLE_setitem` (`arraytypes.c.src:355` and `:449`) both go through a double and then narrow in the same way. Real and complex give the same outcome on `bigEdges` for float32 with complex64 and for float64 with complex128. -/
theorem pyint_to_float_complex_matches_real_float :
    (bigEdges.all fun v => pyIntToFloat NPY_FLOAT v == pyIntToFloat NPY_CFLOAT v
      && pyIntToFloat NPY_DOUBLE v == pyIntToFloat NPY_CDOUBLE v) = true := by
  decide +kernel

/-- PROP dtype.pyint_to_float.complex_matches_real_longdouble : REFUTED
Source: `LONGDOUBLE_setitem` converts a Python int with `npy_longdouble_from_PyLong` (`arraytypes.c.src:526`, `common/npy_longdouble.c:128`), "without precision or range loss via a double", and gives an infinity and a `RuntimeWarning` beyond the range. `CLONGDOUBLE_setitem` (`arraytypes.c.src:449`) takes the int through a Python complex number, a double, and raises `OverflowError` ("int too large to convert to float") from `2**1024 - 2**970`. So `np.asarray(2**1024, dtype=np.longdouble)` is `inf` with a warning and `np.asarray(2**1024, dtype=np.clongdouble)` raises. -/
theorem pyint_to_float_longdouble_complex_differ :
    pyIntToFloat NPY_LONGDOUBLE (2 ^ 1024) = some (.ok true true) ∧ pyIntToFloat NPY_CLONGDOUBLE (2 ^ 1024) = some .overflowError := by
  decide +kernel

/-- PROP dtype.pyint_to_float.longdouble_never_raises : PROVEN
Source: `npy_longdouble_from_PyLong`, `common/npy_longdouble.c:128`, which only warns on `ERANGE`. Storing any Python int in a `longdouble` gives a value, finite or infinite, and never `OverflowError`. -/
theorem pyint_to_float_longdouble_never_raises (v : Int) : pyIntToFloat NPY_LONGDOUBLE v ≠ some .overflowError := by
  simp [pyIntToFloat, NPY_LONGDOUBLE, isFloat, isComplex]

/-- PROP dtype.pyint_to_float.warning_iff_infinite : PROVEN
Source: `MyPyFloat_AsFloat` and `MyPyFloat_AsHalf` (`arraytypes.c.src:123-150`) warn exactly when narrowing makes an infinity from a finite double, `CFLOAT_setitem` does the same for both parts, and `npy_longdouble_from_PyLong` warns on `ERANGE`, which is when `strtold` returns an infinity. Every stored value that is infinite comes with the `RuntimeWarning` and no finite value does. -/
theorem pyint_to_float_warning_iff_infinite (n : Nat) (v : Int) (inf warns : Bool)
    (h : pyIntToFloat n v = some (.ok inf warns)) : warns = inf := by
  unfold pyIntToFloat at h
  split at h
  · simp at h
  · split at h
    · simp only [Option.some.injEq, PyIntConv.ok.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [← h1, ← h2]
    · split at h
      · simp at h
      · split at h
        · simp only [Option.some.injEq, PyIntConv.ok.injEq] at h
          obtain ⟨h1, h2⟩ := h
          rw [← h1, ← h2]
        · split at h
          · simp only [Option.some.injEq, PyIntConv.ok.injEq] at h
            obtain ⟨h1, h2⟩ := h
            rw [← h1, ← h2]
          · simp only [Option.some.injEq, PyIntConv.ok.injEq] at h
            obtain ⟨h1, h2⟩ := h
            rw [← h1, ← h2]

/-- PROP dtype.pyint_to_float.float32_limit_is_exact : REFUTED
Source: the NumPy documentation of `float32` and IEEE 754 round to nearest: an integer converts to infinity when it is at least `2**128 - 2**103`, the midpoint between the largest float32 and `2**128`. The int is rounded twice, first to a double by `PyNumber_Float` and then to float32 (`MyPyFloat_AsFloat`, `arraytypes.c.src:123`). An int up to `2**74` below the midpoint rounds up to the double that is the midpoint and overflows, for example `2**128 - 2**103 - 2**73`. -/
theorem pyint_to_float_float32_limit_refuted :
    pyIntToFloat NPY_FLOAT (2 ^ 128 - 2 ^ 103 - 2 ^ 73) = some (.ok true true) ∧ (2 ^ 128 - 2 ^ 103 - 2 ^ 73 : Int).natAbs < 2 ^ 128 - 2 ^ 103 := by
  decide +kernel

/-- PROP dtype.pyint_to_float.half_limit : PROVEN
Source: IEEE 754 half precision, largest finite value 65504, and the rounding of `npy_double_to_half`. A Python int becomes infinite in a float16 exactly from 65520 on, checked for every int from 65400 to 65700 and its negative. -/
theorem pyint_to_float_half_limit :
    ((List.range 300).all fun k =>
      let v : Int := 65400 + k
      (pyIntToFloat NPY_HALF v == some (.ok (decide (65520 ≤ v)) (decide (65520 ≤ v))))
      && (pyIntToFloat NPY_HALF (-v) == some (.ok (decide (65520 ≤ v)) (decide (65520 ≤ v))))) = true := by
  decide +kernel

/-- PROP dtype.pyint_to_float.double_overflow_threshold : PROVEN
Source: `PyLong_AsDouble` rounds correctly and raises `OverflowError` when the result would be `2**1024`, which is from `2**1024 - 2**970` (the midpoint between the largest double and `2**1024`) on. Checked on `bigEdges`. -/
theorem pyint_to_float_double_overflow_threshold :
    (bigEdges.all fun v => (pyLongToDouble v).isNone == decide (2 ^ 1024 - 2 ^ 970 ≤ v.natAbs)) = true := by
  decide +kernel


end NumpyLean.DType
