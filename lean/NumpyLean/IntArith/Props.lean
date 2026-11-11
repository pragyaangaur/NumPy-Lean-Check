import NumpyLean.IntArith.Model

/-
Properties of the integer arithmetic models. Each property carries a status line that `scripts/check_props.py` counts.

Status values: PROVEN (the theorem states the property), REFUTED (the theorem states the negation and gives a counterexample), OPEN (stated in a comment only).

Some properties are checked over every pair of 8-bit values with `native_decide`, because the general statement needs division lemmas that core Lean does not have. Each such use says so in a comment, since `native_decide` trusts the compiler.
-/
namespace NumpyLean.IntArith

/-! ## Helper lemmas -/

theorem wrapSigned_of_range (bits : Nat) (x : Int) (hb : 1 ≤ bits)
    (hlo : -((2 : Int) ^ (bits - 1)) ≤ x) (hhi : x < (2 : Int) ^ (bits - 1)) :
    wrapSigned bits x = x := by
  have hm : (2 : Int) ^ bits = 2 * (2 : Int) ^ (bits - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, bits = k + 1 := ⟨bits - 1, by omega⟩
    simp [Int.pow_succ, Int.mul_comm]
  have hpos : (0 : Int) < (2 : Int) ^ (bits - 1) := Int.pow_pos (by decide)
  generalize (2 : Int) ^ (bits - 1) = h at hm hpos hlo hhi
  unfold wrapSigned
  simp only [hm]
  rw [Int.mul_ediv_cancel_left h (by decide)]
  by_cases hx : 0 ≤ x
  · rw [Int.emod_eq_of_lt hx (by omega)]
    simp; omega
  · have : x % (2 * h) = x + 2 * h := by
      have e : x = (x + 2 * h) + (-1) * (2 * h) := by omega
      conv => lhs; rw [e]
      rw [Int.add_mul_emod_self_right]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    rw [this]
    simp; omega

/-- The value `2 ^ (bits - 1)`, one past the signed maximum, wraps to the signed minimum. -/
theorem wrapSigned_half (bits : Nat) (hb : 1 ≤ bits) :
    wrapSigned bits ((2 : Int) ^ (bits - 1)) = -((2 : Int) ^ (bits - 1)) := by
  have hm : (2 : Int) ^ bits = 2 * (2 : Int) ^ (bits - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, bits = k + 1 := ⟨bits - 1, by omega⟩
    simp [Int.pow_succ, Int.mul_comm]
  have hpos : (0 : Int) < (2 : Int) ^ (bits - 1) := Int.pow_pos (by decide)
  generalize (2 : Int) ^ (bits - 1) = h at hm hpos
  unfold wrapSigned
  simp only [hm]
  rw [Int.mul_ediv_cancel_left h (by decide), Int.emod_eq_of_lt (by omega) (by omega)]
  simp; omega

theorem wrap_idem (t : IntTy) (x : Int) : t.wrap (t.wrap x) = t.wrap x := by
  unfold IntTy.wrap
  cases t.signed
  · simp [wrapUnsigned]
  · simp only [wrapSigned, ite_true]
    generalize (2 : Int) ^ t.bits = m
    split <;> rename_i h1
    · rw [Int.sub_emod_right, Int.emod_emod]; simp [h1]
    · rw [Int.emod_emod]; simp [h1]

theorem tdiv_mul_eq_iff (a b : Int) : Int.tdiv a b * b = a ↔ Int.tmod a b = 0 := by
  rw [Int.tmod_def, Int.mul_comm (Int.tdiv a b) b]
  omega

theorem gcdLoop_eq (a b : Nat) : gcdLoop a b = Nat.gcd a b := by
  induction a using Nat.strongRecOn generalizing b with
  | _ a ih =>
    unfold gcdLoop
    by_cases h : a = 0
    · subst h; simp
    · simp only [h, dite_false]
      rw [ih (b % a) (Nat.mod_lt _ (Nat.pos_of_ne_zero h)), Nat.gcd_rec a b]

/-- Every 8-bit value of the type, for the exhaustive checks below. -/
def all8 (t : IntTy) : List Int :=
  (List.range 256).map fun (n : Nat) => if t.signed then (n : Int) - 128 else (n : Int)

/-! ## floor_divide, remainder and divmod -/

/-- PROP intarith.floor_divide.scalar_matches_array : PROVEN
Source: consistency between `np.int8(a) // np.int8(b)` (`scalarmath.c.src:175`) and `np.floor_divide` on arrays (`loops_arithmetic.dispatch.c.src:346`). The two paths give the same value and the same warning for every input, including `b == 0` and `MIN // -1`. -/
theorem floorDiv_scalar_eq_array (t : IntTy) (a b : Int) :
    floorDivScalar t a b = floorDivArray t a b := by
  unfold floorDivScalar floorDivArray
  by_cases hb : b = 0 <;> by_cases ho : (a = t.minVal ∧ b = -1) <;>
    by_cases hs : t.signed <;> by_cases hz : Int.tmod a b = 0 <;>
    simp [*, tdiv_mul_eq_iff] <;> intro h1 h2 <;> exact absurd ⟨h2, h1⟩ ho

/-- PROP intarith.remainder.scalar_matches_array : PROVEN
Source: consistency between `np.int8(a) % np.int8(b)` (`scalarmath.c.src:205`) and `np.remainder` on arrays (`loops_modulo.dispatch.c.src:571`), values and warnings. -/
theorem remainder_scalar_eq_array (t : IntTy) (a b : Int) :
    remainderScalar t a b = remainderArray t a b := by
  unfold remainderScalar remainderArray
  by_cases hb : b = 0 <;> by_cases ho : (a = t.minVal ∧ b = -1) <;>
    by_cases hs : t.signed <;> by_cases hz : Int.tmod a b = 0 <;> by_cases hp : (0 < a ↔ 0 < b) <;>
    simp [*]

/-- PROP intarith.divmod.array_is_floor_divide_and_remainder : PROVEN
Source: `numpy.divmod` docs, "``np.divmod(x, y)`` is equivalent to ``(x // y, x % y)``". The array loop at `loops_modulo.dispatch.c.src:614` gives the quotient of `floor_divide`, the remainder of `remainder`, and the union of their warnings. -/
theorem divmod_array_eq_pair (t : IntTy) (a b : Int) :
    divmodArray t a b =
      (((floorDivArray t a b).1, (remainderArray t a b).1),
        (floorDivArray t a b).2.union (remainderArray t a b).2) := by
  unfold divmodArray floorDivArray remainderArray
  by_cases hb : b = 0 <;> by_cases ho : (a = t.minVal ∧ b = -1) <;>
    by_cases hs : t.signed <;> by_cases hz : Int.tmod a b = 0 <;> by_cases hp : (0 < a ↔ 0 < b) <;>
    simp [*, tdiv_mul_eq_iff, Flags.union, Flags.dbz, Flags.ovf, Flags.clear]

/-- PROP intarith.divmod.scalar_matches_array : PROVEN
Source: consistency between the builtin `divmod` on NumPy scalars (`scalarmath.c.src:463`) and `np.divmod` on arrays. It follows from the three properties above. -/
theorem divmod_scalar_eq_array (t : IntTy) (a b : Int) :
    divmodScalar t a b = divmodArray t a b := by
  rw [divmod_array_eq_pair, divmodScalar, floorDiv_scalar_eq_array, remainder_scalar_eq_array]

/-- PROP intarith.floor_divide.pairs_with_remainder : REFUTED
Source: `numpy.floor_divide` docs, "pairs with the Python ``%`` (`remainder`), function so that ``a = a % b + b * (a // b)`` up to roundoff". For `b == 0` both results are 0, so the identity fails for every nonzero `a`. NumPy raises a divide by zero warning for this input, so this is not filed as a bug. -/
theorem floorDiv_pairs_with_remainder_refuted :
    ¬ (∀ (t : IntTy) (a b : Int), t.inRange a → t.inRange b →
        (remainderArray t a b).1 + b * (floorDivArray t a b).1 = a) := by
  intro h
  have := h .i8 5 0 (by decide) (by decide)
  revert this
  decide

/-- PROP intarith.floor_divide.pairs_with_remainder_nonzero_int8 : PROVEN
Source: the same docstring, restricted to the cases without a warning. For every int8 and uint8 pair with `b ≠ 0` other than `MIN // -1`, the identity holds exactly. Checked over all 65536 pairs of each type with `native_decide`, which trusts the compiler. -/
theorem floorDiv_pairs_with_remainder_8bit :
    ([IntTy.i8, IntTy.u8].all fun t => (all8 t).all fun a => (all8 t).all fun b =>
      b == 0 || (a == t.minVal && b == -1) ||
        (remainderArray t a b).1 + b * (floorDivArray t a b).1 == a) = true := by
  native_decide -- exhaustive check over 2 * 65536 pairs, trusts the compiler

/-- PROP intarith.floor_divide.matches_python_8bit : PROVEN
Source: `numpy.floor_divide` docs, "It is equivalent to the Python ``//`` operator". For int8 and uint8 with `b ≠ 0` and not `MIN // -1`, the array loop gives the floor of the quotient, `Int.fdiv`. Checked over all pairs with `native_decide`, which trusts the compiler. -/
theorem floorDiv_matches_python_8bit :
    ([IntTy.i8, IntTy.u8].all fun t => (all8 t).all fun a => (all8 t).all fun b =>
      b == 0 || (a == t.minVal && b == -1) || (floorDivArray t a b).1 == Int.fdiv a b) = true := by
  native_decide -- exhaustive check over 2 * 65536 pairs, trusts the compiler

/-- PROP intarith.remainder.matches_python_8bit : PROVEN
Source: `numpy.remainder` docs, "It is equivalent to the Python modulus operator ``x1 % x2`` and has the same sign as the divisor `x2`". For int8 and uint8 with `b ≠ 0` the array loop gives `Int.fmod`, which has the sign of the divisor. `MIN % -1` is 0 in both. Checked over all pairs with `native_decide`, which trusts the compiler. -/
theorem remainder_matches_python_8bit :
    ([IntTy.i8, IntTy.u8].all fun t => (all8 t).all fun a => (all8 t).all fun b =>
      b == 0 || (remainderArray t a b).1 == Int.fmod a b) = true := by
  native_decide -- exhaustive check over 2 * 65536 pairs, trusts the compiler

/-- PROP intarith.floor_divide.simd_lane_matches_loop_int8 : PROVEN
Source: `loops_arithmetic.dispatch.c.src:80-89`. The SIMD lane formula for a broadcast divisor that is neither 0 nor -1 gives the same value as `floor_div_@TYPE@` for every int8 pair. Checked with `native_decide`, which trusts the compiler. -/
theorem floorDiv_simd_lane_int8 :
    ((all8 .i8).all fun a => (all8 .i8).all fun d =>
      d == 0 || d == -1 || floorDivSimdLane .i8 a d == (floorDivArray .i8 a d).1) = true := by
  native_decide -- exhaustive check over 65536 pairs, trusts the compiler

/-! ## power -/

/-- PROP intarith.power.scalar_matches_array : PROVEN
Source: consistency between `np.int8(a) ** np.int8(b)` (`scalarmath.c.src:244`, `:1549`) and one element of the general `np.power` loop (`loops.c.src:540`). The fast paths of the array loop give the same values as the scalar squaring loop, and both raise the same error for a negative exponent. -/
theorem power_scalar_eq_array (t : IntTy) (a b : Int) :
    (powerScalar t a b).map (·.1) = powerArrayElem t a b := by
  unfold powerScalar powerArrayElem powerFastPath
  by_cases hn : t.signed = true ∧ b < 0
  · simp [hn, Except.map]
  · have hn' : ¬ ((t.signed && decide (b < 0)) = true) := by simpa using hn
    simp only [hn']
    by_cases h0 : b = 0
    · simp [h0, Except.map]
    by_cases h1 : a = 1
    · simp [h0, h1, Except.map]
    by_cases hb1 : b = 1
    · subst hb1; simp [Except.map, squaredExp, h1]; rw [sqLoop]; simp
    by_cases hb2 : b = 2
    · subst hb2; simp [Except.map, squaredExp, h1]; rw [sqLoop, sqLoop]; simp [wrap_idem]
    simp [h0, h1, hb1, hb2, Except.map]

/-- PROP intarith.power.is_wrapped_power_8bit : PROVEN
Source: the "Overflow errors" section of the user guide, which says that `numpy.power` wraps at the width of the type. For every int8 and uint8 base and every exponent from 0 to 255 that the type can hold, the array loop gives `a ^ b` reduced to the type. Checked with `native_decide`, which trusts the compiler. -/
theorem power_is_wrapped_power_8bit :
    ([IntTy.i8, IntTy.u8].all fun t => (all8 t).all fun a => ((all8 t).filter (· ≥ 0)).all fun b =>
      powerArrayElem t a b == .ok (t.wrap (a ^ b.toNat))) = true := by
  native_decide -- exhaustive check over about 49000 pairs, trusts the compiler

/-- PROP intarith.power.scalar_warns_on_overflow : REFUTED
Source: `doc/source/reference/arrays.promotion.rst`, "NumPy warns when overflows occur for scalars, but not for arrays". The scalar multiply `np.int8(100) * np.int8(100)` reports an overflow (`scalarmath.c.src:122`), but `np.int8(100) ** np.int8(2)` returns the same wrapped value 16 with status 0, because `@name@_ctype_power` (`scalarmath.c.src:244-264`) never checks for overflow. -/
theorem power_scalar_warns_on_overflow_refuted :
    ¬ (∀ a : Int, IntTy.i8.inRange a → powerScalar .i8 a 2 = .ok (multiplyScalar .i8 a a)) := by
  intro h
  have := h 100 (by decide)
  unfold powerScalar squaredExp at this
  rw [sqLoop, sqLoop] at this
  revert this
  decide

/-! ## gcd and lcm -/

/-- PROP intarith.gcd.loop_is_gcd : PROVEN
Source: `npy_gcdu` at `npy_math_internal.h.src:630`. The Euclidean loop computes the greatest common divisor of its unsigned arguments. -/
theorem gcdLoop_is_gcd (a b : Nat) : gcdLoop a b = Nat.gcd a b := gcdLoop_eq a b

/-- PROP intarith.gcd.commutative : PROVEN
Source: `gcd(x1, x2) = gcd(x2, x1)`, which users rely on. -/
theorem gcd_comm (t : IntTy) (a b : Int) : gcdElem t a b = gcdElem t b a := by
  simp only [gcdElem, gcdLoop_eq, Nat.gcd_comm]

/-- PROP intarith.gcd.nonnegative : REFUTED
Source: `numpy.gcd` docs, "Returns the greatest common divisor of ``|x1|`` and ``|x2|``". `np.gcd(np.int8(-128), np.int8(0))` is -128, because the gcd 128 does not fit in int8 and the cast at `npy_math_internal.h.src:667` and `loops.c.src:571` wraps it. This is the documented integer overflow wrap, so it is not filed as a bug. -/
theorem gcd_nonneg_refuted :
    ¬ (∀ (t : IntTy) (a b : Int), t.inRange a → t.inRange b → gcdElem t a b ≥ 0) := by
  intro h
  have := h .i8 (-128) 0 (by decide) (by decide)
  simp only [gcdElem, gcdLoop_eq] at this
  revert this
  decide

/-! ## Shifts -/

theorem two_pow_dvd (k n : Nat) (h : k ≤ n) : (2 : Int) ^ k ∣ (2 : Int) ^ n := by
  have e : (2 : Int) ^ n = (2 : Int) ^ k * (2 : Int) ^ (n - k) := by
    rw [← Int.pow_add]; congr 1; omega
  rw [e]; exact Int.dvd_mul_right _ _

/-- PROP intarith.left_shift.is_wrapped_multiplication : PROVEN
Source: `numpy.left_shift` docs, "this operation is equivalent to multiplying `x1` by ``2**x2``". For a non-negative shift the result is `x1 * 2 ** x2` reduced to the type, also for shifts at or past the bit width (`npy_math_internal.h.src:685`). -/
theorem lshift_is_wrapped_mul (t : IntTy) (a b : Int) (hb : 0 ≤ b) (hbits : 1 ≤ t.bits) :
    lshift t a b = t.wrap (a * 2 ^ b.toNat) := by
  unfold lshift
  by_cases hlt : b < t.bits
  · simp [hb, hlt]
  · simp only [hlt, decide_false, Bool.and_false, Bool.false_eq_true, ite_false]
    have hd : (2 : Int) ^ t.bits ∣ a * 2 ^ b.toNat :=
      Int.dvd_trans (two_pow_dvd t.bits b.toNat (by omega)) (Int.dvd_mul_left _ _)
    have h0 := Int.emod_eq_zero_of_dvd hd
    have hpos : (2 : Int) / 2 ≤ (2 : Int) ^ t.bits / 2 := by
      apply Int.ediv_le_ediv (by decide)
      obtain ⟨k, hk⟩ : ∃ k, t.bits = k + 1 := ⟨t.bits - 1, by omega⟩
      rw [hk, Int.pow_succ]
      have : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)
      omega
    unfold IntTy.wrap wrapSigned wrapUnsigned
    cases t.signed <;> simp only [h0] <;> simp <;> omega

/-- PROP intarith.right_shift.is_floor_division_in_width : PROVEN
Source: `numpy.right_shift` docs, "this operation is equivalent to dividing `x1` by ``2**x2``". For shifts from 0 to one below the bit width the result is the floor of `x1 / 2 ** x2` (`npy_math_internal.h.src:695`). -/
theorem rshift_is_floor_div (t : IntTy) (a b : Int) (hb : 0 ≤ b) (hlt : b < t.bits) :
    rshift t a b = a / 2 ^ b.toNat := by
  simp [rshift, hb, hlt, Int.shiftRight_eq_div_pow]

/-- PROP intarith.right_shift.past_width_keeps_sign : PROVEN
Source: the comment "preserve the sign bit" at `npy_math_internal.h.src:703`. A shift at or past the bit width gives -1 for a negative signed value and 0 otherwise, which is the floor of `x1 / 2 ** x2` for every value of the type. -/
theorem rshift_past_width (t : IntTy) (a b : Int) (hb : t.bits ≤ b) :
    rshift t a b = (if t.signed && a < 0 then -1 else 0) := by
  have : ¬ b < t.bits := by omega
  simp [rshift, this]

/-- PROP intarith.right_shift.negative_amount_is_sign_fill : PROVEN
Source: the TODO at `loops_autovec.dispatch.c.src:22` says negative shifts are undefined in C. The cast to `size_t` in `npy_rshift` makes a negative amount behave like an amount past the width, so `np.right_shift(x, -1)` is -1 or 0. -/
theorem rshift_negative (t : IntTy) (a b : Int) (hb : b < 0) :
    rshift t a b = (if t.signed && a < 0 then -1 else 0) := by
  have : ¬ 0 ≤ b := by omega
  simp [rshift, this]

/-! ## absolute and sign -/

/-- PROP intarith.absolute.scalar_matches_array_value : PROVEN
Source: consistency between the builtin `abs` on a NumPy scalar (`scalarmath.c.src:610`) and `np.absolute` on arrays (`loops_autovec.dispatch.c.src:220`). The values agree for every value of the type, `abs(MIN)` included. Only the scalar path reports the overflow of `abs(MIN)`, which the promotion docs describe ("NumPy warns when overflows occur for scalars, but not for arrays"). -/
theorem abs_scalar_value_eq_array (t : IntTy) (a : Int) (hbits : 1 ≤ t.bits)
    (hr : t.inRange a = true) : (absScalar t a).1 = absArray t a := by
  unfold absScalar absArray
  cases hs : t.signed
  · simp
  · simp only [IntTy.inRange, IntTy.minVal, IntTy.maxVal, hs, ite_true, Bool.and_eq_true,
      decide_eq_true_eq] at hr
    simp only [ite_true, IntTy.wrap, hs]
    by_cases hm : a = t.minVal
    · simp only [IntTy.minVal, hs, ite_true] at hm
      subst hm
      have : ¬ (-(2 : Int) ^ (t.bits - 1) ≥ 0) := by
        have : (0 : Int) < 2 ^ (t.bits - 1) := Int.pow_pos (by decide)
        omega
      simp only [IntTy.minVal, hs, beq_self_eq_true, ite_true, this, ite_false, Int.neg_neg,
        wrapSigned_half t.bits hbits]
    · have hne : (a == t.minVal) = false := by simpa using hm
      simp only [hne, Bool.false_eq_true, ite_false]
      simp only [IntTy.minVal, hs, ite_true] at hm
      by_cases h0 : a ≥ 0
      · have : ¬ a < 0 := by omega
        simp [h0, this]
      · have : a < 0 := by omega
        simp only [this, ite_true, h0, ite_false]
        rw [wrapSigned_of_range t.bits (-a) hbits (by omega) (by omega)]

/-- PROP intarith.absolute.nonnegative : REFUTED
Source: `numpy.absolute` docs, "Calculate the absolute value element-wise". `np.absolute(np.int8(-128))` is -128 because 128 does not fit in int8. This is the documented integer overflow wrap, so it is not filed as a bug. -/
theorem abs_nonneg_refuted :
    ¬ (∀ (t : IntTy) (a : Int), t.inRange a → absArray t a ≥ 0) := by
  intro h
  have := h .i8 (-128) (by decide)
  revert this
  decide

/-- PROP intarith.sign.matches_docstring : PROVEN
Source: `numpy.sign` docs, "The `sign` function returns ``-1 if x < 0, 0 if x==0, 1 if x > 0``". The loops at `loops_autovec.dispatch.c.src:126` and `:226` do this for every value, since unsigned values are never negative. -/
theorem sign_matches_docstring (t : IntTy) (a : Int) (hr : t.inRange a = true) :
    signElem t a = (if a < 0 then -1 else if a = 0 then 0 else 1) := by
  unfold signElem
  cases hs : t.signed
  · simp only [IntTy.inRange, IntTy.minVal, hs, Bool.false_eq_true, ite_false, Bool.and_eq_true,
      decide_eq_true_eq] at hr
    by_cases h : a > 0
    · have : ¬ a < 0 := by omega
      have : ¬ a = 0 := by omega
      simp [*]
    · have : a = 0 := by omega
      simp [this]
  · by_cases h : a > 0
    · have : ¬ a < 0 := by omega
      have : ¬ a = 0 := by omega
      simp [*]
    · by_cases h2 : a < 0
      · simp [*]
      · have : a = 0 := by omega
        simp [this]

end NumpyLean.IntArith
