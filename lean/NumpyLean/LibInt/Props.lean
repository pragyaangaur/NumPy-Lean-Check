import NumpyLean.LibInt.Model

/-
Properties of the integer library models. Each property carries a status line that `scripts/check_props.py` counts.

Status values: PROVEN (the theorem states the property), REFUTED (the theorem states the negation and gives a counterexample), OPEN (stated in a comment only).

Some properties are checked over a bounded universe with `native_decide`, because the general statement needs lemmas about digit lists, sorting or division that core Lean does not have. Each such use says so in a comment, since `native_decide` trusts the compiler.
-/
namespace NumpyLean.LibInt

/-! ## arange -/

/-- The length of Python `range(a, b, s)` for `s ≠ 0`. -/
def pyRangeLen (a b s : Int) : Int := max 0 (-((a - b).fdiv s))

/-- PROP libint.arange.length_matches_range : REFUTED
Source: the `numpy.arange` docstring, "For integer arguments the function is roughly equivalent to the Python built-in range", and the `stop` parameter, which may be included only "in some cases where `step` is not an integer". The length is the ceiling of a double (`ctors.c:3213` and `3268`), so `np.arange(0, 2**53 + 1, 2**53)` has one element where `range` has two. -/
theorem arange_length_matches_range_refuted :
    ¬ (∀ a b s o, s ≠ 0 → arangeObj a b (some s) none = .ok o → o.length = pyRangeLen a b s) := by
  intro h
  have := h 0 (2 ^ 53 + 1) (2 ^ 53) ⟨.int 64 true, 1, 0, 0⟩ (by decide +kernel) (by decide +kernel)
  exact absurd this (by decide +kernel)

/-- `arangeOk` checks that the model gives the `range` length and the `range` values for one case. -/
def arangeSmallOk (a b s : Int) : Bool :=
  match arangeObj a b (some s) none with
  | .ok o => o.dtype == .int 64 true && o.length == pyRangeLen a b s &&
      o.values == (List.range (pyRangeLen a b s).toNat).map (fun (i : Nat) => a + s * i)
  | .error _ => false

/-- PROP libint.arange.small_matches_range : PROVEN
Source: the same docstring sentence. For every `start` and `stop` in `[-40, 40]` and every nonzero `step` in `[-7, 7]`, the dtype is `int64`, and the length and values equal those of `range`. The universe has 91,854 cases, too many for `decide`, so this uses `native_decide`, which trusts the compiler. -/
theorem arange_small_matches_range :
    ((List.range 81).all fun i => (List.range 81).all fun j => (List.range 15).all fun k =>
      let s : Int := (k : Int) - 7
      s == 0 || arangeSmallOk ((i : Int) - 40) ((j : Int) - 40) s) = true := by
  native_decide

/-- PROP libint.arange.default_dtype_distinct_values : REFUTED
Source: the `step` parameter of the `numpy.arange` docstring, "For any output `out`, this is the distance between two adjacent values, `out[i+1] - out[i]`", and the `dtype` parameter, "infer the data type from the other input arguments". Discovery starts from `intp` (`ctors.c:3317`), so Python integers in the `uint64` range promote to `float64`, and `np.arange(2**63, 2**63 + 3)` gives three equal values. -/
theorem arange_default_dtype_distinct_refuted :
    ¬ (∀ a b o, arangeObj a b none none = .ok o → o.values.Nodup) := by
  intro h
  have := h (2 ^ 63) (2 ^ 63 + 3) ⟨.float64, 3, 2 ^ 63, 2 ^ 63⟩ (by decide +kernel)
  exact absurd this (by decide +kernel)

/-- PROP libint.arange.length_fits_intp : PROVEN
Source: `_arange_safe_ceil_to_intp` at `ctors.c:3069`, whose purpose is to "check for overflow". A length that passes the check is at most `NPY_MAX_INTP`, including the boundary value `2^63`, which the model casts as arm64 does. -/
theorem arangeCeil_le_intpMax (d s c : Int) (h : arangeCeil d s = some c) : c ≤ intpMax := by
  unfold arangeCeil at h
  simp only [intpMax] at *
  split at h
  · cases h; omega
  · split at h
    · split at h <;> (cases h; omega)
    · split at h
      · cases h
      · split at h <;> (cases h; omega)

/-- PROP libint.arange.length_nonnegative : PROVEN
Source: the clamp `if (length <= 0) length = 0` at `ctors.c:3387`. Every result has a non-negative length. -/
theorem arangeObj_length_nonneg (a b : Int) (s : Option Int) (d : Option ADType) (o : ArangeOut)
    (h : arangeObj a b s d = .ok o) : 0 ≤ o.length := by
  unfold arangeObj at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' (first | split at h | (cases h; first | omega | (simp only []; omega)))
  all_goals first | cases h | omega

/-! ## binary_repr and base_repr -/

/-- PROP libint.binary_repr.nonempty : REFUTED
Source: the `width` parameter of the `numpy.binary_repr` docstring, "If the width value is insufficient, an error is raised". Zero is handled by `'0' * (width or 1)` at `numeric.py:2074`, so `binary_repr(0, width=-1)` returns the empty string, while `binary_repr(1, width=0)` raises. -/
theorem binaryRepr_nonempty_refuted :
    ¬ (∀ n w s, binaryRepr n w = .ok s → s ≠ "") := by
  intro h
  exact h 0 (some (-1)) "" (by decide +kernel) rfl

/-- PROP libint.binary_repr.positive_is_python_bin : PROVEN
Source: the `numpy.binary_repr` docstring, "Return the binary representation of the input number as a string", and Python `f'{num:b}'` at `numeric.py:2078`. Without a width a positive number gives exactly Python's binary digits. -/
theorem binaryRepr_positive (n : Int) (hn : 0 < n) : binaryRepr n none = .ok (binStr n.toNat) := by
  unfold binaryRepr checkWidth
  have h0 : n ≠ 0 := by omega
  simp only [h0, hn, ite_false, ite_true, zeros, Int.sub_self, Int.toNat_zero]
  rfl

/-- Parse a string of binary digits. -/
def parseBin (s : String) : Int := s.toList.foldl (fun acc c => 2 * acc + if c = '1' then 1 else 0) 0

/-- `binaryReprOk` checks the round trip of one case: the digits give back the number, directly for non-negative numbers and numbers without a width, and as two's complement of the string length for negative numbers with a width. -/
def binaryReprOk (n : Int) (w : Option Int) : Bool :=
  match binaryRepr n w with
  | .error _ => true
  | .ok s =>
    if n ≥ 0 then parseBin s == n && (w.isNone || n == 0 || (s.length : Int) == max ((binStr n.toNat).length : Int) (w.getD 0))
    else match w with
      | none => s == "-" ++ binStr n.natAbs
      | some _ => parseBin s - 2 ^ s.length == n

/-- PROP libint.binary_repr.round_trip_small : PROVEN
Source: the `numpy.binary_repr` docstring, "In a two's-complement system negative numbers are represented by the two's complement of the absolute value." For every number in `[-300, 300]` and every width in `None` and `[0, 12]`, an accepted result reads back as the number, and a positive number has length `max(bits, width)`. The universe has 8,427 cases, which is too slow for `decide`, so this uses `native_decide`, which trusts the compiler. -/
theorem binaryRepr_round_trip_small :
    ((List.range 601).all fun i =>
      let n : Int := (i : Int) - 300
      binaryReprOk n none && (List.range 13).all fun w => binaryReprOk n (some w)) = true := by
  native_decide

/-- PROP libint.base_repr.padding_adds_zeros : REFUTED
Source: the `padding` parameter of the `numpy.base_repr` docstring, "Number of zeros padded on the left. Default is 0 (no padding)." The padding replaces the `'0'` of a zero because `res or '0'` at `numeric.py:2160` only applies to an empty list, so `base_repr(0, padding=2)` is `'00'` while `base_repr(1, padding=2)` is `'001'`. -/
theorem baseRepr_padding_refuted :
    ¬ (∀ n b p s s0, 0 ≤ p → baseRepr n b p = .ok s → baseRepr n b 0 = .ok s0 → s.length = s0.length + p.toNat) := by
  intro h
  have := h 0 10 2 "00" "0" (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact absurd this (by decide +kernel)

/-- Parse a string of base `b` digits with an optional leading minus sign. -/
def parseBase (b : Nat) (s : String) : Int :=
  let digit := fun (c : Char) => (digitChars.idxOf c : Int)
  match s.toList with
  | '-' :: rest => -(rest.foldl (fun acc c => b * acc + digit c) 0)
  | cs => cs.foldl (fun acc c => b * acc + digit c) 0

/-- PROP libint.base_repr.round_trip_small : PROVEN
Source: the `numpy.base_repr` docstring, "Return a string representation of a number in the given base system", read back with Python `int(s, base)`. For every number in `[-200, 200]`, every base in `[2, 36]` and every padding in `[0, 3]`, the string reads back as the number. The universe has 59,148 cases, too many for `decide`, so this uses `native_decide`, which trusts the compiler. -/
theorem baseRepr_round_trip_small :
    ((List.range 401).all fun i => (List.range 35).all fun j => (List.range 4).all fun p =>
      let n : Int := (i : Int) - 200
      let b := j + 2
      match baseRepr n b p with
      | .ok s => parseBase b s == n
      | .error _ => false) = true := by
  native_decide

/-! ## packbits and unpackbits -/

/-- PROP libint.check_axis.in_range : PROVEN
Source: `PyArray_CheckAxis` at `ctors.c:2886`, whose result is used as an axis of the array. An accepted axis is a valid axis of the possibly flattened shape. -/
theorem checkAxis_in_range (shape : List Int) (axis : Option Int) (s : List Int) (a : Nat)
    (h : checkAxis shape axis = .ok (s, a)) : a < s.length := by
  unfold checkAxis at h
  split at h
  next shp ax heq =>
    by_cases hc : ax < -(shp.length : Int) ∨ ax ≥ shp.length
    · rw [ite_eq_left hc] at h; cases h
    · rw [ite_eq_right hc] at h
      cases h
      split <;> omega

/-- The bits of a byte list as unpacked, most significant first for big order. -/
def packRoundOk (bits : List Int) (big : Bool) : Bool :=
  match packbits [bits.length] bits true none big with
  | .ok (sh, packed) =>
    match unpackbits sh packed true none (some bits.length) big with
    | .ok (_, some out) => out == bits
    | _ => false
  | .error _ => false

/-- All lists of 0 and 1 of length `n`. -/
def bitLists : Nat → List (List Int)
  | 0 => [[]]
  | n + 1 => (bitLists n).flatMap fun l => [0 :: l, 1 :: l]

/-- PROP libint.packbits.unpack_round_trip_small : PROVEN
Source: the `count` parameter of the `numpy.unpackbits` docstring, "provided as a way of undoing the effect of packing a size that is not a multiple of eight". For every bit list of length at most 12 and both bit orders, `unpackbits(packbits(x), count=len(x))` gives back `x`. The universe has 16,382 lists, too many for `decide`, so this uses `native_decide`, which trusts the compiler. -/
theorem packbits_round_trip_small :
    ((List.range 13).all fun n => (bitLists n).all fun l => packRoundOk l true && packRoundOk l false) = true := by
  native_decide

/-- PROP libint.unpackbits.count_pads_with_zeros : REFUTED
Source: the `count` parameter of the `numpy.unpackbits` docstring, "Counts larger than the available number of bits will add zero padding to the output." For an empty input the iterator of `PyArray_IterAllButAxis` has size 0 (`iterators.c:261`), so the loop at `compiled_base.c:1969` never runs and the output of shape `(8, 1)` for `np.unpackbits(np.empty((0, 1), np.uint8), axis=0, count=8)` stays uninitialised. -/
theorem unpackbits_pads_refuted :
    ¬ (∀ sh d a c big r, unpackbits sh d true a (some c) big = .ok r → r.2.isSome) := by
  intro h
  have := h [0, 1] [] (some 0) 8 true ([8, 1], none) (by decide +kernel)
  exact absurd this (by decide +kernel)

/-- PROP libint.unpackbits.axis_length_no_wrap : REFUTED
Source: the same docstring. The axis length is multiplied by 8 in `npy_intp` without an overflow check (`compiled_base.c:1915`), so for the empty array of shape `(2**61, 0)` the unpacked axis wraps to 0 instead of raising. -/
theorem unpackbits_wrap_refuted :
    ¬ (∀ n m d r, unpackbits [n, m] d true (some 0) none true = .ok r → r.1.head? = some (8 * n)) := by
  intro h
  have := h (2 ^ 61) 0 [] ([0, 0], some []) (by decide +kernel)
  exact absurd this (by decide +kernel)

/-! ## isin -/

/-- PROP libint.isin.kinds_agree : REFUTED
Source: the `kind` parameter of the `numpy.isin` docstring, "This will not affect the final result". The sort path concatenates `int64` and `uint64` arrays into `float64` (`_arraysetops_impl.py:933`), so `2**62 + 1` matches `2**62` there, while the table path and the loop compare exactly. The sort path needs a list of `mergeSort`, which `decide` cannot evaluate, so this uses `native_decide`, which trusts the compiler. -/
theorem isin_kinds_agree_refuted :
    ¬ (∀ a1 a2 d1 d2 inv, isin a1 a2 d1 d2 .sort inv = isin a1 a2 d1 d2 .table inv) := by
  intro h
  have := h [2 ^ 62 + 1] (List.replicate 10 (2 ^ 62)) .i64 .u64 false
  exact absurd this (by native_decide)

/-- PROP libint.isin.matches_membership : REFUTED
Source: the Notes of the `numpy.isin` docstring, "`isin` is an element-wise function version of the python keyword `in`". With the default `kind`, a `uint64` test array whose range is too large for the table goes to the sort path, and the same double comparison gives `True` for `2**62 + 1 in [2**62, 0, ...]`. This uses `native_decide` for the same reason as above. -/
theorem isin_membership_refuted :
    ¬ (∀ a1 a2 d1 d2, isin a1 a2 d1 d2 .auto false = .ok (a1.map fun x => a2.contains x)) := by
  intro h
  have := h [2 ^ 62 + 1] (0 :: List.replicate 10 (2 ^ 62)) .i64 .u64
  exact absurd this (by native_decide)

/-- PROP libint.isin.table_accepts_integers : REFUTED
Source: the `kind` parameter of the `numpy.isin` docstring, "'table' ... is only available for boolean and integer arrays". The range check at `_arraysetops_impl.py:845` compares `max - min` with the largest value of the dtype, so `kind='table'` raises for an `int8` test array holding -128 and 127, although the table would have only 256 entries. The error message names the condition, so this is recorded without a bug record. -/
theorem isin_table_int8_refuted :
    ¬ (∀ a1 a2, ∃ r, isin a1 a2 .i8 .i8 .table false = .ok r) := by
  intro h
  obtain ⟨r, hr⟩ := h [5] [-128, 127]
  have he : isin [5] [-128, 127] .i8 .i8 .table false = .error .tableRange := by decide +kernel
  rw [he] at hr
  cases hr

/-- The test arrays of `isin_invert_small`: values that collide as doubles, with lengths on both sides of the loop limit. -/
def isinInvertCases : List (List Int × List Int × IsinKind × IDType × IDType) :=
  let vals : List Int := [0, 2 ^ 62, 2 ^ 62 + 1]
  let l1 : List (List Int) := [[], [0], [2 ^ 62], [2 ^ 62 + 1], [2 ^ 62, 2 ^ 62 + 1], [0, 2 ^ 62 + 1]]
  let l2 : List (List Int) := vals.flatMap fun v => [[v], List.replicate 12 v, 0 :: List.replicate 11 v]
  l1.flatMap fun a1 => l2.flatMap fun a2 => [IsinKind.auto, .sort, .table].flatMap fun k =>
    [(IDType.i64, IDType.u64), (.u64, .i64), (.i64, .i64)].map fun (d1, d2) => (a1, a2, k, d1, d2)

def isinInvertOk : List Int × List Int × IsinKind × IDType × IDType → Bool
  | (a1, a2, k, d1, d2) =>
    match isin a1 a2 d1 d2 k false, isin a1 a2 d1 d2 k true with
    | .ok r, .ok s => s == r.map (!·)
    | .error _, .error _ => true
    | _, _ => false

/-- PROP libint.isin.invert_small : PROVEN
Source: the `invert` parameter of the `numpy.isin` docstring, "`np.isin(a, b, invert=True)` is equivalent to (but faster than) `np.invert(np.isin(a, b))`". Checked for all three kinds on every pair from `isinInvertCases`, lists of length at most 2 and 12 over values that collide as doubles, with `int64` and `uint64` mixed. The universe has 486 cases with sort paths that `decide` cannot evaluate, so this uses `native_decide`, which trusts the compiler. -/
theorem isin_invert_small : isinInvertCases.all isinInvertOk = true := by
  native_decide

/-! ## digitize -/

/-- PROP libint.digitize.decreasing_bins : REFUTED
Source: the `numpy.digitize` docstring, which for decreasing bins and `right=False` returns `i` with `bins[i-1] > x >= bins[i]`, that is the number of bins greater than `x`. The direction is decided on doubles (`compiled_base.c:35`), so the strictly decreasing `int64` bins `[2**53 + 1, 2**53]` are taken as increasing and `x = 2**53` gets 2 instead of 1. -/
theorem digitize_decreasing_refuted :
    ¬ (∀ x b0 b1, b0 > b1 → digitize [x] [b0, b1] false = .ok [(([b0, b1].filter (· > x)).length : Int)]) := by
  intro h
  have := h (2 ^ 53) (2 ^ 53 + 1) (2 ^ 53) (by decide +kernel)
  exact absurd this (by decide +kernel)

/-- PROP libint.digitize.rejects_non_monotonic : REFUTED
Source: the Raises section of the `numpy.digitize` docstring, "ValueError If `bins` is not monotonic." The `int64` bins `[2**53, 2**53 + 1, 2**53]` are not monotonic but have equal doubles, so they are accepted. -/
theorem digitize_non_monotonic_refuted :
    ¬ (∀ x, digitize x [2 ^ 53, 2 ^ 53 + 1, 2 ^ 53] false = .error .notMonotonic) := by
  intro h
  exact absurd (h [0]) (by decide +kernel)

/-- `digitizeOk` compares the model with the docstring rule for increasing bins: the number of bins at most `x` for `right=False` and below `x` for `right=True`. -/
def digitizeOk (x : Int) (bins : List Int) (right : Bool) : Bool :=
  digitize [x] bins right == .ok [((bins.filter fun b => if right then b < x else b ≤ x).length : Int)]

/-- All non-decreasing lists of length `n` over `[0, k)`. -/
def sortedLists (k : Nat) : Nat → List (List Int)
  | 0 => [[]]
  | n + 1 => (sortedLists k n).flatMap fun l =>
      ((List.range k).map (fun (v : Nat) => (v : Int))).filterMap fun v =>
        if l.all (· ≤ v) then some (l ++ [v]) else none

/-- PROP libint.digitize.increasing_small : PROVEN
Source: the `numpy.digitize` docstring, `bins[i-1] <= x < bins[i]` for increasing bins and `right=False`, and `bins[i-1] < x <= bins[i]` for `right=True`. Checked for every non-decreasing list of up to four bins over `[0, 5)` and every `x` in `[-1, 5]`. The universe has 1,764 lists of bins and 24,696 cases, which is too slow for `decide`, so this uses `native_decide`, which trusts the compiler. -/
theorem digitize_increasing_small :
    ((List.range 5).all fun n => (sortedLists 5 n).all fun bins => (List.range 7).all fun i =>
      digitizeOk ((i : Int) - 1) bins false && digitizeOk ((i : Int) - 1) bins true) = true := by
  native_decide

/-! ## bincount -/

/-- PROP libint.bincount.indices_in_bounds : REFUTED
Source: the `numpy.bincount` docstring, "The length of `out` is equal to `np.amax(x)+1`", and memory safety of the counting loop `ians[numbers[i]] += 1` at `compiled_base.c:236`. For `x = [2**63 - 1]` the length `mx + 1` at `compiled_base.c:222` wraps to `-2**63`, the `minlength` comparison replaces it by 0, and the loop then writes to element `2**63 - 1` of an empty buffer. -/
theorem bincount_in_bounds_refuted :
    ¬ (∀ l m cap n cs, bincount l m cap = .ok (n, cs) → ∀ x ∈ l, x < n) := by
  intro h
  have := h [intpMax] 0 64 0 [] (by decide +kernel) intpMax (by simp)
  exact absurd this (by decide +kernel)

end NumpyLean.LibInt
