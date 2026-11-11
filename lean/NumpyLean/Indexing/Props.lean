import NumpyLean.Indexing.Model

/-
Properties of the indexing models. Each property carries a status line that `scripts/check_props.py` counts.

Status values: PROVEN (the theorem states the property), REFUTED (the theorem states the negation and gives a counterexample), OPEN (stated in a comment only).
-/
namespace NumpyLean.Indexing

/-- PROP indexing.check_and_adjust_index.result_in_range : PROVEN
Source: the comment "Check that index is valid, taking into account negative indices" at `common.h:170`. An accepted index is a valid position on the axis. -/
theorem checkAndAdjustIndex_in_range (i n k : Int) (h : checkAndAdjustIndex i n = .ok k) :
    0 ≤ k ∧ k < n := by
  unfold checkAndAdjustIndex at h
  split at h
  · cases h
  · split at h <;> (cases h; omega)

/-- PROP indexing.check_and_adjust_index.accepts_python_range : PROVEN
Source: the Python rule for sequence indices, which `numpy` indexing follows. Every index in `[-n, n)` is accepted and is mapped to its Python position. -/
theorem checkAndAdjustIndex_accepts (i n : Int) (h1 : -n ≤ i) (h2 : i < n) :
    checkAndAdjustIndex i n = .ok (if i < 0 then i + n else i) := by
  unfold checkAndAdjustIndex
  have : ¬ (i < -n ∨ i ≥ n) := by omega
  simp only [this, ite_false]
  split <;> rfl

/-- A non-empty result of `adjustIndices` starts inside the axis. The step does not matter. -/
theorem adjustIndices_start (length a b s : Int) (hn : 0 ≤ length)
    (h : 0 < (adjustIndices length a b s).2.2) :
    0 ≤ (adjustIndices length a b s).1 ∧ (adjustIndices length a b s).1 < length := by
  simp only [adjustIndices, adjustBound] at h ⊢
  revert h
  repeat' split
  all_goals (intro h; omega)

/-- PROP indexing.slice.start_in_range : PROVEN
Source: `PySlice_AdjustIndices` in CPython, whose result is used at `mapping.c:910` as `data_ptr += stride * start`. A non-empty slice view starts at a valid position of the axis. -/
theorem sliceView_start_in_range (n : Int) (a b s : Option Int) (st sp len : Int)
    (hn : 0 ≤ n) (h : sliceView n a b s = .ok (st, sp, len)) (hl : 0 < len) :
    0 ≤ st ∧ st < n := by
  unfold sliceView at h
  cases hu : sliceUnpack a b s with
  | error e => simp [hu, bind, Except.bind] at h
  | ok v =>
    obtain ⟨a', b', st'⟩ := v
    rcases hadj : adjustIndices n a' b' st' with ⟨x, y, z⟩
    have key := adjustIndices_start n a' b' st' hn
    rw [hadj] at key
    simp only [hu, hadj, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h; omega
    · cases h; exact key hl

/-- PROP indexing.slice.length_nonnegative : PROVEN
Source: `get_view_from_index` at `mapping.c:904-912`, which stores the slice length as a dimension of the view. The stored length is never negative. -/
theorem sliceView_len_nonneg (n : Int) (a b s : Option Int) (st sp len : Int)
    (h : sliceView n a b s = .ok (st, sp, len)) : 0 ≤ len := by
  unfold sliceView at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · simp only [pure, Except.pure] at h
    split at h
    · cases h; omega
    · cases h; omega

/-- PROP indexing.wrap.result_in_range : PROVEN
Source: the `numpy.take` documentation, "'wrap' – wrap around". When the wrap loop ends on a non-empty axis, the index it gives is a valid position. -/
theorem wrapLoop_in_range (t m k : Int) (it : Nat) (hm : 0 < m) (h : wrapLoop t m = some (k, it)) :
    0 ≤ k ∧ k < m := by
  unfold wrapLoop at h
  split at h
  · split at h
    · cases h
    · cases h; exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ hm⟩
  · split at h
    · split at h
      · cases h
      · cases h; exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ hm⟩
    · cases h; omega

/-- PROP indexing.take.clip_never_errors : PROVEN
Source: the `numpy.take` documentation, "'clip' – clip to the range". On a non-empty axis, take with mode clip never raises and always reads a valid position. -/
theorem take1_clip_ok (n idx : Int) (hn : 0 < n) :
    ∃ k, take1 n idx .clip = .ok k ∧ 0 ≤ k ∧ k < n := by
  refine ⟨clipIndex (wrap64 idx) n, ?_, ?_⟩
  · unfold take1
    have : n ≠ 0 := by omega
    simp [this]
  · unfold clipIndex
    split
    · omega
    · split <;> omega

/-- PROP indexing.take.wrap_terminates : REFUTED
Source: the `numpy.take` documentation, "'wrap' – wrap around", which promises a result for every index. The loop at `item_selection.c:97-108` adds or subtracts the axis length one step at a time, so it never ends when the axis length is zero. `np.take(np.zeros((0, 0)), [0], axis=0, mode='wrap')` reaches it, because the output has size zero and the empty-axis check at `item_selection.c:345` does not fire. -/
theorem wrapLoop_terminates_refuted :
    ¬ (∀ t m : Int, 0 ≤ m → 0 ≤ t → (wrapLoop t m).isSome) := by
  intro h
  have := h 0 0 (by decide) (by decide)
  exact absurd this (by decide)

/-- PROP indexing.take.wrap_iterations_bounded : REFUTED
Source: the same loop. The number of iterations grows with the index divided by the axis length, so `np.take(np.arange(3), [2**62], mode='wrap')` runs about `1.5e18` iterations with the GIL released. The property states that the loop needs at most `2**32` iterations. -/
theorem wrapLoop_iterations_refuted :
    ¬ (∀ (t m k : Int) (it : Nat), 0 < m → wrapLoop t m = some (k, it) → it ≤ 2 ^ 32) := by
  intro h
  have := h (2 ^ 62) 3 1 1537228672809129301 (by decide) (by decide)
  exact absurd this (by decide)

/-- PROP indexing.take.clip_matches_documented_clip : REFUTED
Source: the `numpy.take` documentation, "'clip' – clip to the range (all indices that are too large are replaced by the index that addresses the last element along that axis)". A `uint64` index of `2**64 - 1` is too large but is cast to `intp` with `same_kind` casting at `item_selection.c:252`, becomes `-1`, and is clipped to `0`. -/
theorem take1_clip_uint64_refuted :
    ¬ (∀ n idx : Int, 0 < n → 0 ≤ idx → idx < 2 ^ 64 → take1 n idx .clip = .ok (min idx (n - 1))) := by
  intro h
  have := h 3 (2 ^ 64 - 1) (by decide) (by decide) (by decide)
  exact absurd this (by decide)

/-- PROP indexing.put.raise_rejects_out_of_bounds : REFUTED
Source: the `numpy.put` documentation, "'raise' – raise an error (default)" for indices out of range. With an empty `values`, `PyArray_PutTo` returns at `item_selection.c:424` before it looks at the indices, so `np.put(np.arange(3), [100], [])` succeeds. -/
theorem put1_raise_refuted :
    ¬ (∀ n idx nv : Int, 0 < n → (idx < -n ∨ idx ≥ n) → put1 n idx nv .raise = .error .outOfBounds) := by
  intro h
  have := h 3 100 0 (by decide) (by decide)
  exact absurd this (by decide)

/-- PROP indexing.int_index.one_error_for_too_large : REFUTED
Source: plain consistency with Python sequences, which raise `IndexError` for every integer that does not fit in `Py_ssize_t`. NumPy raises `OverflowError` for `2**63` and `IndexError` for `2**64`. -/
theorem pyIntIndex_error_kind_refuted :
    ¬ (∀ n i j : Int, ¬ inIntp i → ¬ inIntp j →
        (pyIntIndex n i = .error .overflow ↔ pyIntIndex n j = .error .overflow)) := by
  intro h
  have := (h 5 (2 ^ 63) (2 ^ 64) (by decide) (by decide)).mp (by decide)
  exact absurd this (by decide)

/-- PROP indexing.ravel_multi_index.inverts_unravel_index : PROVEN
Source: the `numpy.unravel_index` documentation, "See Also: ravel_multi_index". For the shapes `(3, 4)` and `(2, 3, 2)` in both orders, raveling the unraveled index gives the index back. -/
theorem ravel_unravel_34 :
    ∀ v : Fin 12, ∀ f : Bool,
      (do let cs ← (unravelIndex v.val [3, 4] f).mapError (fun _ => RavelErr.invalidEntry)
          ravelMultiIndex cs [3, 4] [.raise, .raise] f) = .ok (v.val : Int) := by
  decide

-- The second shape of the same property.
theorem ravel_unravel_232 :
    ∀ v : Fin 12, ∀ f : Bool,
      (do let cs ← (unravelIndex v.val [2, 3, 2] f).mapError (fun _ => RavelErr.invalidEntry)
          ravelMultiIndex cs [2, 3, 2] [.raise, .raise, .raise] f) = .ok (v.val : Int) := by
  decide

/-- PROP indexing.unravel_index.coords_nonnegative : REFUTED
Source: the `numpy.unravel_index` documentation, "Converts a flat index or array of flat indices into a tuple of coordinate arrays", which are positions in an array of the given shape and so are never negative. `PyArray_IntpConverter` accepts negative entries in `shape`, and `PyArray_OverflowMultiplyList` (`multiarraymodule.c:216`) multiplies them, so `np.unravel_index(5, (-2, -3))` returns `(-1, 2)`. -/
theorem unravel_coords_nonneg_refuted :
    ¬ (∀ (v : Int) (dims cs : List Int), unravelIndex v dims false = .ok cs → ∀ c ∈ cs, 0 ≤ c) := by
  intro h
  have := h 5 [-2, -3] [-1, 2] (by decide) (-1) (by decide)
  exact absurd this (by decide)

/-- PROP indexing.unravel_index.message_reports_input : REFUTED
Source: the error message "index %d is out of bounds for array with size %d" at `compiled_base.c:1324`, which should name the index the user passed. A Python int of `2**63` is cast to `intp` with `same_kind` casting and the message names `-9223372036854775808`. This is a message only and has no bug record. -/
theorem unravel_message_refuted :
    ¬ (∀ (v size w : Int) (dims : List Int), unravelIndex v dims false = .error (.outOfBounds w size) → w = v) := by
  intro h
  have := h (2 ^ 63) 3 (-2 ^ 63) [3] (by decide)
  exact absurd this (by decide)

/-- PROP indexing.ravel_multi_index.result_nonnegative : REFUTED
Source: the `numpy.ravel_multi_index` documentation, "An array of indices into the flattened version of an array of dimensions dims", which are never negative. Negative entries in `dims` are accepted, and the clip and wrap modes then produce negative or out-of-range coordinates, so `np.ravel_multi_index((1, 1), (-2, 3), mode='clip')` returns `-8`. -/
theorem ravel_nonneg_refuted :
    ¬ (∀ (coords dims : List Int) (modes : List ClipMode) (f : Bool) (v : Int),
        ravelMultiIndex coords dims modes f = .ok v → 0 ≤ v) := by
  intro h
  have := h [1, 1] [-2, 3] [.clip, .clip] false (-8) (by decide)
  exact absurd this (by decide)

/-- PROP indexing.ravel_multi_index.clip_matches_documented_clip : REFUTED
Source: the `numpy.ravel_multi_index` documentation, "'clip' – clip to the range". The coordinate `2**63` on an axis of length 3 should clip to 2. `astype_anyint` gives `uint64` and the `same_kind` cast of the iterator (`compiled_base.c:1228`) wraps it to `-2**63`, which clips to 0. -/
theorem ravel_clip_uint64_refuted :
    ¬ (∀ (c d : Int), 0 < d → 0 ≤ c → c < 2 ^ 64 → ravelMultiIndex [c] [d] [.clip] false = .ok (min c (d - 1))) := by
  intro h
  have := h (2 ^ 63) 3 (by decide) (by decide) (by decide)
  exact absurd this (by decide)

/-- PROP indexing.repeat.length_matches_writes : REFUTED
Source: memory safety. `npy_fastrepeat_impl` (`item_selection.c:812-838`) copies `counts[j]` elements for every `j`, so the output allocated by `PyArray_Repeat` must have exactly that many. The length is computed by `total = counts[0] * n` at `item_selection.c:934` or by `total += counts[j]` at `item_selection.c:944`, with no overflow check. For four elements repeated `2**62` times the length wraps to 0 and the copy writes past the end of the buffer. -/
theorem repeat_length_refuted :
    ¬ (∀ (n : Int) (counts : List Int) (t : Int), repeatTotal n counts 8 = .ok t → t = repeatWrites n counts) := by
  intro h
  have := h 4 [2 ^ 62] 0 (by decide)
  exact absurd this (by decide)

/-- PROP indexing.repeat.rejects_negative_counts : REFUTED
Source: the error "repeats may not contain negative values." at `item_selection.c:939`. The check only runs when the counts do not broadcast, so `np.repeat(np.arange(0), -5)` returns an empty array while `np.repeat(np.arange(1), [-5])` with one element and `np.repeat(np.arange(2), [-5, 1])` raise. -/
theorem repeat_negative_refuted :
    ¬ (∀ (n c : Int) (t : Int), c < 0 → repeatTotal n [c] 8 ≠ .ok t) := by
  intro h
  exact h 0 (-5) 0 (by decide) (by decide)

/-- PROP indexing.diagonal.size_bounded : PROVEN
Source: the `numpy.diagonal` documentation. The diagonal of an `r` by `c` array has at most `min(r, c)` elements and never a negative number of them. -/
theorem diagonal2_size (r c s1 off size start step : Int) (hr : 0 ≤ r) (hc : 0 ≤ c)
    (h : diagonal2 r c s1 off = .ok (size, start, step)) : 0 ≤ size ∧ size ≤ r ∧ size ≤ c := by
  unfold diagonal2 at h
  by_cases h1 : off < -(2 : Int) ^ 31 ∨ off ≥ (2 : Int) ^ 31
  · rw [ite_eq_left h1] at h; cases h
  · rw [ite_eq_right h1] at h
    by_cases h2 : off ≥ 0
    · simp only [ite_eq_left h2] at h
      by_cases h3 : c - off < r
      · rw [ite_eq_left h3] at h
        by_cases h4 : c - off < 0
        · rw [ite_eq_left h4] at h; cases h; omega
        · rw [ite_eq_right h4] at h; cases h; omega
      · rw [ite_eq_right h3] at h
        by_cases h4 : r < 0
        · omega
        · rw [ite_eq_right h4] at h; cases h; omega
    · simp only [ite_eq_right h2] at h
      by_cases h3 : c < r + off
      · rw [ite_eq_left h3] at h
        by_cases h4 : c < 0
        · omega
        · rw [ite_eq_right h4] at h; cases h; omega
      · rw [ite_eq_right h3] at h
        by_cases h4 : r + off < 0
        · rw [ite_eq_left h4] at h; cases h; omega
        · rw [ite_eq_right h4] at h; cases h; omega

end NumpyLean.Indexing
