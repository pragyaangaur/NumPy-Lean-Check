import NumpyLean.Broadcast.Model

/-
Properties of the broadcasting, contiguity, reshape and axis models. Each property carries a status line that `scripts/check_props.py` counts.

Status values: PROVEN (the theorem states the property), REFUTED (the theorem states the negation and gives a counterexample), OPEN (stated in a comment only).
-/
namespace NumpyLean.Broadcast

/-! ## PyArray_Broadcast -/

theorem bcastDim_comm (nd i : Nat) (a b : List Int) :
    bcastDim nd i [a, b] 0 1 0 = bcastDim nd i [b, a] 0 1 0 := by
  simp only [bcastDim]
  generalize a.getD (i + a.length - nd) 0 = x
  generalize b.getD (i + b.length - nd) 0 = y
  by_cases ha : i + a.length ≥ nd <;> by_cases hb : i + b.length ≥ nd <;>
    simp only [ha, hb, ite_true, ite_false] <;>
    by_cases hx : x = 1 <;> by_cases hy : y = 1 <;> by_cases hxy : x = y <;> simp_all <;> omega

theorem bcastDims_comm (a b : List Int) (nd : Nat) :
    ∀ fuel i, bcastDims [a, b] nd fuel i = bcastDims [b, a] nd fuel i := by
  intro fuel
  induction fuel with
  | zero => intro i; rfl
  | succ n ih => intro i; simp only [bcastDims, bcastDim_comm, ih]

/-- PROP broadcast.broadcast.commutative_two_shapes : PROVEN
Source: the broadcasting rules in `doc/source/user/basics.broadcasting.rst` compare the two shapes dimension by dimension, which is symmetric. `PyArray_Broadcast` gives the same result for two shapes in either order, including the same error and the same argument numbers in the mismatch message, since the first argument with a non-one entry is always called arg 0. -/
theorem broadcast_commutative_two (a b : List Int) :
    pyArrayBroadcast [a, b] = pyArrayBroadcast [b, a] := by
  have h : maxLen [a, b] = maxLen [b, a] := by simp [maxLen, Nat.max_comm]
  simp only [pyArrayBroadcast, h, bcastDims_comm]

/-! ## np.broadcast_shapes -/

theorem chunkLoop_nil (fuel : Nat) (b : List Int) : chunkLoop fuel [] b = .ok b := by
  cases fuel <;> rfl

/-- PROP broadcast.broadcast_shapes.agrees_with_np_broadcast : PROVEN
Source: `_broadcast_shape` at `lib/_stride_tricks_impl.py:520-534`, which claims to return the shape of broadcasting the arrays against each other. Up to 64 arguments, `broadcast_shapes` is exactly `np.broadcast` on the arrays it builds, so every array that it accepts gives the same shape or the same error as `np.broadcast`. -/
theorem broadcastShapes_agrees_up_to_64 (shapes : List (List Int)) (h : shapes.length ≤ 64) :
    broadcastShapes shapes = (shapes.mapM emptyVoid0 >>= fun _ => npBroadcast shapes) := by
  unfold broadcastShapes
  rw [List.take_of_length_le h, List.drop_eq_nil_of_le h]
  cases shapes.mapM emptyVoid0 with
  | error e => rfl
  | ok u =>
    show (npBroadcast shapes >>= fun b => chunkLoop shapes.length [] b) = npBroadcast shapes
    cases npBroadcast shapes with
    | error e => rfl
    | ok b => simp only [bind, Except.bind, chunkLoop_nil]

/-- PROP broadcast.broadcast_shapes.argument_order_invariant : REFUTED
Source: `numpy.broadcast_shapes` docstring, "Broadcast the input shapes into a single shape", and the comment at `lib/_stride_tricks_impl.py:527` that the chunk loop exists to handle 64 or more arguments. Broadcasting is commutative, so the order of the arguments should not matter. With 65 arguments, `(2**61,)` followed by 64 empty tuples raises "array is too big", but the same arguments with `(2**61,)` last give `(2**61,)`. The chunk loop at `_stride_tricks_impl.py:532` calls `broadcast_to(0, b.shape)` with an 8-byte `int64` array, so the shape of the first 64 arguments must also pass the array size check with item size 8. Bug record `broadcast-shapes-order-beyond-64-args`. -/
theorem broadcastShapes_order_refuted :
    ¬ (∀ shapes : List (List Int), ∀ a : List Int,
        broadcastShapes (a :: shapes) = broadcastShapes (shapes ++ [a])) := by
  intro h
  have := h (List.replicate 64 []) [2 ^ 61]
  exact absurd this (by decide)

/-- PROP broadcast.broadcast_shapes.mismatch_names_arguments : REFUTED
Source: the mismatch message at `_core/src/multiarray/iterators.c:1128`, "Mismatch is between arg i with shape ... and arg j with shape ...", which numbers the arguments of the call. After 64 arguments the numbers are positions inside the chunk of `_stride_tricks_impl.py:533`, where arg 0 is the shape broadcast so far. For 64 empty tuples followed by `(2,)` and `(3,)` the message names arg 1 and arg 2 instead of arg 64 and arg 65. Bug record `broadcast-shapes-mismatch-arg-numbers`. -/
theorem broadcastShapes_mismatch_numbers_refuted :
    broadcastShapes (List.replicate 64 [] ++ [[2], [3]]) = .error (.mismatch 1 2) := by
  decide

/-- PROP broadcast.broadcast_shapes.single_shape_identity : REFUTED
Source: `numpy.broadcast_shapes` docstring, "Broadcast the input shapes into a single shape". A single valid shape should broadcast to itself. `(2**62, 2, 0)` is a valid shape, since `np.empty` accepts it with the item size 0 that `broadcast_shapes` uses, and `(0, 2**62, 2)` broadcasts to itself, but `(2**62, 2, 0)` raises "broadcast dimensions too large". `PyArray_OverflowMultiplyList` at `_core/src/multiarray/multiarraymodule.c:221-230` stops at the first zero, so a product that overflows before the zero is an error and one after it is not. Bug record `broadcast-zero-size-overflow-depends-on-position`. -/
theorem broadcastShapes_single_identity_refuted :
    emptyVoid0 [2 ^ 62, 2, 0] = .ok () ∧
    broadcastShapes [[0, 2 ^ 62, 2]] = .ok [0, 2 ^ 62, 2] ∧
    broadcastShapes [[2 ^ 62, 2, 0]] = .error .bcastTooLarge := by
  decide

/-- PROP broadcast.broadcast_shapes.accepts_every_array_shape : REFUTED
Source: the NumPy 2.0 release notes, "The maximum number of array dimensions is changed from 32 to 64", and the `numpy.broadcast_shapes` docstring, which names no limit. A shape with 33 entries of 1 is a valid array shape, but `broadcast_shapes` raises `RuntimeError` "this function only supports up to 32 dimensions", because `np.broadcast` builds old-style iterators that still stop at `NPY_MAXDIMS_LEGACY_ITERS` (`_core/src/multiarray/iterators.c:124`). Bug record `broadcast-shapes-legacy-32-dims`. -/
theorem broadcastShapes_33_dims_refuted :
    emptyVoid0 (List.replicate 33 1) = .ok () ∧
    broadcastShapes [List.replicate 33 1] = .error .legacyDims := by
  decide

/-! ## np.broadcast_to -/

theorem iterBroadcastOp_spec : ∀ (ops bs : List Int) (off idim : Nat) (bs' : List Int),
    iterBroadcastOp bs ops off idim = .ok bs' →
    bs'.length = bs.length ∧ ∀ p : Nat, bs[p]? = some 1 ∨ bs'[p]? = bs[p]? := by
  intro ops
  induction ops with
  | nil => intro bs off idim bs' h; simp [iterBroadcastOp] at h; subst h; simp
  | cons o rest ih =>
    intro bs off idim bs' h
    simp only [iterBroadcastOp] at h
    split at h
    · rename_i hb
      obtain ⟨hl, hp⟩ := ih _ _ _ _ h
      refine ⟨by simpa using hl, fun p => ?_⟩
      rcases hp p with h1 | h1
      · rw [List.getElem?_set] at h1
        split at h1
        · rename_i hpe
          subst hpe
          left
          rw [List.getD_eq_getElem?_getD] at hb
          split at h1
          · rename_i hlt
            rw [List.getElem?_eq_getElem hlt] at hb ⊢
            simp at hb
            simp [hb]
          · simp at h1
        · exact Or.inl h1
      · rw [List.getElem?_set] at h1
        split at h1
        · rename_i hpe
          subst hpe
          rw [List.getD_eq_getElem?_getD] at hb
          by_cases hlt : idim + off < bs.length
          · left
            rw [List.getElem?_eq_getElem hlt] at hb ⊢
            simp at hb
            simp [hb]
          · right
            rw [h1]
            simp [hlt]
        · exact Or.inr h1
    · split at h
      · simp at h
      · exact ih _ _ _ _ h

theorem bshape_eq (shape v : List Int) (hl : v.length = shape.length)
    (hp : ∀ p : Nat, shape[p]? = some 1 ∨ v[p]? = shape[p]?)
    (hz : ¬((shape.zip v).any fun x => x.fst == 1 && x.snd != 1) = true) : v = shape := by
  apply List.ext_getElem?
  intro p
  rcases hp p with h1 | h1
  · have hlt : p < shape.length := by
      rcases Nat.lt_or_ge p shape.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at h1; simp at h1
    have hlt' : p < v.length := by omega
    have hs : shape[p] = 1 := by rw [List.getElem?_eq_getElem hlt] at h1; simpa using h1
    have hmem : (shape[p], v[p]) ∈ shape.zip v := by
      have := List.getElem_mem (l := shape.zip v) (n := p) (by simp; omega)
      simpa [List.getElem_zip] using this
    have hv : v[p] = 1 := by
      false_or_by_contra
      apply hz
      rw [List.any_eq_true]
      exact ⟨_, hmem, by simp [hs]; assumption⟩
    rw [List.getElem?_eq_getElem hlt', List.getElem?_eq_getElem hlt, hv, hs]
  · exact h1

/-- PROP broadcast.broadcast_to.result_shape_is_requested : PROVEN
Source: `numpy.broadcast_to` docstring, "shape: The shape of the desired array". Whenever `broadcast_to` succeeds, the view has exactly the requested shape. The proof shows that the iterator only changes entries of `itershape` that are 1, and that the check at `_core/src/multiarray/nditer_constr.c:1568` rejects every such change. -/
theorem broadcastTo_shape (op : List Int) (it : Int) (shape r st : List Int)
    (h : broadcastTo op it shape = .ok (r, st)) : r = shape := by
  unfold broadcastTo at h
  simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  repeat' split at h
  all_goals (try simp at h)
  rename_i hb hz _ _ _ _
  obtain ⟨hl, hp⟩ := iterBroadcastOp_spec _ _ _ _ _ hb
  rw [← h.1]
  exact bshape_eq shape _ hl hp hz

/-- PROP broadcast.broadcast_to.agrees_with_broadcast_shapes : REFUTED
Source: the `numpy.broadcast_to` docstring raises only "If the array is not compatible with the new shape according to NumPy's broadcasting rules". `broadcast_shapes((), (2**61,))` is `(2**61,)`, but `broadcast_to` of a 0-d `int64` array to `(2**61,)` raises "array is too big", because the view must pass the size check of `_core/src/multiarray/ctors.c:748` with its item size. Every ndarray, views included, must have `size * itemsize` inside `npy_intp`, so this is the general array size limit and has no bug record. -/
theorem broadcastTo_vs_shapes_refuted :
    broadcastShapes [[], [2 ^ 61]] = .ok [2 ^ 61] ∧ broadcastTo [] 8 [2 ^ 61] = .error .tooBig := by
  decide

/-! ## Contiguity flags -/

def hasZero (l : List (Int × Int)) : Bool := l.any (·.1 == 0)

theorem cScan_zero (l : List (Int × Int)) : ∀ sd c, hasZero l = true → cScan l sd c = none := by
  induction l with
  | nil => intro sd c h; simp [hasZero] at h
  | cons p rest ih =>
    intro sd c h
    obtain ⟨d, st⟩ := p
    by_cases hd : d = 0
    · simp [cScan, hd]
    · have h' : hasZero rest = true := by simpa [hasZero, hd] using h
      by_cases h1 : d = 1 <;> simp [cScan, hd, h1, ih _ _ h']

theorem cScan_nozero (l : List (Int × Int)) :
    ∀ sd c, hasZero l = false → cScan l sd c = some (c && fScan l sd) := by
  induction l with
  | nil => intro sd c _; simp [cScan, fScan]
  | cons p rest ih =>
    intro sd c h
    obtain ⟨d, st⟩ := p
    have hd : d ≠ 0 := by intro hd; simp [hasZero, hd] at h
    have h' : hasZero rest = false := by
      cases hr : hasZero rest
      · rfl
      · simp only [hasZero] at hr h
        simp [List.any_cons, hr] at h
    by_cases h1 : d = 1
    · simp [cScan, fScan, h1, ih _ _ h']
    · by_cases hs : st = sd <;> simp [cScan, fScan, hd, h1, hs, ih _ _ h']

/-- The flags as a function of the list of (dimension, stride) pairs. -/
def flagsOfPairs (l : List (Int × Int)) (itemsize : Int) : Bool × Bool :=
  match cScan l.reverse itemsize true with
  | none => (true, true)
  | some c => (c, fScan l itemsize)

theorem contigFlags_eq (dims strides : List Int) (it : Int) :
    contigFlags dims strides it = flagsOfPairs (dims.zip strides) it := rfl

/-- PROP broadcast.flags.transpose_swaps_c_and_f : PROVEN
Source: `numpy.ndarray.T` and the flags documentation in `doc/source/reference/arrays.ndarray.rst`, where Fortran order is C order with the axes reversed. Reversing the axes of any array, which is what `.T` does, swaps the C and the Fortran contiguity flag, for every list of dimensions and strides, zero sizes included. -/
theorem flags_transpose_swaps (l : List (Int × Int)) (it : Int) :
    flagsOfPairs l.reverse it = (flagsOfPairs l it).swap := by
  unfold flagsOfPairs
  rw [List.reverse_reverse]
  cases hz : hasZero l
  · have hz' : hasZero l.reverse = false := by simpa [hasZero] using hz
    rw [cScan_nozero _ _ _ hz, cScan_nozero _ _ _ hz']
    simp
  · have hz' : hasZero l.reverse = true := by simpa [hasZero] using hz
    rw [cScan_zero _ _ _ hz, cScan_zero _ _ _ hz']
    rfl

/-- PROP broadcast.flags.zero_size_is_contiguous : PROVEN
Source: the comment "contiguous by definition" at `_core/src/multiarray/flagsobject.c:126`. An array with a zero dimension is both C and Fortran contiguous, whatever its strides. -/
theorem flags_zero_size (dims strides : List Int) (it : Int) (h : hasZero (dims.zip strides) = true) :
    contigFlags dims strides it = (true, true) := by
  rw [contigFlags_eq]
  unfold flagsOfPairs
  have h' : hasZero (dims.zip strides).reverse = true := by simpa [hasZero] using h
  rw [cScan_zero _ _ _ h']

/-- PROP broadcast.flags.c_contiguous_means_c_strides : REFUTED
Source: the plain reading of `C_CONTIGUOUS` as "the strides are the C strides of the shape". An array of shape `(2, 1)` with strides `(8, 100)` and item size 8 is C contiguous. `doc/source/reference/arrays.ndarray.rst` already says that a stride may be arbitrary when the dimension is 1 or the array has no elements, so this is documented and has no bug record. -/
theorem flags_c_strides_refuted : contigFlags [2, 1] [8, 100] 8 = (true, true) := by decide

/-! ## No-copy reshape -/

/-- The memory offsets of all elements of an array, in C order. -/
def offsetsC : List Int → List Int → List Int
  | [], _ => [0]
  | d :: ds, ss =>
    let inner := offsetsC ds ss.tail
    (List.range d.toNat).flatMap (fun (i : Nat) => inner.map (fun x => x + (i : Int) * ss.headD 0))

/-- The offsets in the order in which `reshape` reads the elements: C order, or Fortran order. -/
def offsets (dims strides : List Int) (fOrder : Bool) : List Int :=
  if fOrder then offsetsC dims.reverse strides.reverse else offsetsC dims strides

def exactly (xs : List Int) : Nat → List (List Int)
  | 0 => [[]]
  | n + 1 => (exactly xs n).flatMap (fun l => xs.map (fun x => x :: l))

/-- Old shapes with up to three entries from 1, 2 and 3, new shapes with up to three entries from 1, 2, 3, 4, 6 and 9, and strides from a set with zero, negative and non-contiguous values. -/
def shapesU : List (List Int) := (List.range 4).flatMap (fun n => exactly [1, 2, 3] n)
def newShapesU : List (List Int) := (List.range 4).flatMap (fun n => exactly [1, 2, 3, 4, 6, 9] n)
def strideVals : List Int := [0, 1, 2, 3, 6, -1, -3]

def reshapeCases : List (List Int × List Int × List Int × Bool) :=
  shapesU.flatMap fun d =>
    (exactly strideVals d.length).flatMap fun s =>
      (newShapesU.filter fun n => n.foldl (· * ·) 1 == d.foldl (· * ·) 1).flatMap fun n =>
        [(d, s, n, false), (d, s, n, true)]

/-- A successful reshape must read the same memory offsets in the same order, and the model must never reach a state the C code cannot handle. -/
def reshapeOk : List Int × List Int × List Int × Bool → Bool
  | (d, s, n, f) =>
    match reshapeNoCopy d s 1 n f with
    | .ok ns => ns.length == n.length && offsets d s f == offsets n ns f
    | .error .unreachable => false
    | .error _ => true

/-- PROP broadcast.reshape.nocopy_same_elements : PROVEN
Source: the comment at `_core/src/multiarray/shape.c:356-377`, that `_attempt_nocopy_reshape` fills in strides for the new shape that view the same data in the requested order, and that "Zero strides should work but are untested". The universe includes zero and negative strides. Checked on all 224,456 cases of `reshapeCases`, of which 79,028 succeed without a copy: whenever `reshape(..., copy=False)` succeeds, the new strides address the same memory offsets in the same C or Fortran order, and no case reaches the out-of-range reads of the C loop. The universe has 224,456 cases, too many for `decide`, so this uses `native_decide`, which trusts the compiler. -/
theorem reshape_nocopy_same_elements : reshapeCases.all reshapeOk = true := by
  native_decide

/-! ## Axis arguments -/

/-- Every source and destination list of length up to 2 with axes from `-ndim - 1` to `ndim`, for `ndim` up to 4. -/
def moveaxisCases : List (Nat × List Int × List Int) :=
  (List.range 5).flatMap fun nd =>
    let ax : List Int := (List.range (2 * nd + 2)).map fun (k : Nat) => (k : Int) - (nd : Int) - 1
    let ls := [[]] ++ ax.map (fun a => [a]) ++ ax.flatMap (fun a => ax.map (fun b => [a, b]))
    ls.flatMap fun s => ls.map fun d => (nd, s, d)

def moveaxisOk : Nat × List Int × List Int → Bool
  | (nd, s, d) =>
    match moveaxis nd s d, normalizeAxisTuple s nd, normalizeAxisTuple d nd with
    | .ok perm, .ok s', .ok d' =>
      let others := ((List.range nd).map Int.ofNat).filter (fun n => !(s'.contains n))
      -- The result is a permutation of the axes.
      ((List.range nd).map Int.ofNat).all (fun k => perm.count k == 1) && perm.length == nd &&
      -- Each source axis ends at its destination.
      (s'.zip d').all (fun (a, b) => perm[b.toNat]? == some a) &&
      -- "Other axes remain in their original order."
      perm.filter (fun n => !(s'.contains n)) == others
    | .ok _, _, _ => false
    | .error _, _, _ => true

/-- PROP broadcast.moveaxis.permutation : PROVEN
Source: `numpy.moveaxis` docstring, "Move axes of an array to new positions. Other axes remain in their original order." Checked on every case of `moveaxisCases`: when `moveaxis` succeeds the permutation it passes to `transpose` moves each source axis to its destination and keeps the other axes in order. The universe has 19,989 cases, of which 3,069 succeed, which is too slow for `decide`, so this uses `native_decide`, which trusts the compiler. -/
theorem moveaxis_permutation : moveaxisCases.all moveaxisOk = true := by
  native_decide

/-- PROP broadcast.transpose.only_permutations : REFUTED
Source: `numpy.transpose` docstring, "If specified, it must be a tuple or list which contains a permutation of [0, 1, ..., N-1] where N is the number of axes of a". `np.transpose(a, (2**32, 1))` on a 2-d array returns the array unchanged instead of raising `AxisError`, because `int axis = axes[i]` at `_core/src/multiarray/shape.c:703` keeps only the low 32 bits of the `npy_intp` axis. Bug record `broadcast-transpose-axis-truncated-to-int`. -/
theorem transpose_only_permutations_refuted :
    transpose 2 [2 ^ 32, 1] = .ok [0, 1] ∧ transpose 2 [2 ^ 32 + 1, 2 ^ 33] = .ok [1, 0] := by
  decide

/-- PROP broadcast.squeeze.axis_in_range : REFUTED
Source: `numpy.squeeze` docstring, which raises for an axis that is not of length one. `np.empty(()).squeeze(axis=-1)` and `axis=0` succeed on a 0-d array, while `axis=(0,)` raises `AxisError`. The comment at `_core/src/multiarray/conversion_utils.c:417-420` says this is a deliberate special case kept for backwards compatibility, so it has no bug record. -/
theorem squeeze_axis_in_range_refuted :
    squeeze [] false [-1] = .ok [] ∧ squeeze [] true [0] = .error .axis := by
  decide

/-! ## np.array_split and np.split -/

/-- The length of each piece of a split of a 1-d array of length `N`. -/
def pieceLens (r : Except SplitErr (List (List Int))) : Option (List Int) := r.toOption.map (·.map (·.headD 0))

def equalSplitOk : Nat × Nat → Bool
  | (N, n) =>
    match pieceLens (arraySplit [N] 0 (.count (n : Int))) with
    | some l => l.length == n && l.foldl (· + ·) 0 == (N : Int) && (l.foldl max 0 - l.foldl min (N : Int) ≤ 1)
    | none => n == 0

def equalSplitCases : List (Nat × Nat) :=
  (List.range 13).flatMap fun (N : Nat) => (List.range 15).map fun (n : Nat) => (N, n)

/-- PROP broadcast.array_split.integer_sections_balanced : PROVEN
Source: the `array_split` docstring, "For an array of length l that should be split into n sections, it returns l % n sub-arrays of size l//n + 1 and the rest of size l//n." Checked for every length up to 12 and every number of sections from 0 to 14 (0 is the `ValueError`): there are `n` pieces, their lengths add up to `N` and differ by at most one. Uses `native_decide`, which trusts the compiler. -/
theorem array_split_balanced : equalSplitCases.all equalSplitOk = true := by
  native_decide

/-- Every non-decreasing list of up to three indices between 0 and `N`. -/
def sortedIdx (N : Nat) : List (List Int) :=
  let r := (List.range (N + 1)).map Int.ofNat
  [[]] ++ r.map (fun a => [a]) ++ r.flatMap (fun a => r.filterMap fun b => if a ≤ b then some [a, b] else none) ++
    r.flatMap (fun a => r.flatMap fun b => r.filterMap fun c => if a ≤ b && b ≤ c then some [a, b, c] else none)

def sortedSplitOk : Nat × List Int → Bool
  | (N, l) =>
    match pieceLens (arraySplit [N] 0 (.idx l)) with
    | some p => p.length == l.length + 1 && p.foldl (· + ·) 0 == (N : Int)
    | none => false

def sortedSplitCases : List (Nat × List Int) :=
  (List.range 7).flatMap fun (N : Nat) => (sortedIdx N).map fun l => (N, l)

/-- PROP broadcast.array_split.sorted_indices_partition : PROVEN
Source: the `split` docstring, "If `indices_or_sections` is a 1-D array of sorted integers, the entries indicate where along `axis` the array is split." For every non-decreasing list of up to three indices inside `[0, N]` and every length up to 6, the pieces add up to the whole axis, one piece more than there are indices. Uses `native_decide`. -/
theorem array_split_sorted_partition : sortedSplitCases.all sortedSplitOk = true := by
  native_decide

/-- PROP broadcast.array_split.unsorted_indices_partition : REFUTED
Source: the `split` docstring asks for "a 1-D array of sorted integers", so this behaviour is outside the documented contract and has no bug record. `np.array_split(np.arange(5), [3, 1])` returns pieces of lengths 3, 0 and 4, which add up to 7, because each piece is the plain slice `[3:1]` of the axis and elements 1 and 2 appear twice. -/
theorem array_split_unsorted_refuted :
    pieceLens (arraySplit [5] 0 (.idx [3, 1])) = some [3, 0, 4] := by
  decide

def equalNpSplitOk : Nat × Int → Bool
  | (N, n) =>
    match pieceLens (npSplit [N] 0 (.count n)) with
    | some l => l.all (· == l.headD 0) && (N : Int) % n == 0
    | none => true

def equalNpSplitCases : List (Nat × Int) :=
  (List.range 13).flatMap fun (N : Nat) => ((List.range 20).map fun (n : Nat) => (N, (n : Int) - 5))

/-- PROP broadcast.split.success_means_equal_division : PROVEN
Source: the `split` docstring, "Raises ValueError if `indices_or_sections` is given as an integer, but a split does not result in equal division." Whenever `np.split` with an integer succeeds, all pieces have the same length and `N` is a multiple of the number of sections. Checked for lengths up to 12 and sections from -5 to 14. Uses `native_decide`. -/
theorem split_equal_division : equalNpSplitCases.all equalNpSplitOk = true := by
  native_decide

/-- PROP broadcast.split.zero_sections_error_kind : REFUTED
Source: `array_split` raises `ValueError` "number sections must be larger than 0." (`_shape_base_impl.py:760`) and the `split` docstring documents only `ValueError`. `np.split(np.arange(4), 0)` raises `ZeroDivisionError` instead, from the check `N % sections` at line 853 that runs before `array_split` is called. Bug record `broadcast-split-zero-sections-zerodivision`. -/
theorem split_zero_sections_refuted :
    npSplit [4] 0 (.count 0) = .error .zeroDiv ∧ arraySplit [4] 0 (.count 0) = .error .sections := by
  decide

/-! ## np.delete and np.insert -/

def deleteSliceOk : Nat × Option Int × Option Int × Option Int → Bool
  | (N, a, b, c) =>
    let arr := (List.range N).map Int.ofNat
    match deleteSlice arr a b c, sliceIndices N a b c with
    | .ok r, some (x, y, z) => r == arr.filter (fun v => !((pyRange x y z).contains v))
    | .error _, none => true
    | _, _ => false

def deleteSliceCases : List (Nat × Option Int × Option Int × Option Int) :=
  let bounds : List (Option Int) := none :: ((List.range 19).map fun (k : Nat) => some ((k : Int) - 9))
  let steps : List (Option Int) := none :: ((List.range 9).map fun (k : Nat) => some ((k : Int) - 4))
  (List.range 8).flatMap fun (N : Nat) => bounds.flatMap fun a => bounds.flatMap fun b => steps.map fun c => (N, a, b, c)

/-- PROP broadcast.delete.slice_removes_exactly_the_slice : PROVEN
Source: the `delete` docstring, "For a one dimensional array, this returns those entries not returned by `arr[obj]`." The slice branch copies an initial chunk, an end chunk and, for steps other than 1, the kept middle elements (`_function_base_impl.py:5301-5345`). Checked for lengths up to 7, start and stop from -9 to 9 or `None`, and steps from -4 to 4 or `None`: the result is the array without the elements of the slice, and a zero step is the only error. Uses `native_decide`. -/
theorem delete_slice_complement : deleteSliceCases.all deleteSliceOk = true := by
  native_decide

def deleteIntOk : Nat × Int → Bool
  | (N, i) =>
    let arr := (List.range N).map Int.ofNat
    match deleteObj arr (.int i) with
    | .ok r => !(i < -(N : Int) || i ≥ N) && r == arr.filter (fun v => v != wrapIndex N i)
    | .error .index => i < -(N : Int) || i ≥ N
    | .error _ => false

/-- PROP broadcast.delete.single_index : PROVEN
Source: the `delete` docstring and the single value path at `_function_base_impl.py:5352-5368`. For every length up to 7 and every index from -9 to 9, `np.delete(a, i)` removes the element at `i` (counting from the end when negative) and an index outside `[-N, N)` is an `IndexError`. -/
theorem delete_single_index : ((List.range 8).flatMap fun (N : Nat) => (List.range 19).map fun (k : Nat) => (N, (k : Int) - 9)).all deleteIntOk = true := by
  decide

def insertSingleOk : Nat × Int × List Int → Bool
  | (N, i, v) =>
    let arr := (List.range N).map Int.ofNat
    insertObj arr (.list [i]) v == insertObj arr (.int i) v

/-- PROP broadcast.insert.list_of_one_matches_scalar : PROVEN
Source: the `insert` docstring, "Support for multiple insertions when `obj` is a single scalar or a sequence with one element". On a 1-d array `np.insert(a, [i], v)` and `np.insert(a, i, v)` give the same result or the same error, for lengths up to 5, indices from -8 to 8 and value lists of length 0 to 3. Uses `native_decide`. -/
theorem insert_list_of_one_matches_scalar :
    ((List.range 6).flatMap fun (N : Nat) => (List.range 17).flatMap fun (k : Nat) => (List.range 4).map fun (m : Nat) =>
      (N, (k : Int) - 8, (List.range m).map fun (j : Nat) => (100 + j : Int))).all insertSingleOk = true := by
  native_decide

/-- PROP broadcast.insert.out_of_range_index_rejected : REFUTED
Source: `insert` raises `IndexError` for an index outside `[-N, N]` on the single index path (`_function_base_impl.py:5555-5558`), and the docstring describes a list as "similar to calling insert multiple times". On the multiple index path there is no range check, only `indices[indices < 0] += N` at line 5586 and a fancy index that wraps negative numbers. `np.insert(np.arange(3), -5, 9)` raises, while `np.insert(np.arange(3), [-5, 1], 9)` returns `[0, 1, 9, 9, 2]`, silently treating -5 as a valid position. Bug record `broadcast-insert-multiple-negative-out-of-range`. -/
theorem insert_out_of_range_refuted :
    insertObj [0, 1, 2] (.int (-5)) [9] = .error .index ∧ insertObj [0, 1, 2] (.list [-5, 1]) [9] = .ok [0, 1, 9, 9, 2] := by
  decide

/-- PROP broadcast.insert.bool_list_accepted : REFUTED
Source: the `insert` docstring lists `obj` as "slice, int, array-like of ints or bools" and says boolean indices are a mask. `np.insert(np.arange(3), np.array([True, False, True]), 9)` works, but the same mask as a Python list raises `AttributeError: 'list' object has no attribute 'ndim'`, because line 5539 reads `obj.ndim` instead of `indices.ndim`. Bug record `broadcast-insert-bool-list-attribute-error`. -/
theorem insert_bool_list_refuted :
    insertObj [0, 1, 2] (.mask [true, false, true]) [9] = .ok [9, 0, 1, 9, 2] ∧
    insertObj [0, 1, 2] (.boolList [true, false, true]) [9] = .error .attr := by
  decide

/-- PROP broadcast.insert.mask_length_checked : REFUTED
Source: `delete` raises `ValueError` when a boolean mask does not match the axis length (`_function_base_impl.py:5372-5376`), and the `insert` docstring describes a boolean `obj` as a mask in the same words. `insert` has no such check: `np.insert(np.arange(3), np.array([False] * 5), 9)` returns `[0, 1, 2]` and a five element mask `[True, False, False, False, False]` inserts before element 0, where `np.delete` raises on both. The mask is only turned into indices by `np.flatnonzero` at line 5540. Bug record `broadcast-insert-bool-mask-length-unchecked`. -/
theorem insert_mask_length_refuted :
    insertObj [0, 1, 2] (.mask [false, false, false, false, false]) [9] = .ok [0, 1, 2] ∧
    deleteObj [0, 1, 2] (.mask [false, false, false, false, false]) = .error .value := by
  decide

/-! ## np.pad -/

def padScalarOk : List Int × Int → Bool
  | (shape, w) => padShape shape [] [w] == .ok (shape.map (· + 2 * w))

def padShapes : List (List Int) :=
  let r : List Int := [0, 1, 2, 3]
  [[]] ++ r.map (fun a => [a]) ++ r.flatMap (fun a => r.map fun b => [a, b]) ++
    r.flatMap (fun a => r.flatMap fun b => r.map fun c => [a, b, c])

/-- PROP broadcast.pad.scalar_width : PROVEN
Source: the `pad` docstring, "`(pad,)` or int is a shortcut for before = after = pad width for all axes." For every shape of up to three axes with lengths 0 to 3 and every width from 0 to 5, a scalar width adds twice the width to every axis. Uses `native_decide`, which trusts the compiler, because `decide` reaches the recursion limit. -/
theorem pad_scalar_width : (padShapes.flatMap fun s => (List.range 6).map fun (w : Nat) => (s, (w : Int))).all padScalarOk = true := by
  native_decide

def padColumnOk : List Int → Bool
  | shape =>
    let w := (List.range shape.length).map fun (k : Nat) => (k : Int) + 1
    padShape shape [shape.length, 1] w == .ok ((shape.zip w).map fun (s, x) => s + 2 * x)

/-- PROP broadcast.pad.column_of_widths : PROVEN
Source: the comment at `_arraypad_impl.py:520-524`, "each dimension has a single value which should be broadcasted to a pair, e.g. [[1], [2]] -> [[1, 1], [2, 2]] not [[1, 2], [1, 2]]". For shapes of up to three axes the width array of shape `(ndim, 1)` pads axis `k` by `w[k]` on both sides. Shapes of fewer than two axes are left out. -/
theorem pad_column_of_widths : (padShapes.filter (fun s => s.length ≥ 2)).all padColumnOk = true := by
  decide

/-- PROP broadcast.pad.large_scalar_width_error : REFUTED
Source: `pad` should reject a width that makes the array impossibly large with the error that `np.empty` gives for the shape, as the nested form does. A scalar or pair width reaches `_pad_simple` as `intp` scalars (`_arraypad_impl.py:519`, `529`), so `left + size + right` at line 111 wraps around in 64 bits. `np.pad(np.zeros((4, 4)), 2**63 - 1)` raises "could not broadcast input array from shape (4,4) into shape (0,0)" and `np.pad(np.zeros(1), 2**63 - 1)` raises "negative dimensions are not allowed", while the same widths as `[[2**63-1, 2**63-1], [2**63-1, 2**63-1]]` give "Maximum allowed dimension exceeded". Every case still raises `ValueError`, so only the message is wrong. Bug record `broadcast-pad-scalar-width-wraps`. -/
theorem pad_large_width_refuted :
    padShape [4, 4] [] [2 ^ 63 - 1] = .error .assign ∧
    padShape [1] [] [2 ^ 63 - 1] = .error .negDim ∧
    padShape [4, 4] [2, 2] [2 ^ 63 - 1, 2 ^ 63 - 1, 2 ^ 63 - 1, 2 ^ 63 - 1] = .error .conv := by
  decide

end NumpyLean.Broadcast
