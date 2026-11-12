import NumpyLean.Strings.Model

/-
Properties of the string models. Each property carries a status line that `scripts/check_props.py` counts.

Status values: PROVEN (the theorem states the property), REFUTED (the theorem states the negation and gives a counterexample), OPEN (stated in a comment only).

The long counterexamples (a haystack of 2500 characters) are checked with `native_decide`, which trusts the compiler, because the kernel would take too long to run the search.
-/
namespace NumpyLean.Strings

/-! ## Trailing NULs -/

/-- PROP strings.str_len.s_trailing_nul_invisible : PROVEN
Source: `Buffer::num_codepoints` (`string_buffer.h:280`) and the documentation in `doc/source/reference/routines.strings.rst`, which says that `S` and `U` arrays drop trailing NULs. A NUL added at the end of an `S` element does not change `str_len`. -/
theorem strLen_S_append_nul (a : Str) : strLen .S (a ++ [0]) = strLen .S a := by
  simp [strLen, readStr, dropTrailingZeros]

/-- PROP strings.str_len.t_keeps_trailing_nul : PROVEN
Source: the `StringDType` length loop (`stringdtype_ufuncs.cpp:719`) counts every code point. A trailing NUL is one more character in a `T` element, which is the documented difference between `StringDType` and the fixed width kinds. -/
theorem strLen_T_append_nul (a : Str) : strLen .T (a ++ [0]) = strLen .T a + 1 := by
  simp [strLen, readStr]

/-! ## Offsets -/

/-- PROP strings.adjust_offsets.in_range : PROVEN
Source: `adjust_offsets` (`string_buffer.h:829`). After the adjustment `start` is not negative and `end` lies in `[0, len]`, so the slice of the haystack that the search sees never reaches outside the buffer. -/
theorem adjustOffsets_in_range (start end_ : Int) (len : Nat) :
    0 ≤ (adjustOffsets start end_ len).1 ∧ 0 ≤ (adjustOffsets start end_ len).2 ∧
      (adjustOffsets start end_ len).2 ≤ len := by
  unfold adjustOffsets
  dsimp only
  repeat' split
  all_goals omega

/-- Inside the string the adjustment changes nothing. -/
theorem adjustOffsets_id (s e : Int) (len : Nat) (h0 : 0 ≤ s) (h1 : 0 ≤ e) (h2 : e ≤ len) :
    adjustOffsets s e len = (s, e) := by
  have a1 : ¬ (e > (len : Int)) := by omega
  have a2 : ¬ e < 0 := by omega
  have a3 : ¬ s < 0 := by omega
  simp [adjustOffsets, a1, a2, a3]

/-- PROP strings.find.empty_needle_returns_start : PROVEN
Source: `string_find` (`string_buffer.h:851`) returns `start` for an empty needle, as `str.find` does. It holds for `StringDType` and for any range inside the string. -/
theorem find_empty_needle_T (a : Str) (s e : Int) (h0 : 0 ≤ s) (hse : s ≤ e) (he : e ≤ a.length) :
    findImpl .T a [] s e = s := by
  have h := adjustOffsets_id s e a.length h0 (by omega) he
  have n1 : ¬ (e - s < 0) := by omega
  simp [findImpl, readStr, h, n1]

/-- PROP strings.rfind.empty_needle_returns_end : PROVEN
Source: `string_rfind` (`string_buffer.h:954`) returns `end` for an empty needle, as `str.rfind` does. -/
theorem rfind_empty_needle_T (a : Str) (s e : Int) (h0 : 0 ≤ s) (hse : s ≤ e) (he : e ≤ a.length) :
    rfindImpl .T a [] s e = e := by
  have h := adjustOffsets_id s e a.length h0 (by omega) he
  have n1 : ¬ (e - s < 0) := by omega
  simp [rfindImpl, readStr, h, n1]

/-- PROP strings.count.empty_needle_counts_gaps : PROVEN
Source: `string_count` (`string_buffer.h:1066`) gives `end - start + 1` for an empty needle, as `str.count` does. -/
theorem count_empty_needle_T (a : Str) (s e : Int) (h0 : 0 ≤ s) (hse : s ≤ e) (he : e ≤ a.length) :
    countImpl .T a [] s e = e - s + 1 := by
  have h := adjustOffsets_id s e a.length h0 (by omega) he
  have n1 : ¬ (e < s) := by omega
  have n2 : ¬ (e - s < 0) := by omega
  simp [countImpl, readStr, h, n1, n2]

/-- PROP strings.startswith.empty_prefix_in_range : PROVEN
Source: `tailmatch` (`string_buffer.h:1110`) returns true for an empty prefix when `start <= end`, and `str.startswith` does the same. -/
theorem startswith_empty_T (a : Str) (s e : Int) (h0 : 0 ≤ s) (hse : s ≤ e) (he : e ≤ a.length) :
    tailmatchImpl .T true a [] s e = true := by
  have h := adjustOffsets_id s e a.length h0 (by omega) he
  have n1 : ¬ (e < s) := by omega
  simp [tailmatchImpl, readStr, h, n1]

/-! ## Padding -/

/-- PROP strings.center.length_is_max : PROVEN
Source: `str.center` and the `center` docstring: the result has length `width` unless the string is longer. `string_pad` (`string_buffer.h:1569`) splits the padding into a left and a right part that add up to `final - len`. -/
theorem padCore_length (pos : Pos) (a : Str) (final : Nat) (fill : Int) :
    (padCore pos a final fill).length = max a.length final := by
  unfold padCore
  split
  · omega
  · rename_i h
    simp only [padSplit, List.length_append, List.length_replicate]
    cases pos <;> simp only <;> (try split) <;> omega

/-- PROP strings.zfill.sign_stays_in_front : PROVEN
Source: the `zfill` docstring says a leading sign is handled by inserting the padding after the sign. The statement is checked for the `StringDType` input "-5" padded to width 4. -/
theorem zfill_sign_example : zfillImpl .T [45, 53] 4 = .ok [45, 48, 48, 53] := by decide

/-- PROP strings.center.extra_pad_rule_matches_python : PROVEN
Source: `str.center` puts the extra character on the left when both the padding and the width are odd, and `padSplit` copies that rule (`string_buffer.h:1604`). Checked on the model for `"ab".center(5)`, `"a".center(4)` and `"abc".center(6)`, whose Python results are `"  ab "`, `" a  "` and `" abc  "`. -/
theorem center_examples :
    padCore .center [97, 98] 5 32 = [32, 32, 97, 98, 32] ∧
    padCore .center [97] 4 32 = [32, 97, 32, 32] ∧
    padCore .center [97, 98, 99] 6 32 = [32, 97, 98, 99, 32, 32] := by decide

/-- PROP strings.center.huge_width_same_error_kind : REFUTED
Source: `center`, `ljust`, `rjust` and `zfill` with a width that is far too large. The `S` and `U` wrappers build the dtype `S<width>` or `U<width>` first, and `np.dtype` rejects an item size above `INT_MAX` with `TypeError: data type 'U...' not understood` (`strings.py:754`). The `StringDType` loop tries to allocate and raises `MemoryError`. `str.center` raises `MemoryError` or `OverflowError`. The same call on the three kinds gives different error kinds, and the `TypeError` message does not mention the width. -/
theorem center_huge_width_error_kinds :
    justImpl .U .center [97] 4294967296 [32] = .error .dtype ∧
    justImpl .T .center [97] 4611686018427387904 [32] = .error .alloc := by decide

/-! ## Tabs -/

/-- PROP strings.expandtabs.huge_tabsize_overflow_error : PROVEN
Source: `string_expandtabs_length` (`string_buffer.h:1496`) rejects an output longer than `INT_MAX` with `OverflowError: new string is too long`, so a tab with a tab size of 2^31 fails in every kind. -/
theorem expandtabs_huge_tabsize :
    (expandtabsImpl .S [9] 2147483648 = .error .tooLong) ∧ (expandtabsImpl .T [9] 2147483648 = .error .tooLong) := by
  decide

/-- PROP strings.expandtabs.tabsize_zero_example : PROVEN
Source: the `expandtabs` docstring and `str.expandtabs`: with a tab size of zero tabs are removed. Checked on `"a\tb"`. -/
theorem expandtabs_zero_example : expandtabsImpl .U [97, 9, 98] 0 = .ok [97, 98] := by decide

/-! ## Slices -/

/-- PROP strings.slice.reverse_with_defaults : PROVEN
Source: `np.strings.slice` fills a missing start and stop of a negative step with `INTP_MAX` and `INTP_MIN` (`strings.py:1801`), and `PySlice_AdjustIndices` clips them, so the result is the reversed string, like `a[::-1]`. -/
theorem slice_reverse_example (a : Str) (h : a = [1, 2, 3]) :
    sliceImpl .T a intpMax intpMin (-1) = .ok [3, 2, 1] := by
  subst h; decide

/-! ## strip with chars -/

/-- The result that `str.strip`, `str.lstrip` and `str.rstrip` give with the characters in `ch`, in terms of the plain test of membership. -/
def pyStrip (mode : Strip) (ch : Str) (a : Str) : Str :=
  stripCore mode (fun c => ch.contains c) (fun c => ch.contains c) a

theorem flatMap_utf8Encode_ascii (ch : Str) (h : ∀ c ∈ ch, 0 ≤ c ∧ c < 128) : ch.flatMap utf8Encode = ch := by
  induction ch with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have hx' : x < 0x80 := by omega
    simp [List.flatMap_cons, utf8Encode, hx', ih (fun c hc => h c (by simp [hc]))]

/-- PROP strings.strip.chars_ascii_only_matches_python : PROVEN
Source: `string_lrstrip_chars` (`string_buffer.h:1230`) for `StringDType`. When every character of `chars` is ASCII the search over its UTF-8 bytes, cut to `len2` bytes, covers the whole set, and the result is the same as for `str.strip`. -/
theorem strip_T_ascii_chars (mode : Strip) (ch a : Str) (h : ∀ c ∈ ch, 0 ≤ c ∧ c < 128) (hne : ch ≠ []) :
    stripImpl .T mode a (some ch) = readStr .T (pyStrip mode ch a) := by
  have hf := flatMap_utf8Encode_ascii ch h
  have hin : ∀ c, inStripSet .T ch c = ch.contains c := by
    intro c
    unfold inStripSet
    split
    · rw [hf]; simp
    · rfl
  have hfun : inStripSet .T ch = fun c => ch.contains c := funext hin
  simp [stripImpl, readStr, hne, pyStrip, hfun]

/-- PROP strings.strip.chars_multibyte_matches_python : REFUTED
Source: `string_lrstrip_chars` (`string_buffer.h:1270`, `:1316`). For `StringDType`, an ASCII character is searched for in the first `len2` bytes of the UTF-8 form of `chars`, where `len2` counts code points. With `chars = "éa"` the bytes are `c3 a9 61` and only `c3 a9` are searched, so `"aaa"` is not stripped, while `str.strip` gives the empty string. -/
theorem strip_T_multibyte_chars :
    stripImpl .T .both [97, 97, 97] (some [233, 97]) ≠ readStr .T (pyStrip .both [233, 97] [97, 97, 97]) := by decide

/-- PROP strings.strip.u_chars_matches_python : PROVEN
Source: the same function for `U`, which searches the code points directly, on the same input as the refuted `StringDType` property. -/
theorem strip_U_multibyte_example :
    stripImpl .U .both [97, 97, 97] (some [233, 97]) = readStr .U (pyStrip .both [233, 97] [97, 97, 97]) := by decide

/-! ## strip of whitespace and NUL -/

/-- What `str.rstrip()` gives. -/
def pyRstripWs (k : Kind) (a : Str) : Str := (a.reverse.dropWhile (isSpace k)).reverse

/-- PROP strings.rstrip.t_matches_python : PROVEN
Source: `string_lrstrip_whitespace` (`string_buffer.h:1166`) for `StringDType`, whose right-hand test is `isspace` only. -/
theorem rstrip_T_matches_python (a : Str) :
    stripImpl .T .right a none = readStr .T (pyRstripWs .T (readStr .T a)) := by
  simp [stripImpl, readStr, stripCore, pyRstripWs]

/-- PROP strings.rstrip.u_matches_python : REFUTED
Source: `string_lrstrip_whitespace` (`string_buffer.h:1202`). For `S` and `U` the right-hand test also removes NUL (`*traverse_buf != 0`), so the whitespace in front of an embedded NUL goes too. For `"a \x00\n"`, `str.rstrip` gives `"a \x00"`, which an `S` or `U` array reads as `"a "`, and `np.strings.rstrip` gives `"a"`. `StringDType` gives `"a \x00"`. -/
theorem rstrip_U_nul_in_whitespace :
    stripImpl .U .right [97, 32, 0, 10] none ≠ readStr .U (pyRstripWs .U (readStr .U [97, 32, 0, 10])) := by decide

/-! ## Long strings: the UTF-32 two-way search -/

/-- PROP strings.find.u_periodicity_test_counts_bytes : REFUTED
Source: `preprocess` (`string_fastsearch.h:639`) calls `memcmp(needle, needle + period, cut)` with `cut` counted in characters, so for `npy_ucs4` it compares only `cut` bytes. For the needle "bb" followed by 98 letters "a" the test says periodic for `U` and not periodic for `S`. The needle has no period. -/
theorem u_periodic_flag_wrong :
    (preprocess (#[98, 98] ++ Array.replicate 98 97) 100 4).periodic = true ∧
    (preprocess (#[98, 98] ++ Array.replicate 98 97) 100 1).periodic = false := by
  native_decide -- the kernel is too slow for a needle of 100 characters

/-- PROP strings.find.u_agrees_with_s : REFUTED
Source: `fastsearch` (`string_fastsearch.h:1258`) goes to `two_way_find` for a haystack of 2500 or more units and a needle of 100 or more. For "a" repeated 2500 times and the needle "bb" followed by 98 letters "a", `np.strings.find` gives 1 for `U` and -1 for `S`, `StringDType` and `str.find`. -/
theorem find_u_wrong_on_long_needle :
    findImpl .U (List.replicate 2500 97) (98 :: 98 :: List.replicate 98 97) 0 intpMax = 1 ∧
    findImpl .S (List.replicate 2500 97) (98 :: 98 :: List.replicate 98 97) 0 intpMax = -1 := by
  native_decide -- runs the search on 2500 characters

/-- PROP strings.count.u_agrees_with_s : REFUTED
Source: `two_way_count` with the same periodicity test. The same input counts 24 matches for `U` and 0 for `S`. -/
theorem count_u_wrong_on_long_needle :
    countImpl .U (List.replicate 2500 97) (98 :: 98 :: List.replicate 98 97) 0 intpMax = 24 ∧
    countImpl .S (List.replicate 2500 97) (98 :: 98 :: List.replicate 98 97) 0 intpMax = 0 := by
  native_decide -- runs the search on 2500 characters

end NumpyLean.Strings
