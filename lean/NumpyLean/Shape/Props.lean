import NumpyLean.Shape.Model

/-
Properties of the shape models. Each property carries a status line that `scripts/check_props.py` counts.

Status values: PROVEN (the theorem states the property), REFUTED (the theorem states the negation and gives a counterexample), OPEN (stated in a comment only).
-/
namespace NumpyLean.Shape

/-- PROP shape.reshape.empty_shape_needs_size_one : PROVEN
Source: `numpy.reshape` docs, "The new shape should be compatible with the original shape". The empty shape is accepted exactly for arrays with one element. -/
theorem reshape_empty_shape (s : Int) :
    fixUnknownDimension [] s = .ok [] ↔ s = 1 := by
  simp only [fixUnknownDimension, scanDims, bind, Except.bind]
  by_cases h : s = 1 <;> simp [h]

/-- PROP shape.reshape.only_minus_one_is_unknown : REFUTED
Source: `numpy.reshape` docs, "One shape dimension can be -1. In this case, the value is inferred from the length of the array and remaining dimensions." The docs name -1 only, so other negative entries should be rejected. `shape.c:499` accepts any negative entry, so `reshape(-5, 2)` on six elements gives `(3, 2)`. -/
theorem reshape_only_minus_one_is_unknown_refuted :
    ¬ (∀ (dims : List Int) (s : Int) (r : List Int),
        fixUnknownDimension dims s = .ok r → ∀ d ∈ dims, d < 0 → d = -1) := by
  intro h
  have := h [-5, 2] 6 [3, 2] (by decide) (-5) (by decide) (by decide)
  exact absurd this (by decide)

end NumpyLean.Shape
