import StructuralNote.MatchingActivityActiveConstraintDifferentials
import StructuralNote.LensIncrementDerivatives

/-! The nonzero diagonal derivative of a selected lens endpoint.  The
derivative of the height, including any closure correction, cancels exactly. -/

namespace StructuralNote.MatchingActivityActiveConstraintLensDerivative

open Erdos1045.EventualExact Complex LensClosure
open LensIncrementDerivatives
open MatchingActivityCrossingVariationDerivative
open scoped Topology ContDiff

noncomputable section

def selectedLensValue (e L s h : ℝ) : ℝ :=
  ‖(L : ℂ) + (e : ℂ) * LensClosure.increment 0 L s h‖ ^ 2

theorem selectedLensValue_hasDerivAt {e L : ℝ} {s h : ℝ → ℝ}
    {s' h' : ℝ} (hs : HasDerivAt s s' 0) (hh : HasDerivAt h h' 0)
    (he : e = 1 ∨ e = -1) (hse : s 0 = e) (hsmall : (h 0) ^ 2 < 4) :
    HasDerivAt (fun t => selectedLensValue e L (s t) (h t))
      (2 * e * Lens.height (h 0) * Lens.width L (h 0) * s') 0 := by
  have hi := increment_sigma_hasDerivAt 0 L hs hh hsmall
  have hz := (hi.const_mul (e : ℂ)).const_add (L : ℂ)
  have hd := hz.norm_sq
  have hH := Lens.height_sq hsmall.le
  have hHp := height_pos hsmall
  change HasDerivAt (fun t => selectedLensValue e L (s t) (h t)) _ 0 at hd
  apply hd.congr_deriv
  rw [hse]
  rcases he with rfl | rfl
  · rw [Complex.inner]
    simp [unit, controlSource, tangent, LensClosure.increment, Lens.width]
    field_simp
    nlinarith
  · rw [Complex.inner]
    simp [unit, controlSource, tangent, LensClosure.increment, Lens.width]
    field_simp
    nlinarith

theorem selectedLensValue_derivative_ne_zero {e L h : ℝ}
    (he : e = 1 ∨ e = -1) (hsmall : h ^ 2 < 4)
    (hw : 0 < Lens.width L h) :
    2 * e * Lens.height h * Lens.width L h ≠ 0 := by
  have hH : 0 < Lens.height h := height_pos hsmall
  rcases he with rfl | rfl <;> positivity

end
end StructuralNote.MatchingActivityActiveConstraintLensDerivative
