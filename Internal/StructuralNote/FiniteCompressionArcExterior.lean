import StructuralNote.FixedDualClassificationNormalizedSigns
import StructuralNote.FiniteCompressionLocalizedBackground
import StructuralNote.FiniteCompressionArcAngles

/-! The exterior platform signs used by the actual background patch follow
from six-arc localization and the rounded midpoint bounds. -/

namespace StructuralNote.FiniteCompressionArcExterior

open Real Erdos1045.EventualExact FiniteBox
open FixedDualClassificationStep FixedDualClassificationZeroArcs
open FixedDualClassificationExteriorGaps FiniteCompressionLocalizedBackground
open FiniteCompressionArcAngles FiniteCompressionRanked
noncomputable section

theorem exteriorSigns_of_midpoint_bounds {m : ℕ} (hm : 0 < m)
    (s : SignPattern hm) {β : ℝ} (hs : LocalizedSigns hm s β)
    {L₀ R₀ L₁ R₁ L₂ R₂ : ℕ}
    (hstep : Real.pi / m ≤ (Real.pi - 3) / 24)
    (hL₀lo : zeroCenter β 0 - 1 / 8 - Real.pi / m < cellMidpoint (2 * m) L₀)
    (hL₀hi : cellMidpoint (2 * m) L₀ ≤ zeroCenter β 0 - 1 / 8)
    (hL₁hi : cellMidpoint (2 * m) L₁ ≤ zeroCenter β 1 - 1 / 8)
    (hL₂hi : cellMidpoint (2 * m) L₂ ≤ zeroCenter β 2 - 1 / 8)
    (hR₀ : zeroCenter β 0 + 1 / 8 < cellMidpoint (2 * m) (R₀ + 1))
    (hR₁ : zeroCenter β 1 + 1 / 8 < cellMidpoint (2 * m) (R₁ + 1))
    (hR₂ : zeroCenter β 2 + 1 / 8 < cellMidpoint (2 * m) (R₂ + 1)) :
    ExteriorSigns hm s L₀ R₀ L₁ R₁ L₂ R₂ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply sign_positive_in_gap hs L₀ (k := -1) (by norm_num)
    · dsimp only [zeroCenter] at hL₀lo ⊢
      norm_num at hL₀lo ⊢
      linarith [pi_gt_three]
    · simpa only [show (-1 : ℤ) + 1 = 0 by norm_num] using hL₀hi
  · intro j hjlo hjhi
    apply sign_negative_in_gap hs j (k := 0) (by norm_num)
    · exact hR₀.le.trans (midpoint_monotone (2 * m) (show R₀ + 1 ≤ j by omega))
    · exact (midpoint_monotone (2 * m) hjhi).trans hL₁hi
  · intro j hjlo hjhi
    apply sign_positive_in_gap hs j (k := 1) (by norm_num)
    · exact hR₁.le.trans (midpoint_monotone (2 * m) (show R₁ + 1 ≤ j by omega))
    · exact (midpoint_monotone (2 * m) hjhi).trans hL₂hi
  · intro j hjlo hjhi
    apply sign_negative_in_gap hs j (k := 2) (by norm_num)
    · exact hR₂.le.trans (midpoint_monotone (2 * m) (show R₂ + 1 ≤ j by omega))
    · have hx := midpoint_monotone (2 * m) hjhi
      rw [midpoint_half_period hm] at hx
      have hc : zeroCenter β (2 + 1) = zeroCenter β 0 + Real.pi := by
        unfold zeroCenter
        norm_num
      rw [hc]
      linarith

end
end StructuralNote.FiniteCompressionArcExterior
