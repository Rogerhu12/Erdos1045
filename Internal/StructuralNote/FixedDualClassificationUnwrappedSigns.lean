import StructuralNote.FixedDualClassificationSixArcSigns
import StructuralNote.FixedDualClassificationGridPeriodicity

/-! Six-arc localization in unwrapped natural coordinates, as used by the
background convolution and terminal-component slide. -/

namespace StructuralNote.FixedDualClassificationUnwrappedSigns

open Real Set Filter Erdos1045.EventualExact FiniteBox
open FixedDualClassificationStep FixedDualClassificationFinite
open FixedDualClassificationSixArcSigns FixedDualClassificationZeroArcs
open FixedDualClassificationGridPeriodicity FiniteCompressionRanked
noncomputable section

theorem eventually_near_maximum_unwrapped_signs (C₀ : ℝ) :
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 0 < m) (s : SignPattern hm),
      deficit hm s ≤ C₀ / (2 * m : ℝ) ^ 2 →
      ∃ α ∈ Icc (-(Real.pi / 3)) (Real.pi / 3), ∀ j : ℕ,
        (∀ k : ℤ, (1 : ℝ) / 8 ≤ |cellMidpoint (2 * m) j - zeroCenter α k|) →
        (1 : ℝ) / 100 < |potential s (site hm j)| ∧
        patternSign s (site hm j) =
          if 0 ≤ cos (3 * (cellMidpoint (2 * m) j - α)) then 1 else -1 := by
  filter_upwards [eventually_near_maximum_six_arc_signs C₀] with m h hm s hdef
  obtain ⟨α, hα, hsites⟩ := h hm s hdef
  refine ⟨α, hα, fun j haway => ?_⟩
  have hsite := hsites (site hm j) (haway_site_of_haway hm j α haway)
  rwa [← cos_third_cellMidpoint_site hm j α] at hsite

end
end StructuralNote.FixedDualClassificationUnwrappedSigns
