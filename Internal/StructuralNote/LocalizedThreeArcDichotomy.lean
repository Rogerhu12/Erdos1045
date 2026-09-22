import StructuralNote.LocalizedTerminalImprovement
import StructuralNote.FixedDualClassificationArcRecenter
import StructuralNote.ArcTransitionTransport

/-! The same two-site estimate handles all three independent arcs, after
actual integer rotations and a sign reversal for the ascending arc. -/

namespace StructuralNote.LocalizedThreeArcDichotomy

open Real Set Filter Erdos1045.EventualExact FiniteBox
open SignPatternSymmetry FixedDualClassificationFinite
open FixedDualClassificationExteriorGaps FixedDualClassificationNormalizedSigns
open FixedDualClassificationArcGrid FixedDualClassificationArcRecenter
open LocalizedTerminalImprovement ArcTransitionTransport FiniteCompressionArcAngles
open scoped Topology
noncomputable section

def ThreeTransitions {m : ℕ} (hm : 0 < m) (s : SignPattern hm) (β : ℝ) : Prop :=
  DescendingTransition hm s (arcLeft m β 0) (arcRight m β 0) ∧
    AscendingTransition hm s (arcLeft m β 1) (arcRight m β 1) ∧
    DescendingTransition hm s (arcLeft m β 2) (arcRight m β 2)

theorem eventually_three_arc_dichotomy : ∃ η : ℝ, 0 < η ∧
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 0 < m) (s : SignPattern hm) (β : ℝ),
      0 ≤ β → β ≤ gridStep m → LocalizedSigns hm s β →
        ThreeTransitions hm s β ∨ TwoSiteImprovement hm η s := by
  obtain ⟨η, hη, hevent⟩ := eventually_first_arc_dichotomy
  refine ⟨η, hη, ?_⟩
  filter_upwards [hevent, eventually_small_grid_step] with m hfirst hstep
  intro hm s β hβ0 hβhi hs
  rcases hfirst hm s β hβ0 hβhi hs with h0 | himp
  · obtain ⟨k₁, γ₁, hγ₁, he₁⟩ := phase_normalization_nonneg hm
      (show 0 ≤ β + Real.pi / 3 by positivity)
    have hs₁ := localizedSigns_rotate_direct (localizedSigns_negate_third hs) k₁ he₁
    rcases hfirst hm (rotatePattern k₁ (globalNegate s)) γ₁ hγ₁.1 hγ₁.2.le hs₁ with h1 | himp
    · have hcuts₁ := arc_cuts_recenter hm hγ₁.1 hstep
        (i := 1) (α := β) (by simpa only [Nat.cast_one, one_mul] using he₁)
      have h1' := descending_of_rotate hm (globalNegate s) k₁ _ _ h1
      rw [hcuts₁.1, hcuts₁.2] at h1'
      have ha1 := ascending_of_negate hm s _ _ h1'
      obtain ⟨k₂, γ₂, hγ₂, he₂⟩ := phase_normalization_nonneg hm
        (show 0 ≤ β + 2 * Real.pi / 3 by positivity)
      have hs₂ := localizedSigns_rotate_direct (localizedSigns_two_thirds hs) k₂ he₂
      rcases hfirst hm (rotatePattern k₂ s) γ₂ hγ₂.1 hγ₂.2.le hs₂ with h2 | himp
      · have hcuts₂ := arc_cuts_recenter hm hγ₂.1 hstep
          (i := 2) (α := β) (by norm_num only [Nat.cast_ofNat] at *; exact he₂)
        have h2' := descending_of_rotate hm s k₂ _ _ h2
        rw [hcuts₂.1, hcuts₂.2] at h2'
        exact Or.inl ⟨h0, ha1, h2'⟩
      · exact Or.inr (improvement_of_rotate k₂ himp)
    · exact Or.inr (improvement_of_negate (improvement_of_rotate k₁ himp))
  · exact Or.inr himp

theorem eventually_near_maximum_three_arcs (C₀ : ℝ) : ∃ η : ℝ, 0 < η ∧
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 0 < m) (s : SignPattern hm),
      deficit hm s ≤ C₀ / (2 * m : ℝ) ^ 2 →
      TwoSiteImprovement hm η s ∨
        ∃ k : ℕ, ∃ β ∈ Ico 0 (gridStep m),
          LocalizedSigns hm (rotatePattern k s) β ∧ ThreeTransitions hm (rotatePattern k s) β := by
  obtain ⟨η, hη, hevent⟩ := eventually_three_arc_dichotomy
  refine ⟨η, hη, ?_⟩
  filter_upwards [hevent, eventually_normalized_localization C₀] with m hthree hloc
  intro hm s hdef
  obtain ⟨k, β, hβ, hs, _⟩ := hloc hm s hdef
  rcases hthree hm (rotatePattern k s) β hβ.1 hβ.2.le hs with hcuts | himp
  · exact Or.inr ⟨k, β, hβ, hs, hcuts⟩
  · exact Or.inl (improvement_of_rotate k himp)

end
end StructuralNote.LocalizedThreeArcDichotomy
