import StructuralNote.FiniteCompressionStandardArcs
import StructuralNote.LocalizedArcDichotomy
import StructuralNote.TerminalSlideBackground

/-! A localized word either has a single transition in its first descending
arc, or admits an actual two-site improvement. All background data are constructed. -/

namespace StructuralNote.LocalizedTerminalImprovement

open Real Filter Erdos1045.EventualExact FourierMultiplier FiniteBox
open FixedDualClassificationFinite FixedDualClassificationExteriorGaps
open FixedDualClassificationArcGrid FiniteCompressionLocalizedBackground
open FiniteCompressionStandardArcs FiniteCompressionArcAngles
open FiniteCompressionKernelGeometry FiniteCompressionRanked
open SolTerminalComponent SolWordHamming LocalizedArcDichotomy
open SignPatternSymmetry SignPatternEnergySymmetry FixedDualClassificationNormalizedSigns
open scoped Topology
noncomputable section

def TwoSiteImprovement {m : ℕ} (hm : 0 < m) (η : ℝ) (s : SignPattern hm) : Prop :=
  ∃ t : SignPattern hm, hamming s t ≤ 2 ∧
    η / (2 * m : ℕ) ^ 2 ≤
      normalizedBoxEnergy (operator (2 * m)) (vertex (amplitude (2 * m)) t) -
        normalizedBoxEnergy (operator (2 * m)) (vertex (amplitude (2 * m)) s)

theorem improvement_of_rotate {m : ℕ} {hm : 0 < m} {η : ℝ} {s : SignPattern hm}
    (k : ℕ) (h : TwoSiteImprovement hm η (rotatePattern k s)) :
    TwoSiteImprovement hm η s :=
  improvement_transport_rotatePattern (amplitude (2 * m)) k s h

theorem improvement_of_negate {m : ℕ} {hm : 0 < m} {η : ℝ} {s : SignPattern hm}
    (h : TwoSiteImprovement hm η (globalNegate s)) : TwoSiteImprovement hm η s :=
  improvement_transport_globalNegate (amplitude (2 * m)) s h

theorem improvement_deficit {m : ℕ} {hm : 0 < m} {η : ℝ} {s : SignPattern hm}
    (h : TwoSiteImprovement hm η s) :
    ∃ t : SignPattern hm, hamming s t ≤ 2 ∧ 0 ≤ deficit hm t ∧
      deficit hm t + η / (2 * m : ℕ) ^ 2 ≤ deficit hm s := by
  obtain ⟨t, hh, hg⟩ := h
  have hu := energy_le_B hm (vertex_mem_box (amplitude_pos (by omega)).le t)
  refine ⟨t, hh, sub_nonneg.mpr hu, ?_⟩
  dsimp only [deficit]
  linarith

theorem standard_arc_short_span {m : ℕ} (hm : 0 < m) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβhi : β ≤ gridStep m) (hstep : gridStep m ≤ (Real.pi - 3) / 24) :
    2 * Real.pi * (arcRight m β 0 - (arcLeft m β 0 + 1) : ℕ) / (2 * m : ℝ) ≤
      Real.pi / 12 := by
  have horder := standard_arc_order hm hβ0 hβhi hstep
  have ha := (standard_angle_bounds hm hβ0 hβhi hstep horder.1.le le_rfl).1
  have hsub : arcRight m β 0 - (arcLeft m β 0 + 1) ≤
      arcRight m β 0 - arcLeft m β 0 := by omega
  calc
    _ ≤ 2 * Real.pi * (arcRight m β 0 - arcLeft m β 0 : ℕ) / (2 * m : ℝ) := by
      gcongr
    _ = compressionAngle m (arcRight m β 0 - arcLeft m β 0) := by
      unfold compressionAngle
      push_cast
      ring
    _ ≤ _ := ha

theorem eventually_first_arc_dichotomy : ∃ η : ℝ, 0 < η ∧
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 0 < m) (s : SignPattern hm) (β : ℝ),
      0 ≤ β → β ≤ gridStep m → LocalizedSigns hm s β →
      (∃ cut ∈ Set.Icc (arcLeft m β 0) (arcRight m β 0),
        ∀ j ∈ Set.Icc (arcLeft m β 0) (arcRight m β 0 + 1),
          patternSign s (site hm j) = if j ≤ cut then 1 else -1) ∨
        TwoSiteImprovement hm η s := by
  obtain ⟨η, hη, hevent⟩ := TerminalSlideBackground.eventually_two_site_improvement
  refine ⟨η, hη, ?_⟩
  filter_upwards [hevent, eventually_small_grid_step] with m hslide hstep
  intro hm s β hβ0 hβhi hs
  obtain ⟨h01, h12, h11, h23, h22, hlast, hR⟩ := standard_arc_order hm hβ0 hβhi hstep
  have hex := standard_exteriorSigns hm s hβ0 hstep hs
  let E := localizedPositiveSites hm s (arcLeft m β 0) (arcRight m β 0)
  have hsupport : ∀ x ∈ E, arcLeft m β 0 + 1 ≤ x ∧ x ≤ arcRight m β 0 := by
    intro x hx
    exact Finset.mem_Icc.mp (Finset.mem_filter.mp hx).1
  have hsign : ∀ j, arcLeft m β 0 + 1 ≤ j → j ≤ arcRight m β 0 →
      (j ∈ E ↔ patternSign s (site hm j) = 1) := by
    intro j hjL hjR
    simp only [E, localizedPositiveSites, Finset.mem_filter, Finset.mem_Icc]
    exact and_iff_right ⟨hjL, hjR⟩
  rcases localized_arc_dichotomy s h01.le hex.1
      (hex.2.1 _ (by omega) (by omega)) E hsupport hsign with hbad | hgood
  · right
    obtain ⟨hE, hnot⟩ := hbad
    have harcs : ∀ k, terminalLeft E hE ≤ k → k ≤ terminalRight E hE →
        Nonempty (FiniteCompressionBackgroundUniform.BackgroundArcs hm
          (localizedBackground hm (amplitude (2 * m)) s (arcLeft m β 0) (arcRight m β 0))
          (k - 1)) := by
      intro k hkL hkR
      have hk := hsupport k (terminal_interval E hE hkL hkR)
      exact standard_background_arcs hm s hβ0 hβhi hstep hs (by omega) (by omega)
    obtain ⟨t, hh, hg, _⟩ := hslide hm E hE (arcLeft m β 0 + 1) (arcRight m β 0) s
      hR (standard_arc_short_span hm hβ0 hβhi hstep) hnot hsupport hsign harcs
    exact ⟨t, hh, hg⟩
  · exact Or.inl hgood

theorem eventually_near_maximum_first_arc (C₀ : ℝ) : ∃ η : ℝ, 0 < η ∧
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 0 < m) (s : SignPattern hm),
      deficit hm s ≤ C₀ / (2 * m : ℝ) ^ 2 →
      TwoSiteImprovement hm η s ∨
        ∃ k : ℕ, ∃ β ∈ Set.Ico 0 (gridStep m),
          LocalizedSigns hm (rotatePattern k s) β ∧
          ∃ cut ∈ Set.Icc (arcLeft m β 0) (arcRight m β 0),
            ∀ j ∈ Set.Icc (arcLeft m β 0) (arcRight m β 0 + 1),
              patternSign (rotatePattern k s) (site hm j) = if j ≤ cut then 1 else -1 := by
  obtain ⟨η, hη, hevent⟩ := eventually_first_arc_dichotomy
  refine ⟨η, hη, ?_⟩
  filter_upwards [hevent, eventually_normalized_localization C₀] with m hfirst hloc
  intro hm s hdef
  obtain ⟨k, β, hβ, hs, _⟩ := hloc hm s hdef
  rcases hfirst hm (rotatePattern k s) β hβ.1 hβ.2.le hs with hcut | himp
  · exact Or.inr ⟨k, β, hβ, hs, hcut⟩
  · exact Or.inl (improvement_of_rotate k himp)

end
end StructuralNote.LocalizedTerminalImprovement
