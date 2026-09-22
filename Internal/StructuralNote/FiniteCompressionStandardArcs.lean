import StructuralNote.FiniteCompressionArcExterior
import StructuralNote.FixedDualClassificationArcGrid

/-! Construct the background arc data from the actual three rounded arcs.
There is no background-drop or energy-gain hypothesis in this construction. -/

namespace StructuralNote.FiniteCompressionStandardArcs

open Real Erdos1045.EventualExact FiniteBox
open FixedDualClassificationStep FixedDualClassificationZeroArcs
open FixedDualClassificationExteriorGaps FixedDualClassificationArcGrid
open FiniteCompressionLocalizedBackground FiniteCompressionArcExterior
open FiniteCompressionArcAngles FiniteCompressionKernelGeometry
open FiniteCompressionBackgroundUniform FiniteCompressionConvolutionBase
noncomputable section

theorem standard_left_lower {m : ℕ} (hm : 0 < m) {β : ℝ}
    (hβ : 0 ≤ β) (hstep : gridStep m ≤ (Real.pi - 3) / 24) (k : ℕ) :
    zeroCenter β k - 1 / 8 - Real.pi / m < cellMidpoint (2 * m) (arcLeft m β k) := by
  have h := (standard_arc_midpoint_bounds hm hβ hstep k).1.2
  rw [cellMidpoint_succ_gridStep hm] at h
  change zeroCenter β k - 1 / 8 < cellMidpoint (2 * m) (arcLeft m β k) + Real.pi / m at h
  linarith

theorem standard_exteriorSigns {m : ℕ} (hm : 0 < m) (s : SignPattern hm) {β : ℝ}
    (hβ : 0 ≤ β) (hstep : gridStep m ≤ (Real.pi - 3) / 24)
    (hs : LocalizedSigns hm s β) :
    ExteriorSigns hm s (arcLeft m β 0) (arcRight m β 0)
      (arcLeft m β 1) (arcRight m β 1) (arcLeft m β 2) (arcRight m β 2) := by
  have h0 := standard_arc_midpoint_bounds hm hβ hstep 0
  have h1 := standard_arc_midpoint_bounds hm hβ hstep 1
  have h2 := standard_arc_midpoint_bounds hm hβ hstep 2
  exact exteriorSigns_of_midpoint_bounds hm s hs hstep
    (standard_left_lower hm hβ hstep 0) h0.1.1 h1.1.1 h2.1.1 h0.2.2 h1.2.2 h2.2.2

theorem standard_angle_bounds {m : ℕ} (hm : 0 < m) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβhi : β ≤ gridStep m) (hstep : gridStep m ≤ (Real.pi - 3) / 24)
    {j : ℕ} (hjL : arcLeft m β 0 ≤ j) (hjR : j ≤ arcRight m β 0) :
    compressionAngle m (j - arcLeft m β 0) ≤ Real.pi / 12 ∧
      Real.pi / 4 ≤ compressionAngle m (arcLeft m β 1 - j) ∧
      compressionAngle m (arcRight m β 1 - j) ≤ 5 * Real.pi / 12 ∧
      Real.pi / 4 ≤ compressionAngle m (j + m - arcRight m β 2) ∧
      compressionAngle m (j + m - arcLeft m β 2) ≤ 5 * Real.pi / 12 := by
  obtain ⟨h01, h12, h11, h23, h22, hlast, _⟩ := standard_arc_order hm hβ0 hβhi hstep
  have h0 := standard_arc_midpoint_bounds hm hβ0 hstep 0
  have h1 := standard_arc_midpoint_bounds hm hβ0 hstep 1
  have h2 := standard_arc_midpoint_bounds hm hβ0 hstep 2
  have hl1 := standard_left_lower hm hβ0 hstep 1
  have hl2 := standard_left_lower hm hβ0 hstep 2
  apply three_arc_angle_bounds hm (c := zeroCenter β 0) hstep hjL hjR
    (hjR.trans h12.le) (show arcRight m β 2 ≤ j + m by omega) h11 h22
    (standard_left_lower hm hβ0 hstep 0) h0.2.1
  · simpa [zeroCenter] using hl1
  · simpa [zeroCenter] using h1.2.1
  · simpa [zeroCenter] using hl2
  · simpa [zeroCenter] using h2.2.1

theorem standard_background_arcs {m : ℕ} (hm : 0 < m) (s : SignPattern hm) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβhi : β ≤ gridStep m) (hstep : gridStep m ≤ (Real.pi - 3) / 24)
    (hs : LocalizedSigns hm s β) {j : ℕ}
    (hjL : arcLeft m β 0 ≤ j) (hjR : j ≤ arcRight m β 0) :
    Nonempty (BackgroundArcs hm
      (localizedBackground hm (amplitude (2 * m)) s (arcLeft m β 0) (arcRight m β 0)) j) := by
  obtain ⟨h01, h12, h11, h23, h22, hlast, hR⟩ := standard_arc_order hm hβ0 hβhi hstep
  have hex := standard_exteriorSigns hm s hβ0 hstep hs
  have hv := localized_background_values hm (amplitude (2 * m)) s
    h01 h12 h11 h23 h22 hlast hR hex
  have hd := localized_background_increment_support hm (amplitude (2 * m)) s
    h01 h12 h11 h23 h22 hlast hR hex
  obtain ⟨hn, hflo, hfhi, hslo, hshi⟩ := standard_angle_bounds hm hβ0 hβhi hstep hjL hjR
  refine ⟨{
    start := arcLeft m β 0
    jump := arcLeft m β 0
    left₁ := arcLeft m β 1
    right₁ := arcRight m β 1
    left₂ := arcLeft m β 2
    right₂ := arcRight m β 2
    start_le := le_rfl
    jump_lt := by omega
    first_nonempty := h11
    separated := h23
    second_nonempty := h22
    last_lt := hlast
    outside := ?_
    jump_left := hv.2.2.2
    jump_right := hv.1 _ (by omega) (by omega)
    first_left := hv.1 _ (by omega) le_rfl
    first_right := hv.2.1 _ le_rfl (by omega)
    second_left := hv.2.1 _ (by omega) le_rfl
    second_right := hv.2.2.1 _ le_rfl (by omega)
    jump_le_site := hjL
    near_angle := hn
    site_le_first := hjR.trans h12.le
    first_angle_lo := hflo
    first_angle_hi := hfhi
    second_le_antipode := by omega
    second_angle_lo := hslo
    second_angle_hi := hshi }⟩
  intro t ht hne hnot1 hnot2
  apply hd t (Finset.mem_Ico.mp ht) hne
  · simpa only [Finset.mem_Icc, Set.mem_Icc] using hnot1
  · simpa only [Finset.mem_Icc, Set.mem_Icc] using hnot2

end
end StructuralNote.FiniteCompressionStandardArcs
