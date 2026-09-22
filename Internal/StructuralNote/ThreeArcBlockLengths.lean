import StructuralNote.FixedDualClassificationArcGrid
import StructuralNote.FiniteCompressionArcAngles
import StructuralNote.ThreeBlockKernelMargin

/-! Actual three-cut block lengths obtained from the rounded fixed zero arcs. -/

namespace StructuralNote.ThreeArcBlockLengths

open Real Set
open FixedDualClassificationStep FixedDualClassificationZeroArcs
open FixedDualClassificationArcGrid FiniteCompressionArcAngles
open FiniteCompressionKernelGeometry
open ThreeBlockKernelMargin
open scoped BigOperators

noncomputable section

theorem angle_nat_eq_compressionAngle {m r : ℕ} :
    ThreeBlockKernelMargin.angle m (r : ℤ) = compressionAngle m r := by
  unfold ThreeBlockKernelMargin.angle compressionAngle
  push_cast
  ring

private theorem arcLeft_midpoint_lower {m : ℕ} (hm : 0 < m) {β : ℝ}
    (hβ0 : 0 ≤ β) (hstep : gridStep m ≤ (Real.pi - 3) / 24) (k : ℕ) :
    zeroCenter β (k : ℤ) - 1 / 8 - gridStep m <
      cellMidpoint (2 * m) (arcLeft m β k) := by
  have h := (standard_arc_midpoint_bounds hm hβ0 hstep k).1.2
  rw [cellMidpoint_succ_gridStep hm] at h
  linarith

private theorem arc_point_midpoint_bounds {m : ℕ} (hm : 0 < m) {β : ℝ}
    (hβ0 : 0 ≤ β) (hstep : gridStep m ≤ (Real.pi - 3) / 24)
    {k j : ℕ} (hj : j ∈ Set.Icc (arcLeft m β k) (arcRight m β k)) :
    zeroCenter β (k : ℤ) - 1 / 8 - gridStep m <
        cellMidpoint (2 * m) j ∧
      cellMidpoint (2 * m) j ≤ zeroCenter β (k : ℤ) + 1 / 8 := by
  have hstd := standard_arc_midpoint_bounds hm hβ0 hstep k
  have hlo := arcLeft_midpoint_lower hm hβ0 hstep k
  rcases hj with ⟨hjL, hjR⟩
  constructor
  · exact hlo.trans_le (midpoint_monotone (2 * m) hjL)
  · exact (midpoint_monotone (2 * m) hjR).trans hstd.2.1

private theorem three_arc_error {m : ℕ}
    (hstep : gridStep m ≤ (Real.pi - 3) / 24) :
    1 / 4 + gridStep m < Real.pi / 12 := by
  nlinarith [Real.pi_gt_three]

theorem three_arc_block_lengths_and_angles {m : ℕ} (hm : 0 < m) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβhi : β ≤ gridStep m)
    (hstep : gridStep m ≤ (Real.pi - 3) / 24) {a b c : ℕ}
    (ha : a ∈ Set.Icc (arcLeft m β 0) (arcRight m β 0))
    (hb : b ∈ Set.Icc (arcLeft m β 1) (arcRight m β 1))
    (hc : c ∈ Set.Icc (arcLeft m β 2) (arcRight m β 2)) :
    0 < b - a ∧
      0 < c - b ∧
      0 < m + a - c ∧
      (b - a) + (c - b) + (m + a - c) = m ∧
      ThreeBlockKernelMargin.angle m ((b - a : ℕ) : ℤ) ∈
        Set.Icc (Real.pi / 4) (5 * Real.pi / 12) ∧
      ThreeBlockKernelMargin.angle m ((c - b : ℕ) : ℤ) ∈
        Set.Icc (Real.pi / 4) (5 * Real.pi / 12) ∧
      ThreeBlockKernelMargin.angle m ((m + a - c : ℕ) : ℤ) ∈
        Set.Icc (Real.pi / 4) (5 * Real.pi / 12) := by
  obtain ⟨h01, h12, h11, h23, h22, hlast, hR0⟩ :=
    standard_arc_order hm hβ0 hβhi hstep
  have hab : a < b := by
    exact lt_of_le_of_lt ha.2 (h12.trans_le hb.1)
  have hbc : b < c := by
    exact lt_of_le_of_lt hb.2 (h23.trans_le hc.1)
  have hca : c < m + a := by
    have hcm : c < arcLeft m β 0 + m := lt_of_le_of_lt hc.2 hlast
    have hma : arcLeft m β 0 + m ≤ m + a := by
      calc
        arcLeft m β 0 + m ≤ a + m := Nat.add_le_add_right ha.1 m
        _ = m + a := Nat.add_comm _ _
    exact hcm.trans_le hma
  have hpos₁ : 0 < b - a := Nat.sub_pos_of_lt hab
  have hpos₂ : 0 < c - b := Nat.sub_pos_of_lt hbc
  have hpos₃ : 0 < m + a - c := Nat.sub_pos_of_lt hca
  have hsum : (b - a) + (c - b) + (m + a - c) = m := by
    omega
  have ha_mid := arc_point_midpoint_bounds hm hβ0 hstep ha
  have hb_mid := arc_point_midpoint_bounds hm hβ0 hstep hb
  have hc_mid := arc_point_midpoint_bounds hm hβ0 hstep hc
  have hc01 : zeroCenter β (1 : ℤ) =
      zeroCenter β (0 : ℤ) + Real.pi / 3 := by
    unfold zeroCenter
    push_cast
    ring
  have hc12 : zeroCenter β (2 : ℤ) =
      zeroCenter β (1 : ℤ) + Real.pi / 3 := by
    unfold zeroCenter
    push_cast
    ring
  have herror := three_arc_error hstep
  have hab_lo : Real.pi / 3 - (1 / 4 + gridStep m) <
      cellMidpoint (2 * m) b - cellMidpoint (2 * m) a := by
    nlinarith [ha_mid.2, hb_mid.1, hc01]
  have hab_hi : cellMidpoint (2 * m) b - cellMidpoint (2 * m) a ≤
      Real.pi / 3 + (1 / 4 + gridStep m) := by
    nlinarith [ha_mid.1, hb_mid.2, hc01]
  have hbc_lo : Real.pi / 3 - (1 / 4 + gridStep m) <
      cellMidpoint (2 * m) c - cellMidpoint (2 * m) b := by
    nlinarith [hb_mid.2, hc_mid.1, hc12]
  have hbc_hi : cellMidpoint (2 * m) c - cellMidpoint (2 * m) b ≤
      Real.pi / 3 + (1 / 4 + gridStep m) := by
    nlinarith [hb_mid.1, hc_mid.2, hc12]
  have hma_mid_lo : zeroCenter β (0 : ℤ) + Real.pi -
      1 / 8 - gridStep m < cellMidpoint (2 * m) (a + m) := by
    rw [midpoint_half_period hm]
    nlinarith [ha_mid.1]
  have hma_mid_hi : cellMidpoint (2 * m) (a + m) ≤
      zeroCenter β (0 : ℤ) + Real.pi + 1 / 8 := by
    rw [midpoint_half_period hm]
    nlinarith [ha_mid.2]
  have h02 : zeroCenter β (2 : ℤ) =
      zeroCenter β (0 : ℤ) + 2 * Real.pi / 3 := by
    rw [hc12, hc01]
    ring
  have hca_lo : Real.pi / 3 - (1 / 4 + gridStep m) <
      cellMidpoint (2 * m) (a + m) - cellMidpoint (2 * m) c := by
    linarith only [hma_mid_lo, hc_mid.2, h02]
  have hca_hi : cellMidpoint (2 * m) (a + m) - cellMidpoint (2 * m) c ≤
      Real.pi / 3 + (1 / 4 + gridStep m) := by
    linarith only [hma_mid_hi, hc_mid.1, h02]
  have hab_comp : compressionAngle m (b - a) ∈
      Set.Icc (Real.pi / 4) (5 * Real.pi / 12) := by
    rw [compressionAngle_eq_midpoint_sub hab.le]
    constructor
    · linarith only [hab_lo, herror]
    · linarith only [hab_hi, herror]
  have hbc_comp : compressionAngle m (c - b) ∈
      Set.Icc (Real.pi / 4) (5 * Real.pi / 12) := by
    rw [compressionAngle_eq_midpoint_sub hbc.le]
    constructor
    · linarith only [hbc_lo, herror]
    · linarith only [hbc_hi, herror]
  have hca_comp : compressionAngle m (m + a - c) ∈
      Set.Icc (Real.pi / 4) (5 * Real.pi / 12) := by
    have hca' : c ≤ a + m := by omega
    have hca_lo' : Real.pi / 3 - (1 / 4 + gridStep m) <
        cellMidpoint (2 * m) a + Real.pi - cellMidpoint (2 * m) c := by
      rw [← midpoint_half_period hm a]
      exact hca_lo
    have hca_hi' : cellMidpoint (2 * m) a + Real.pi -
        cellMidpoint (2 * m) c ≤
        Real.pi / 3 + (1 / 4 + gridStep m) := by
      rw [← midpoint_half_period hm a]
      exact hca_hi
    rw [show m + a - c = a + m - c by omega,
      compressionAngle_reflected hm hca']
    constructor
    · linarith only [hca_lo', herror]
    · linarith only [hca_hi', herror]
  have hab_angle : ThreeBlockKernelMargin.angle m ((b - a : ℕ) : ℤ) ∈
      Set.Icc (Real.pi / 4) (5 * Real.pi / 12) := by
    have he := angle_nat_eq_compressionAngle (m := m) (r := b - a)
    exact he.symm ▸ hab_comp
  have hbc_angle : ThreeBlockKernelMargin.angle m ((c - b : ℕ) : ℤ) ∈
      Set.Icc (Real.pi / 4) (5 * Real.pi / 12) := by
    have he := angle_nat_eq_compressionAngle (m := m) (r := c - b)
    exact he.symm ▸ hbc_comp
  have hca_angle : ThreeBlockKernelMargin.angle m ((m + a - c : ℕ) : ℤ) ∈
      Set.Icc (Real.pi / 4) (5 * Real.pi / 12) := by
    have he := angle_nat_eq_compressionAngle (m := m) (r := m + a - c)
    exact he.symm ▸ hca_comp
  exact ⟨hpos₁, hpos₂, hpos₃, hsum, hab_angle, hbc_angle, hca_angle⟩

theorem three_arc_block_lengths {m : ℕ} (hm : 0 < m) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβhi : β ≤ gridStep m)
    (hstep : gridStep m ≤ (Real.pi - 3) / 24) {a b c : ℕ}
    (ha : a ∈ Set.Icc (arcLeft m β 0) (arcRight m β 0))
    (hb : b ∈ Set.Icc (arcLeft m β 1) (arcRight m β 1))
    (hc : c ∈ Set.Icc (arcLeft m β 2) (arcRight m β 2)) :
    0 < b - a ∧ 0 < c - b ∧ 0 < m + a - c ∧
      (b - a) + (c - b) + (m + a - c) = m := by
  have h := three_arc_block_lengths_and_angles hm hβ0 hβhi hstep ha hb hc
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem three_arc_block_angle_bounds {m : ℕ} (hm : 0 < m) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβhi : β ≤ gridStep m)
    (hstep : gridStep m ≤ (Real.pi - 3) / 24) {a b c : ℕ}
    (ha : a ∈ Set.Icc (arcLeft m β 0) (arcRight m β 0))
    (hb : b ∈ Set.Icc (arcLeft m β 1) (arcRight m β 1))
    (hc : c ∈ Set.Icc (arcLeft m β 2) (arcRight m β 2)) :
    ThreeBlockKernelMargin.angle m ((b - a : ℕ) : ℤ) ∈
        Set.Icc (Real.pi / 4) (5 * Real.pi / 12) ∧
      ThreeBlockKernelMargin.angle m ((c - b : ℕ) : ℤ) ∈
        Set.Icc (Real.pi / 4) (5 * Real.pi / 12) ∧
      ThreeBlockKernelMargin.angle m ((m + a - c : ℕ) : ℤ) ∈
        Set.Icc (Real.pi / 4) (5 * Real.pi / 12) := by
  have h := three_arc_block_lengths_and_angles hm hβ0 hβhi hstep ha hb hc
  exact ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem three_arc_block_angles_in_enlarged_window
    {m : ℕ} (hm : 0 < m) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβhi : β ≤ gridStep m)
    (hstep : gridStep m ≤ (Real.pi - 3) / 24) {a b c : ℕ}
    (ha : a ∈ Set.Icc (arcLeft m β 0) (arcRight m β 0))
    (hb : b ∈ Set.Icc (arcLeft m β 1) (arcRight m β 1))
    (hc : c ∈ Set.Icc (arcLeft m β 2) (arcRight m β 2))
    {αₑ βₑ : ℝ} (hαₑ : αₑ < Real.pi / 4)
    (hβₑ : 5 * Real.pi / 12 < βₑ) :
    ThreeBlockKernelMargin.angle m ((b - a : ℕ) : ℤ) ∈ Set.Icc αₑ βₑ ∧
      ThreeBlockKernelMargin.angle m ((c - b : ℕ) : ℤ) ∈ Set.Icc αₑ βₑ ∧
      ThreeBlockKernelMargin.angle m ((m + a - c : ℕ) : ℤ) ∈
        Set.Icc αₑ βₑ := by
  have h := three_arc_block_angle_bounds hm hβ0 hβhi hstep ha hb hc
  constructor
  · exact ⟨hαₑ.le.trans h.1.1, h.1.2.trans hβₑ.le⟩
  constructor
  · exact ⟨hαₑ.le.trans h.2.1.1, h.2.1.2.trans hβₑ.le⟩
  · exact ⟨hαₑ.le.trans h.2.2.1, h.2.2.2.trans hβₑ.le⟩

end
end StructuralNote.ThreeArcBlockLengths
