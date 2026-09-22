import StructuralNote.FixedDualClassificationGridPeriodicity
import StructuralNote.FiniteCompressionKernelGeometry
import Mathlib.Algebra.Order.Floor.Ring

/-! Grid geometry for the three fixed zero arcs in unwrapped coordinates. -/

namespace StructuralNote.FixedDualClassificationArcGrid

open Real Set
open StructuralNote.FixedDualClassificationStep
open StructuralNote.FixedDualClassificationZeroArcs
open StructuralNote.FixedDualClassificationGridPeriodicity
open StructuralNote.FiniteCompressionKernelGeometry

noncomputable section

def gridStep (m : ℕ) : ℝ := Real.pi / (m : ℝ)

def cutIndex (m : ℕ) (x : ℝ) : ℕ :=
  ⌊x * (m : ℝ) / Real.pi - 1 / 2⌋₊

def arcLeft (m : ℕ) (β : ℝ) (k : ℕ) : ℕ :=
  cutIndex m (zeroCenter β (k : ℤ) - 1 / 8)

def arcRight (m : ℕ) (β : ℝ) (k : ℕ) : ℕ :=
  cutIndex m (zeroCenter β (k : ℤ) + 1 / 8)

theorem gridStep_pos {m : ℕ} (hm : 0 < m) : 0 < gridStep m := by
  unfold gridStep
  positivity

theorem cellMidpoint_succ_gridStep {m : ℕ} (hm : 0 < m) (j : ℕ) :
    cellMidpoint (2 * m) (j + 1) =
      cellMidpoint (2 * m) j + gridStep m := by
  unfold cellMidpoint gridStep
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp [hmR]
  ring

theorem cutIndex_midpoint_bounds {m : ℕ} (hm : 0 < m) {x : ℝ}
    (hx : gridStep m / 2 ≤ x) :
    cellMidpoint (2 * m) (cutIndex m x) ≤ x ∧
      x < cellMidpoint (2 * m) (cutIndex m x + 1) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hx' : Real.pi / 2 ≤ x * (m : ℝ) := by
    apply (div_le_iff₀ hmR).mp
    calc
      (Real.pi / 2) / (m : ℝ) = (Real.pi / (m : ℝ)) / 2 := by
        field_simp
      _ = gridStep m / 2 := by rfl
      _ ≤ x := hx
  have hratio : (1 / 2 : ℝ) ≤ x * (m : ℝ) / Real.pi := by
    apply (le_div_iff₀ hpi).mpr
    nlinarith [hx']
  have hy : 0 ≤ x * (m : ℝ) / Real.pi - 1 / 2 := by linarith
  have hlo : (cutIndex m x : ℝ) ≤ x * (m : ℝ) / Real.pi - 1 / 2 := by
    simpa only [cutIndex] using Nat.floor_le hy
  have hhi : x * (m : ℝ) / Real.pi - 1 / 2 <
      (cutIndex m x : ℝ) + 1 := by
    simpa only [cutIndex] using Nat.lt_floor_add_one _
  have hmid (q : ℕ) :
      cellMidpoint (2 * m) q = ((q : ℝ) + 1 / 2) * gridStep m := by
    unfold cellMidpoint gridStep
    push_cast
    field_simp [ne_of_gt hmR]
  have hratio_eq :
      (x * (m : ℝ) / Real.pi) * gridStep m = x := by
    unfold gridStep
    field_simp [ne_of_gt hmR, ne_of_gt hpi]
  constructor
  · calc
      cellMidpoint (2 * m) (cutIndex m x) =
          ((cutIndex m x : ℝ) + 1 / 2) * gridStep m := hmid _
      _ ≤
          (x * (m : ℝ) / Real.pi) * gridStep m := by
        exact mul_le_mul_of_nonneg_right (by linarith) (gridStep_pos hm).le
      _ = x := hratio_eq
  · calc
      x = (x * (m : ℝ) / Real.pi) * gridStep m := hratio_eq.symm
      _ < ((cutIndex m x : ℝ) + 3 / 2) * gridStep m := by
        have hupper : x * (m : ℝ) / Real.pi < (cutIndex m x : ℝ) + 3 / 2 := by
          linarith
        exact mul_lt_mul_of_pos_right hupper (gridStep_pos hm)
      _ = (((cutIndex m x + 1 : ℕ) : ℝ) + 1 / 2) * gridStep m := by
        congr 1
        push_cast
        ring
      _ = cellMidpoint (2 * m) (cutIndex m x + 1) := by
        exact (hmid _).symm

theorem cutIndex_mono {m : ℕ} (hm : 0 < m) {x y : ℝ} (hxy : x ≤ y) :
    cutIndex m x ≤ cutIndex m y := by
  unfold cutIndex
  apply Nat.floor_mono
  gcongr

theorem cutIndex_lt_of_gap {m : ℕ} (hm : 0 < m) {x y : ℝ}
    (hx : gridStep m / 2 ≤ x) (hy : gridStep m / 2 ≤ y)
    (hgap : x + gridStep m ≤ y) :
    cutIndex m x < cutIndex m y := by
  have hxmid := cutIndex_midpoint_bounds hm hx
  have hymid := cutIndex_midpoint_bounds hm hy
  by_contra hnot
  have hle : cutIndex m y ≤ cutIndex m x := Nat.le_of_not_gt hnot
  have hmono : cellMidpoint (2 * m) (cutIndex m y + 1) ≤
      cellMidpoint (2 * m) (cutIndex m x + 1) := by
    unfold cellMidpoint
    gcongr
  have hupper : y < cellMidpoint (2 * m) (cutIndex m x + 1) :=
    hymid.2.trans_le hmono
  have hstep := cellMidpoint_succ_gridStep hm (cutIndex m x)
  linarith [hxmid.1, hgap]

theorem cutIndex_add_pi {m : ℕ} (hm : 0 < m) {x : ℝ}
    (hx : gridStep m / 2 ≤ x) :
    cutIndex m (x + Real.pi) = cutIndex m x + m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have harg :
      (x + Real.pi) * (m : ℝ) / Real.pi - 1 / 2 =
        (x * (m : ℝ) / Real.pi - 1 / 2) + (m : ℝ) := by
    field_simp [ne_of_gt Real.pi_pos]
    ring
  have hx0 : 0 ≤ x * (m : ℝ) / Real.pi - 1 / 2 := by
    have hratio : (1 / 2 : ℝ) ≤ x * (m : ℝ) / Real.pi := by
      apply (le_div_iff₀ Real.pi_pos).mpr
      have hx' : Real.pi / 2 ≤ x * (m : ℝ) := by
        apply (div_le_iff₀ hmR).mp
        calc
          (Real.pi / 2) / (m : ℝ) = gridStep m / 2 := by
            unfold gridStep
            field_simp
          _ ≤ x := hx
      nlinarith
    linarith
  unfold cutIndex
  rw [harg, Nat.floor_add_natCast hx0]

theorem cutIndex_argument_nonneg {m : ℕ} (hm : 0 < m) {x : ℝ}
    (hx : gridStep m / 2 ≤ x) :
    0 ≤ x * (m : ℝ) / Real.pi - 1 / 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hx' : Real.pi / 2 ≤ x * (m : ℝ) := by
    apply (div_le_iff₀ hmR).mp
    calc
      (Real.pi / 2) / (m : ℝ) = gridStep m / 2 := by
        unfold gridStep
        field_simp
      _ ≤ x := hx
  have hratio : (1 / 2 : ℝ) ≤ x * (m : ℝ) / Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).mpr
    nlinarith [hx']
  linarith

theorem arcLeft_midpoint_bounds {m : ℕ} (hm : 0 < m) (β : ℝ) (k : ℕ)
    (hboundary : gridStep m / 2 ≤ zeroCenter β (k : ℤ) - 1 / 8) :
    cellMidpoint (2 * m) (arcLeft m β k) ≤
        zeroCenter β (k : ℤ) - 1 / 8 ∧
      zeroCenter β (k : ℤ) - 1 / 8 <
        cellMidpoint (2 * m) (arcLeft m β k + 1) := by
  simpa only [arcLeft] using
    (cutIndex_midpoint_bounds hm hboundary)

theorem arcRight_midpoint_bounds {m : ℕ} (hm : 0 < m) (β : ℝ) (k : ℕ)
    (hboundary : gridStep m / 2 ≤ zeroCenter β (k : ℤ) + 1 / 8) :
    cellMidpoint (2 * m) (arcRight m β k) ≤
        zeroCenter β (k : ℤ) + 1 / 8 ∧
      zeroCenter β (k : ℤ) + 1 / 8 <
        cellMidpoint (2 * m) (arcRight m β k + 1) := by
  simpa only [arcRight] using
    (cutIndex_midpoint_bounds hm hboundary)

theorem arc_boundary_lower {m : ℕ} (_hm : 0 < m) {β : ℝ}
    (hβ0 : 0 ≤ β) (hstep : gridStep m ≤ (Real.pi - 3) / 24) (k : ℕ) :
    gridStep m / 2 ≤ zeroCenter β (k : ℤ) - 1 / 8 := by
  have hsmall : gridStep m / 2 ≤ (Real.pi - 3) / 48 := by
    linarith
  have hbase : (Real.pi - 3) / 48 ≤ Real.pi / 6 - 1 / 8 := by
    nlinarith [Real.pi_gt_three]
  unfold zeroCenter
  push_cast
  have hk : (0 : ℝ) ≤ k := by positivity
  nlinarith [Real.pi_pos]

theorem arc_boundary_right_lower {m : ℕ} (_hm : 0 < m) {β : ℝ}
    (hβ0 : 0 ≤ β) (hstep : gridStep m ≤ (Real.pi - 3) / 24) (k : ℕ) :
    gridStep m / 2 ≤ zeroCenter β (k : ℤ) + 1 / 8 := by
  exact (arc_boundary_lower _hm hβ0 hstep k).trans (by linarith)

theorem standard_arc_midpoint_bounds {m : ℕ} (hm : 0 < m) {β : ℝ}
    (hβ0 : 0 ≤ β) (hstep : gridStep m ≤ (Real.pi - 3) / 24) (k : ℕ) :
    (cellMidpoint (2 * m) (arcLeft m β k) ≤
        zeroCenter β (k : ℤ) - 1 / 8 ∧
      zeroCenter β (k : ℤ) - 1 / 8 <
        cellMidpoint (2 * m) (arcLeft m β k + 1)) ∧
    (cellMidpoint (2 * m) (arcRight m β k) ≤
        zeroCenter β (k : ℤ) + 1 / 8 ∧
      zeroCenter β (k : ℤ) + 1 / 8 <
        cellMidpoint (2 * m) (arcRight m β k + 1)) := by
  exact ⟨arcLeft_midpoint_bounds hm β k (arc_boundary_lower hm hβ0 hstep k),
    arcRight_midpoint_bounds hm β k (arc_boundary_right_lower hm hβ0 hstep k)⟩

theorem standard_arc_order {m : ℕ} (hm : 0 < m) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβhi : β ≤ gridStep m)
    (hstep : gridStep m ≤ (Real.pi - 3) / 24) :
    arcLeft m β 0 < arcRight m β 0 ∧
      arcRight m β 0 < arcLeft m β 1 ∧
      arcLeft m β 1 ≤ arcRight m β 1 ∧
      arcRight m β 1 < arcLeft m β 2 ∧
      arcLeft m β 2 ≤ arcRight m β 2 ∧
      arcRight m β 2 < arcLeft m β 0 + m ∧
      arcRight m β 0 < m := by
  have hL0 := arc_boundary_lower hm hβ0 hstep 0
  have hR0 := arc_boundary_right_lower hm hβ0 hstep 0
  have hL1 := arc_boundary_lower hm hβ0 hstep 1
  have hR1 := arc_boundary_right_lower hm hβ0 hstep 1
  have hL2 := arc_boundary_lower hm hβ0 hstep 2
  have hR2 := arc_boundary_right_lower hm hβ0 hstep 2
  have hquart : gridStep m ≤ 1 / 4 := by
    nlinarith [hstep, Real.pi_lt_four]
  have hc01 : zeroCenter β (1 : ℤ) = zeroCenter β (0 : ℤ) + Real.pi / 3 := by
    unfold zeroCenter
    push_cast
    ring
  have hc12 : zeroCenter β (2 : ℤ) = zeroCenter β (1 : ℤ) + Real.pi / 3 := by
    unfold zeroCenter
    push_cast
    ring
  have hgap0 :
      zeroCenter β (0 : ℤ) - 1 / 8 + gridStep m ≤
        zeroCenter β (0 : ℤ) + 1 / 8 := by
    linarith
  have hgap01 :
      zeroCenter β (0 : ℤ) + 1 / 8 + gridStep m ≤
        zeroCenter β (1 : ℤ) - 1 / 8 := by
    rw [hc01]
    nlinarith [hstep, Real.pi_gt_three]
  have hgap12 :
      zeroCenter β (1 : ℤ) + 1 / 8 + gridStep m ≤
        zeroCenter β (2 : ℤ) - 1 / 8 := by
    rw [hc12]
    nlinarith [hstep, Real.pi_gt_three]
  have hgap2period :
      zeroCenter β (2 : ℤ) + 1 / 8 + gridStep m ≤
        zeroCenter β (0 : ℤ) - 1 / 8 + Real.pi := by
    rw [hc12, hc01]
    nlinarith [hstep, Real.pi_gt_three]
  have h01 := cutIndex_lt_of_gap hm hL0 hR0 hgap0
  have h12 := cutIndex_lt_of_gap hm hR0 hL1 hgap01
  have h23 := cutIndex_lt_of_gap hm hR1 hL2 hgap12
  have h30 := cutIndex_lt_of_gap hm hR2
    (show gridStep m / 2 ≤ zeroCenter β (0 : ℤ) - 1 / 8 + Real.pi by
      linarith [hL0, Real.pi_pos]) hgap2period
  have hL01 : cutIndex m (zeroCenter β (0 : ℤ) - 1 / 8) ≤
      cutIndex m (zeroCenter β (0 : ℤ) + 1 / 8) :=
    cutIndex_mono hm (by linarith)
  have hL12 : cutIndex m (zeroCenter β (1 : ℤ) - 1 / 8) ≤
      cutIndex m (zeroCenter β (1 : ℤ) + 1 / 8) :=
    cutIndex_mono hm (by linarith)
  have hL22 : cutIndex m (zeroCenter β (2 : ℤ) - 1 / 8) ≤
      cutIndex m (zeroCenter β (2 : ℤ) + 1 / 8) :=
    cutIndex_mono hm (by linarith)
  have hL0period : gridStep m / 2 ≤
      zeroCenter β (0 : ℤ) - 1 / 8 + Real.pi := by
    linarith [hL0, Real.pi_pos]
  have hperiod := cutIndex_add_pi (x := zeroCenter β (0 : ℤ) - 1 / 8) hm hL0
  have hR0arg : zeroCenter β (0 : ℤ) + 1 / 8 <
      Real.pi + gridStep m / 2 := by
    unfold zeroCenter
    push_cast
    nlinarith [hβhi, hstep, Real.pi_gt_three]
  have hR0arg' :
      (zeroCenter β (0 : ℤ) + 1 / 8) * (m : ℝ) / Real.pi - 1 / 2 <
        (m : ℝ) := by
    apply (sub_lt_iff_lt_add).2
    apply (div_lt_iff₀ Real.pi_pos).2
    have hmul := mul_lt_mul_of_pos_right hR0arg
      (show (0 : ℝ) < m by exact_mod_cast hm)
    have heq : (Real.pi + gridStep m / 2) * (m : ℝ) =
        ((m : ℝ) + 1 / 2) * Real.pi := by
      unfold gridStep
      field_simp
    rw [heq] at hmul
    exact hmul
  have hR0ltm : arcRight m β 0 < m := by
    unfold arcRight
    apply (Nat.floor_lt (by
      exact (cutIndex_argument_nonneg hm hR0))).mpr
    exact hR0arg'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hR0ltm⟩
  · simpa only [arcLeft, arcRight] using h01
  · simpa only [arcLeft, arcRight] using h12
  · exact hL12
  · simpa only [arcLeft, arcRight] using h23
  · exact hL22
  · have h30' := h30
    rw [hperiod] at h30'
    simpa [arcLeft, arcRight] using h30'

end
end StructuralNote.FixedDualClassificationArcGrid
