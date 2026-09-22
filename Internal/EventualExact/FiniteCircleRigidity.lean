import EventualExact.CircleForceDifference
import EventualExact.CyclicMaximum

/-! Finite circle rigidity for actual ordered periodic angle configurations.
The maximum estimate is instantiated with the cotangent secants, and its
auxiliary upper bound on the gaps is eliminated by the exact force budget. -/

namespace Erdos1045.EventualExact.FiniteCircleRigidity

open scoped BigOperators
open CyclicAngles CyclicCosecant CyclicForceBudget

noncomputable section

def gapDeviation {n : ℕ} (a : Angles n) : Fin n → ℝ :=
  fun i => relativeGaps a i - 1

def forceDifference {n : ℕ} (a : Angles n) : Fin n → ℝ :=
  fun i => circleForce (angleVector a) (cyclicAdvance i 1) - circleForce (angleVector a) i

def forceSquareSum {n : ℕ} (a : Angles n) : ℝ :=
  ∑ i, circleForce (angleVector a) i ^ 2

theorem forceSquareSum_nonneg {n : ℕ} (a : Angles n) : 0 ≤ forceSquareSum a :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem sum_relativeGaps {n : ℕ} (a : Angles n) (hn : 0 < n) :
    ∑ i, relativeGaps a i = (n : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  change (∑ i : Fin n, window a 1 i / (2 * Real.pi / n)) = _
  rw [← Finset.sum_range (fun i => window a 1 i / (2 * Real.pi / n)),
    ← Finset.sum_div, sum_window]
  field_simp [Real.pi_ne_zero]
  norm_num

theorem sum_gapDeviation {n : ℕ} (a : Angles n) (hn : 0 < n) :
    ∑ i, gapDeviation a i = 0 := by
  simp only [gapDeviation, Finset.sum_sub_distrib, sum_relativeGaps a hn,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, sub_self]

theorem gapDeviation_squareMass {n : ℕ} (a : Angles n) :
    finiteSquareMass (gapDeviation a) = gapSquareSum (relativeGaps a) := rfl

theorem actual_laplacian {n : ℕ} (a : Angles n) :
    weightedLaplacian (circleForceWeight a) (gapDeviation a) = -forceDifference a := by
  funext i
  simp only [weightedLaplacian, gapDeviation, sub_sub_sub_cancel_right,
    Pi.neg_apply, forceDifference, circleForce_next_difference, neg_neg]

theorem forceDifference_norm_le {n : ℕ} (a : Angles n) :
    ‖forceDifference a‖ ≤ 2 * ‖circleForce (angleVector a)‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  calc
    ‖forceDifference a i‖ ≤ ‖circleForce (angleVector a) (cyclicAdvance i 1)‖ +
        ‖circleForce (angleVector a) i‖ := norm_sub_le _ _
    _ ≤ ‖circleForce (angleVector a)‖ + ‖circleForce (angleVector a)‖ :=
      add_le_add (norm_le_pi_norm _ _) (norm_le_pi_norm _ _)
    _ = _ := by ring

/-- Equation (2.22), now for the actual circle forces and actual relative gaps. -/
theorem cubic_gap_bound {n : ℕ} (a : Angles n) (hn : 0 < n) {b : ℝ}
    (hb : ∀ i, relativeGaps a i ≤ b) :
    ‖gapDeviation a‖ ^ 3 ≤
      36 * Real.pi * b ^ 2 * gapSquareSum (relativeGaps a) * ‖forceDifference a‖ := by
  have hbpos : 0 < b :=
    (relativeGaps_pos a hn ⟨0, hn⟩).trans_le (hb ⟨0, hn⟩)
  have h := cyclic_cubic_maximum hn hbpos (sum_gapDeviation a hn)
    (circleForceWeight_nonneg a)
    (fun i j hji => circleForceWeight_lower a (Ne.symm hji) hb)
  rwa [gapDeviation_squareMass, actual_laplacian, norm_neg] at h

/-- The maximum estimate with its upper-gap parameter determined by the actual force. -/
theorem cubic_gap_bound_force_only {n : ℕ} (a : Angles n) (hn : 3 ≤ n) :
    ‖gapDeviation a‖ ^ 3 ≤
      36 * Real.pi * (2 + 3 * Real.pi ^ 2 * forceSquareSum a) ^ 2 *
        gapSquareSum (relativeGaps a) * ‖forceDifference a‖ :=
  cubic_gap_bound a (by omega) (each_gap_le_force a hn)

theorem cubic_gap_bound_force {n : ℕ} (a : Angles n) (hn : 0 < n) {b : ℝ}
    (hb : ∀ i, relativeGaps a i ≤ b) :
    ‖gapDeviation a‖ ^ 3 ≤
      72 * Real.pi * b ^ 2 * gapSquareSum (relativeGaps a) * ‖circleForce (angleVector a)‖ := by
  have hS : 0 ≤ gapSquareSum (relativeGaps a) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc
    _ ≤ 36 * Real.pi * b ^ 2 * gapSquareSum (relativeGaps a) * ‖forceDifference a‖ :=
      cubic_gap_bound a hn hb
    _ ≤ 36 * Real.pi * b ^ 2 * gapSquareSum (relativeGaps a) *
        (2 * ‖circleForce (angleVector a)‖) :=
      mul_le_mul_of_nonneg_left (forceDifference_norm_le a) (by positivity)
    _ = _ := by ring

/-- Equation (2.25). No upper-gap, force-representation, or weight hypotheses remain. -/
theorem finite_circle_rigidity {n : ℕ} (a : Angles n) (hn : 3 ≤ n) :
    ‖gapDeviation a‖ ^ 3 ≤
      54 * Real.pi ^ 3 * (2 + 3 * Real.pi ^ 2 * forceSquareSum a) ^ 3 *
        forceSquareSum a * ‖circleForce (angleVector a)‖ := by
  let b := 2 + 3 * Real.pi ^ 2 * forceSquareSum a
  have hT := forceSquareSum_nonneg a
  have hbpos : 0 < b := by dsimp [b]; positivity
  have hb : ∀ i, relativeGaps a i ≤ b := each_gap_le_force a hn
  have hS : gapSquareSum (relativeGaps a) ≤ (3 * Real.pi ^ 2 / 4) * b * forceSquareSum a :=
    gapSquareSum_le_force a hn hb
  calc
    _ ≤ 72 * Real.pi * b ^ 2 * gapSquareSum (relativeGaps a) * ‖circleForce (angleVector a)‖ :=
      cubic_gap_bound_force a (by omega) hb
    _ ≤ 72 * Real.pi * b ^ 2 * ((3 * Real.pi ^ 2 / 4) * b * forceSquareSum a) *
        ‖circleForce (angleVector a)‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS (by positivity)) (norm_nonneg _)
    _ = _ := by dsimp [b]; ring

/-- Vanishing force energy forces every actual relative gap to be exactly one. -/
theorem relativeGaps_eq_one_of_forceSquareSum_eq_zero {n : ℕ} (a : Angles n)
    (hn : 3 ≤ n) (hT : forceSquareSum a = 0) : ∀ i, relativeGaps a i = 1 := by
  have hr := relativeGaps_pos a (show 0 < n by omega)
  have h := totalGapDefect_le_force a hn
  change totalGapDefect (relativeGaps a) ≤ (3 * Real.pi ^ 2 / 2) * forceSquareSum a at h
  rw [hT, mul_zero] at h
  exact (totalGapDefect_eq_zero_iff _ hr).mp
    (le_antisymm h (totalGapDefect_nonneg _ hr))

end
end Erdos1045.EventualExact.FiniteCircleRigidity
