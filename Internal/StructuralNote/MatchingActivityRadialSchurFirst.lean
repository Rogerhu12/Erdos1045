import StructuralNote.MatchingActivityRadialCenterFirst
import StructuralNote.CommonFiberSchurExpansion

/-! The Schur main term of the first center derivative with the physical
velocity retained. The residual costs only the square root of its energy. -/

namespace StructuralNote.MatchingActivityRadialSchurFirst

open Erdos1045 Erdos1045.EventualExact Complex Configuration
open GeometricRelativeRemainder SchurLift SchurSpectrum FourierMultiplier QuadraticStability
open CommonFiberSchurExpansion SignedPressureAngular
open scoped BigOperators
noncomputable section

def quadraticFirst {n : ℕ} (D C U : Points n) : ℝ :=
  -(∑ p : Fin n × Fin n, (quotient C D p * quotient U D p).re)

theorem quadratic_add {n : ℕ} (D C U : Points n) :
    quadratic D (C + U) = quadratic D C + quadratic D U + quadraticFirst D C U := by
  have hq (p : Fin n × Fin n) : quotient (C + U) D p = quotient C D p + quotient U D p := by
    unfold quotient
    simp only [Pi.add_apply]
    rw [← add_div]
    congr 1
    ring
  have he (p : Fin n × Fin n) : (quotient (C + U) D p ^ 2).re =
      (quotient C D p ^ 2).re + (quotient U D p ^ 2).re + 2 * (quotient C D p * quotient U D p).re := by
    rw [hq, show (quotient C D p + quotient U D p) ^ 2 = quotient C D p ^ 2 + quotient U D p ^ 2 +
      2 * (quotient C D p * quotient U D p) by ring]
    norm_num [add_re, mul_re]
  simp only [quadratic, quadraticFirst, he, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem quadraticFirst_eq_bilinear {n : ℕ} (hn : 0 < n) (C U : Points n) :
    quadraticFirst (root n) C U = -2 * bilinear hn C U := by
  have h := quadratic_add (root n) C U
  rw [ActualObjectiveLoss.quadratic_eq_pairPotential hn,
    ActualObjectiveLoss.quadratic_eq_pairPotential hn,
    ActualObjectiveLoss.quadratic_eq_pairPotential hn, potential_add] at h
  linarith only [h]

theorem physical_schur_identity {m : ℕ} (hm : 2 ≤ m) (c U : Points (2 * m))
    (hc : HalfPeriodic (by omega) c) (hU : HalfPeriodic (by omega) U) :
    quadraticFirst (root (2 * m)) c U =
      finitePairing (operator (2 * m) (constraint (by omega) c)) (constraint (by omega) U) / (2 * m : ℝ) -
      2 * bilinear (by omega) (c - canonicalLift (constraint (by omega) c)) U := by
  let q := constraint (show 0 < 2 * m by omega) c
  have hq : FiniteBox.Antiperiodic (by omega) q := StrongObjectiveEstimate.actual_constraint_antiperiodic (by omega) c hc
  have he : c = canonicalLift q + (c - canonicalLift q) := by abel
  rw [quadraticFirst_eq_bilinear (by omega)]
  conv_lhs => rw [he, bilinear_add_left]
  have hb := canonical_remainder_bilinear hm q hq U hU
  change _ = finitePairing (operator (2 * m) q) (constraint (by omega) U) / (2 * m : ℝ) - _
  linarith only [hb]

theorem physical_schur_error {m : ℕ} (hm : 2 ≤ m) (c U : Points (2 * m))
    (hc : HalfPeriodic (by omega) c) (hU : HalfPeriodic (by omega) U) :
    |quadraticFirst (root (2 * m)) c U -
      finitePairing (operator (2 * m) (constraint (by omega) c)) (constraint (by omega) U) / (2 * m : ℝ)| ≤
      2 * Real.sqrt (StrongObjectiveEstimate.residualEnergy (by omega) c) * Real.sqrt (pairEnergy (by omega) U) := by
  rw [physical_schur_identity hm c U hc hU, sub_sub_cancel_left, abs_neg, abs_mul]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hb := bilinear_abs_le (show 0 < 2 * m by omega) (c - canonicalLift (constraint (by omega) c)) U
  change |bilinear (by omega) (c - canonicalLift (constraint (by omega) c)) U| ≤
    Real.sqrt (StrongObjectiveEstimate.residualEnergy (by omega) c) * Real.sqrt (pairEnergy (by omega) U) at hb
  nlinarith only [hb]

theorem first_argument_error {n : ℕ} (hn : 0 < n) (C c U : Points n) :
    |quadraticFirst (root n) C U - quadraticFirst (root n) c U| ≤
      2 * Real.sqrt (pairEnergy hn (C - c)) * Real.sqrt (pairEnergy hn U) := by
  rw [quadraticFirst_eq_bilinear hn, quadraticFirst_eq_bilinear hn]
  have he : C = c + (C - c) := by abel
  have hh : bilinear hn C U = bilinear hn c U + bilinear hn (C - c) U := by
    conv_lhs => rw [he, bilinear_add_left]
  rw [hh, show -2 * (bilinear hn c U + bilinear hn (C - c) U) - -2 * bilinear hn c U =
    -2 * bilinear hn (C - c) U by ring, abs_mul]
  norm_num only [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hb := bilinear_abs_le hn (C - c) U
  nlinarith only [hb]

end
end StructuralNote.MatchingActivityRadialSchurFirst
