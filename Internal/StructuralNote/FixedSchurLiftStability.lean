import StructuralNote.FixedSchurChart
import StructuralNote.CommonFiberSchurExpansion
import EventualExact.SchurLiftBounds

/-! Energy control of the change in the actual Schur center at fixed free parameters. -/

namespace StructuralNote.FixedSchurLiftStability

open Complex Erdos1045.EventualExact
open FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum SchurLiftBounds
open FixedSchurLinear
open scoped BigOperators

noncomputable section

theorem canonicalLift_sub {n : ℕ} (q r : Fin n → ℝ) :
    canonicalLift (q - r) = canonicalLift q - canonicalLift r := by
  have h := CommonFiberSchurExpansion.canonicalLift_add (q - r) r
  rw [sub_add_cancel] at h
  exact eq_sub_iff_add_eq.mpr h.symm

theorem center_sub_same_parameter {m : ℕ} (q r : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) : center q v - center r v = canonicalLift (q - r) := by
  rw [canonicalLift_sub]
  unfold center
  abel

theorem meanSquare_sub_le_l1 {n : ℕ} (q r : Fin n → ℝ)
    (hq : ‖q‖ ≤ 5) (hr : ‖r‖ ≤ 5) :
    meanSquare (q - r) ≤ 10 * (∑ j, |q j - r j|) / (n : ℝ) := by
  have hp (j : Fin n) : |q j - r j| ≤ 10 := by
    have hqj : |q j| ≤ 5 := by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm q j).trans hq
    have hrj : |r j| ≤ 5 := by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm r j).trans hr
    have ht : |q j - r j| ≤ |q j| + |r j| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le (q j) (r j)
    linarith
  have hs : (∑ j, (q j - r j) ^ 2) ≤ 10 * ∑ j, |q j - r j| := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have h := mul_le_mul_of_nonneg_right (hp j) (abs_nonneg (q j - r j))
    nlinarith only [h, sq_abs (q j - r j)]
  unfold meanSquare
  simp only [Pi.sub_apply]
  exact div_le_div_of_nonneg_right hs (by positivity)

theorem center_difference_energy_le {m : ℕ} (hm : 2 ≤ m)
    (q r : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (hqa : FiniteBox.Antiperiodic (by omega) q)
    (hra : FiniteBox.Antiperiodic (by omega) r)
    (hq : ‖q‖ ≤ 5) (hr : ‖r‖ ≤ 5) :
    pairEnergy (by omega) (center q v - center r v) ≤
      320 * (∑ j, |q j - r j|) / (2 * m : ℝ) := by
  have ha : FiniteBox.Antiperiodic (by omega) (q - r) := by
    intro j
    simp only [Pi.sub_apply, hqa j, hra j]
    ring
  rw [center_sub_same_parameter]
  have hA := canonicalLift_pairEnergy_le hm (q - r) ha
  have hl := meanSquare_sub_le_l1 q r hq hr
  calc
    _ ≤ 32 * meanSquare (q - r) := hA
    _ ≤ 32 * (10 * (∑ j, |q j - r j|) / ((2 * m : ℕ) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hl (by norm_num)
    _ = _ := by simp only [Nat.cast_mul, Nat.cast_ofNat]; ring

end
end StructuralNote.FixedSchurLiftStability
