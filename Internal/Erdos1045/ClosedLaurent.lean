import Erdos1045.ClosedSeries
import Erdos1045.LaurentBase
import Mathlib.Analysis.PSeries

namespace Erdos1045.ClosedSeries

open scoped BigOperators
open ExteriorClassical
noncomputable section

def weightedTail (a : ℕ → ℂ) (m : ℕ) : ℂ := ((m + 1 : ℕ) : ℂ) * a (m + 1)

theorem weightedTail_sq (a : ℕ → ℂ) (m : ℕ) :
    ‖weightedTail a m‖ ^ 2 = ((m + 1 : ℕ) : ℝ) ^ 2 * ‖a (m + 1)‖ ^ 2 := by
  simp only [weightedTail, norm_mul, Complex.norm_natCast, mul_pow]

theorem weightedTail_summable {a : ℕ → ℂ} (ha : SobolevCoefficients a) :
    Summable (fun m => ‖weightedTail a m‖ ^ 2) := by
  simp_rw [weightedTail_sq]
  exact (FaberFourier.coefficient_energies_summable ha.2).2.comp_injective
    (fun _ _ h => Nat.add_right_cancel h)

theorem weightedTail_energy {a : ℕ → ℂ} (ha : SobolevCoefficients a) :
    (∑' m, ‖weightedTail a m‖ ^ 2) = ∑' m : ℕ, (m : ℝ) ^ 2 * ‖a m‖ ^ 2 := by
  simp_rw [weightedTail_sq]
  have h := (FaberFourier.coefficient_energies_summable ha.2).2.tsum_eq_zero_add
  simpa using h.symm

theorem laurent_absolute (a : ℕ → ℂ) (ha : SobolevCoefficients a) :
    Summable (fun m => ‖a m‖) := by
  let y : ℕ → ℂ := fun m => (((m + 1 : ℕ) : ℂ))⁻¹
  have hy : Summable (fun m => ‖y m‖ ^ 2) := by
    have hs : Summable (fun m : ℕ => ((m : ℝ) ^ 2)⁻¹) :=
      Real.summable_nat_pow_inv.mpr (by norm_num)
    have ht : Summable (fun m : ℕ => (((m + 1 : ℕ) : ℝ) ^ 2)⁻¹) :=
      hs.comp_injective (fun _ _ h => Nat.add_right_cancel h)
    simpa only [y, norm_inv, Complex.norm_natCast, inv_pow] using ht
  have hp := (complex_sequence_cauchy (weightedTail a) y (weightedTail_summable ha) hy).1
  have heq (m : ℕ) : weightedTail a m * y m = a (m + 1) := by
    have hm : (((m + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    dsimp only [weightedTail, y]
    field_simp
  simp_rw [heq] at hp
  exact (summable_nat_add_iff 1).mp hp

theorem hardy_kernel_hasSum {w : ℂ} (hw : 1 < ‖w‖) :
    HasSum (fun m : ℕ => ‖w⁻¹ ^ (m + 2)‖ ^ 2)
      (1 / (‖w‖ ^ 2 * (‖w‖ ^ 2 - 1))) := by
  have hr0 : 0 < ‖w‖ := lt_trans zero_lt_one hw
  have hi0 : 0 ≤ ‖w‖⁻¹ := inv_nonneg.mpr hr0.le
  have hi1 : ‖w‖⁻¹ < 1 := (inv_lt_one₀ hr0).2 hw
  have hq1 : (‖w‖⁻¹) ^ 2 < 1 := pow_lt_one₀ hi0 hi1 (by norm_num)
  have h := (hasSum_geometric_of_lt_one (sq_nonneg ‖w‖⁻¹) hq1).mul_left ((‖w‖⁻¹) ^ 4)
  convert h using 1 <;> try rfl
  · funext m
    rw [norm_pow, norm_inv, pow_add, mul_pow]
    simp only [← pow_mul]
    rw [Nat.mul_comm m 2]
    ring
  · have hr2 : ‖w‖ ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp [hr0.ne', hr2]

theorem laurent_hardy_evaluation (a : ℕ → ℂ) (ha : SobolevCoefficients a)
    (w : ℂ) (hw : 1 < ‖w‖) :
    ‖laurentDerivative a w‖ ^ 2 ≤ sobolevEnergySquared a /
      (2 * Real.pi * ‖w‖ ^ 2 * (‖w‖ ^ 2 - 1)) := by
  have hy := hardy_kernel_hasSum hw
  have hp := complex_sequence_cauchy (weightedTail a) (fun m => w⁻¹ ^ (m + 2))
    (weightedTail_summable ha) hy.summable
  have hfull : Summable (fun m : ℕ => (m : ℂ) * a m * w⁻¹ ^ (m + 1)) := by
    apply (summable_nat_add_iff 1).mp
    exact Summable.of_norm hp.1
  have heq : ‖laurentDerivative a w‖ =
      ‖∑' m, weightedTail a m * w⁻¹ ^ (m + 2)‖ := by
    rw [laurentDerivative, norm_neg, hfull.tsum_eq_zero_add]
    simp [weightedTail]
  have hb := hp.2
  rw [weightedTail_energy ha, hy.tsum_eq] at hb
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hr : 0 < ‖w‖ ^ 2 - 1 := by nlinarith
  have hden : 0 ≤ 1 / (‖w‖ ^ 2 * (‖w‖ ^ 2 - 1)) :=
    one_div_nonneg.mpr (mul_nonneg (sq_nonneg _) hr.le)
  rw [← heq, mul_pow, Real.sq_sqrt (tsum_nonneg (fun m => mul_nonneg (sq_nonneg _) (sq_nonneg _))),
    Real.sq_sqrt hden] at hsq
  convert hsq using 1 <;> first | rfl | (unfold sobolevEnergySquared; field_simp)

end
end Erdos1045.ClosedSeries
