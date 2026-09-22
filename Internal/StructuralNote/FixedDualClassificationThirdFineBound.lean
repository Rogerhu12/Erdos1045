import StructuralNote.FixedDualClassificationThirdDefect
import StructuralNote.FixedDualClassificationThirdArithmetic

/-! The fine energy bound uses the actual first, third, fifth and seventh coefficients. -/

namespace StructuralNote.FixedDualClassificationThirdFineBound

open Real MeasureTheory Set
open FixedDualClassificationStep FixedDualClassificationCoefficientBound
open FixedDualClassificationThirdDefect FixedDualClassificationThirdArithmetic
open FixedDualClassificationStepEnergy FixedDualClassificationThirdCoarse
open FixedDualClassificationOddSpectrum FixedDualClassificationMultiplierLimit
open Erdos1045.EventualExact Erdos1045.EventualExact.FourierMultiplier
open Erdos1045.EventualExact.SchurLiftBounds Erdos1045.EventualExact.FiniteBox
open scoped BigOperators
noncomputable section

theorem positiveWeight_fine (k : ℕ) : positiveWeight k ≤ (1 / 10 : ℝ) +
    (if k = 0 then -(1 / 10) else 0) + (if k = 1 then 3 / 20 else 0) +
    (if k = 2 then 1 / 15 else 0) + (if k = 3 then 1 / 40 else 0) := by
  by_cases hk0 : k = 0
  · subst k; norm_num [positiveWeight, kernelCoefficient, naturalKernelCoefficient]
  by_cases hk1 : k = 1
  · subst k; norm_num [positiveWeight, kernelCoefficient, naturalKernelCoefficient]
  by_cases hk2 : k = 2
  · subst k; norm_num [positiveWeight, kernelCoefficient, naturalKernelCoefficient]
  by_cases hk3 : k = 3
  · subst k; norm_num [positiveWeight, kernelCoefficient, naturalKernelCoefficient]
  simp only [positiveWeight, kernelCoefficient, naturalKernelCoefficient, if_neg hk0,
    if_neg hk1, if_neg hk2, if_neg hk3, add_zero]
  have hk : (4 : ℝ) ≤ k := by exact_mod_cast (show 4 ≤ k by omega)
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 10)).mpr
  have hden : 0 < 4 * ((k : ℝ) + 1) := by positivity
  field_simp
  linarith

theorem continuousEnergy_four_coefficients {n : ℕ} (hn : 0 < n)
    (q : Fin n → ℝ) (scale : ℝ) :
    let c := profileCoefficient (stepProfile q scale)
    continuousEnergy q scale ≤ scale ^ 2 * meanSquare q / 20 - ‖c 1‖ ^ 2 / 10 +
      3 * ‖c 3‖ ^ 2 / 20 + ‖c 5‖ ^ 2 / 15 + ‖c 7‖ ^ 2 / 40 := by
  dsimp only
  apply (energy_summable hn q scale).tsum_le_of_sum_range_le
  intro P
  let c := profileCoefficient (stepProfile q scale)
  have hsum : (∑ k ∈ Finset.range (P + 4), energyTerm q scale k) ≤
      (1 / 10 : ℝ) * (∑ k ∈ Finset.range (P + 4), ‖c (2 * k + 1)‖ ^ 2) -
        ‖c 1‖ ^ 2 / 10 + 3 * ‖c 3‖ ^ 2 / 20 + ‖c 5‖ ^ 2 / 15 + ‖c 7‖ ^ 2 / 40 := by
    have h := Finset.sum_le_sum (s := Finset.range (P + 4)) (fun k _ =>
      mul_le_mul_of_nonneg_right (positiveWeight_fine k) (sq_nonneg ‖c (2 * k + 1)‖))
    simp only [add_mul, ite_mul, zero_mul, Finset.sum_add_distrib, ← Finset.mul_sum] at h
    simp only [Finset.sum_ite_eq', Finset.mem_range, show 0 < P + 4 by omega,
      show 1 < P + 4 by omega, show 2 < P + 4 by omega, show 3 < P + 4 by omega,
      ite_true] at h
    norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, mul_zero, zero_add,
      mul_one, show (2 : ℤ) + 1 = 3 by norm_num, show (2 : ℤ) * 2 + 1 = 5 by norm_num,
      show (2 : ℤ) * 3 + 1 = 7 by norm_num] at h
    change (∑ k ∈ Finset.range (P + 4), energyTerm q scale k) ≤ _ at h
    linarith
  have hm : (∑ k ∈ Finset.range P, energyTerm q scale k) ≤
      ∑ k ∈ Finset.range (P + 4), energyTerm q scale k :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun k _ _ => mul_nonneg (positiveWeight_nonneg k) (sq_nonneg _))
  have hb := positive_bessel_half hn q scale (P + 4)
  change (∑ k ∈ Finset.range (P + 4), ‖c (2 * k + 1)‖ ^ 2) ≤ _ at hb
  dsimp only [c] at hsum
  linarith

theorem normalized_fine_bound {m : ℕ} (hm : 0 < m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ Q hm) :
    let c := profileCoefficient (stepProfile q (profileScale (2 * m)))
    continuousEnergy q (profileScale (2 * m)) ≤
      upperEnergy (Real.pi ^ 2 / 8) (1 - ‖c 3‖) ‖c 1‖ := by
  let c := profileCoefficient (stepProfile q (profileScale (2 * m)))
  have h := continuousEnergy_four_coefficients (by omega) q (profileScale (2 * m))
  have hmss := normalized_square_mass_le hm q hq
  have hr : ‖c 3‖ ≤ 1 := normalized_coefficient_le_one hm q hq (by norm_num : 0 < (3 : ℕ))
  have hnonneg : 0 ≤ ‖c 1‖ + 2 * (1 - ‖c 3‖) := by positivity
  have h57 := normalized_five_seven hm q hq
  change ‖c 5‖ ≤ _ ∧ ‖c 7‖ ≤ _ at h57
  have h5 := (sq_le_sq₀ (norm_nonneg (c 5)) hnonneg).mpr h57.1
  have h7 := (sq_le_sq₀ (norm_nonneg (c 7)) hnonneg).mpr h57.2
  change continuousEnergy q (profileScale (2 * m)) ≤
    upperEnergy (Real.pi ^ 2 / 8) (1 - ‖c 3‖) ‖c 1‖
  dsimp only at h
  change continuousEnergy q (profileScale (2 * m)) ≤ _ at h
  unfold upperEnergy
  dsimp only [c] at h5 h7 ⊢
  nlinarith

end
end StructuralNote.FixedDualClassificationThirdFineBound
