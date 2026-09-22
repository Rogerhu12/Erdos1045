import StructuralNote.FixedDualClassificationStepEnergy
import StructuralNote.FixedDualClassificationMultiplierLimit

/-! Uniform convergence of the actual finite quadratic energy to the
positive odd Fourier energy of its normalized step profile. -/

namespace StructuralNote.FixedDualClassificationUniformEnergy

open Real Complex Filter Erdos1045.EventualExact FourierMultiplier SchurLiftBounds
open FixedDualClassificationStep FixedDualClassificationStepEnergy
open FixedDualClassificationOddSpectrum FixedDualClassificationFiniteTail
open FixedDualClassificationMidpointSynthesis FixedDualClassificationSignedCutoff
open FixedDualClassificationMultiplierLimit
open scoped Topology BigOperators
noncomputable section

def energyMultiplierError (n : ℕ) (scale : ℝ) (k : ℕ) : ℝ :=
  |SchurWeights.weight n (2 * k + 1) -
    positiveWeight k * (scale * sinc ((2 * k + 1 : ℕ) * Real.pi / n)) ^ 2|

theorem energyMultiplierError_tendsto {scale : ℕ → ℝ}
    (hscale : Tendsto scale atTop (𝓝 1)) (k : ℕ) :
    Tendsto (fun n : ℕ => energyMultiplierError n (scale n) k) atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ => sinc ((2 * k + 1 : ℕ) * Real.pi / n)) atTop (𝓝 1) := by
    simpa only [sinc_zero, Function.comp_def] using continuous_sinc.continuousAt.tendsto.comp
      (tendsto_const_div_atTop_nhds_zero_nat ((2 * k + 1 : ℕ) * Real.pi))
  have h := ((positive_multiplier_tendsto k).sub
    (((hscale.mul hs).pow 2).const_mul (positiveWeight k))).abs
  simpa only [energyMultiplierError, positiveWeight, mul_one, one_pow, sub_self, abs_zero] using h

theorem low_energy_difference_le {n P : ℕ} (hn : 4 * P < n) (heven : Even n)
    (q : Fin n → ℝ) {A : ℝ} (hA : 0 ≤ A) (hq : ∀ j, |q j| ≤ A) (scale : ℝ) :
    |partialEnergy q (lowFrequencies n (2 * P)) -
      ∑ k ∈ Finset.range P, energyTerm q scale k| ≤
      A ^ 2 * ∑ k ∈ Finset.range P, energyMultiplierError n scale k := by
  let : NeZero n := ⟨by omega⟩
  rw [finite_positive_energy hn heven, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  rw [energyTerm_eq (by omega), ← sub_mul, abs_mul, abs_sq]
  have hnorm := midpointCoefficient_norm_le (by omega) q hA hq
    ⟨2 * k + 1, by have hk' := Finset.mem_range.mp hk; omega⟩
  have hs : ‖signedMidpointCoefficient q (2 * k + 1)‖ ^ 2 ≤ A ^ 2 := by
    convert (sq_le_sq₀ (norm_nonneg _) hA).mpr hnorm using 1 <;> push_cast <;> rfl
  exact (mul_le_mul_of_nonneg_left hs (abs_nonneg _)).trans_eq (mul_comm _ _)

theorem low_energy_error_tendsto {scale : ℕ → ℝ} (hscale : Tendsto scale atTop (𝓝 1))
    (A : ℝ) (P : ℕ) :
    Tendsto (fun n : ℕ => A ^ 2 * ∑ k ∈ Finset.range P, energyMultiplierError n (scale n) k)
      atTop (𝓝 0) := by
  have h := (tendsto_finsetSum (Finset.range P)
    (fun k _ => energyMultiplierError_tendsto hscale k)).const_mul (A ^ 2)
  simpa only [Finset.sum_const_zero, mul_zero] using h

theorem uniform_energy_comparison {scale : ℕ → ℝ}
    (hscale : Tendsto scale atTop (𝓝 1)) {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ∀ q : Fin n → ℝ,
      (∀ j, |q j| ≤ A) →
        |normalizedBoxEnergy (operator n) q - continuousEnergy q (scale n)| < ε := by
  have ht : Tendsto (fun P : ℕ => 5 * A ^ 2 / ((P : ℝ) + 1)) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (5 * A ^ 2)
    simpa only [mul_zero, mul_one_div] using h
  obtain ⟨P, hP⟩ := (ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 2))).exists
  have hlow := (low_energy_error_tendsto hscale A P).eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 2))
  have hs : ∀ᶠ n : ℕ in atTop, |scale n| < 2 :=
    hscale.abs.eventually (gt_mem_nhds (by norm_num : |(1 : ℝ)| < 2))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlow.and (hs.and (eventually_gt_atTop (4 * P))))
  refine ⟨N, fun n hn heven q hq => ?_⟩
  obtain ⟨hlo, hsc, hnP⟩ := hN n hn
  have hn0 : 0 < n := by omega
  have hmass := meanSquare_le_of_bound hn0 q hA hq
  have hf := energy_lowFrequency_error (P := 2 * P) hn0 heven q
  have hc := continuousEnergy_tail (P := P) hn0 q (scale n)
  have hfl : normalizedBoxEnergy (operator n) q - partialEnergy q (lowFrequencies n (2 * P)) ≤
      A ^ 2 / ((P : ℝ) + 1) := by
    apply hf.2.trans
    apply (div_le_div_of_nonneg_right hmass (by positivity)).trans
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    push_cast
    linarith
  have hcl : continuousEnergy q (scale n) - ∑ k ∈ Finset.range P, energyTerm q (scale n) k ≤
      4 * A ^ 2 / ((P : ℝ) + 1) := by
    apply hc.2.trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hss : scale n ^ 2 ≤ 4 := by
      simpa only [sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] using
        (sq_le_sq₀ (abs_nonneg (scale n)) (by norm_num : (0 : ℝ) ≤ 2)).mpr hsc.le
    exact (mul_le_mul_of_nonneg_left hmass (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hss (sq_nonneg _))
  have hl := (low_energy_difference_le hnP heven q hA hq (scale n)).trans_lt hlo
  have hd := abs_lt.mp hl
  have hp' : 5 * (A ^ 2 / ((P : ℝ) + 1)) < ε / 2 := by
    calc
      _ = 5 * A ^ 2 / ((P : ℝ) + 1) := by ring
      _ < ε / 2 := hP
  have hc' : continuousEnergy q (scale n) - ∑ k ∈ Finset.range P, energyTerm q (scale n) k ≤
      4 * (A ^ 2 / ((P : ℝ) + 1)) := by
    calc
      _ ≤ 4 * A ^ 2 / ((P : ℝ) + 1) := hcl
      _ = _ := by ring
  have hnonneg : 0 ≤ A ^ 2 / ((P : ℝ) + 1) := by positivity
  apply abs_lt.mpr
  constructor <;> linarith [hf.1, hc.1]

theorem normalized_energy_comparison {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ∀ q : Fin n → ℝ,
      (∀ j, |q j| ≤ A) →
        |normalizedBoxEnergy (operator n) q - continuousEnergy q (profileScale n)| < ε :=
  uniform_energy_comparison profileScale_tendsto hA hε

end
end StructuralNote.FixedDualClassificationUniformEnergy
