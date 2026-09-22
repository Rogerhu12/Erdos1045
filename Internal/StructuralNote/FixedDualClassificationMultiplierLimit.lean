import StructuralNote.FixedDualClassificationMidpointSynthesis
import EventualExact.SchurWeightLimit

/-! The actual normalization and fixed-frequency Schur multipliers converge. -/

namespace StructuralNote.FixedDualClassificationMultiplierLimit

open Real Complex Filter Erdos1045.EventualExact
open FixedDualClassificationOddSpectrum FixedDualClassificationStep
open FixedDualClassificationStepPotential FixedDualClassificationMidpointSynthesis
open scoped Topology BigOperators ComplexConjugate
noncomputable section

def profileScale (n : ℕ) : ℝ := (Real.pi / 2) / FiniteBox.amplitude n

theorem amplitude_eq_sinc {n : ℕ} (hn : 0 < n) :
    FiniteBox.amplitude n = (Real.pi / 2) *
      sinc (Real.pi / (2 * n)) / Real.cos (Real.pi / (2 * n)) := by
  have hx : Real.pi / (2 * n) ≠ 0 := by positivity
  rw [FiniteBox.amplitude, sinc_of_ne_zero hx, Real.tan_eq_sin_div_cos]
  have hn' : (n : ℝ) ≠ 0 := by positivity
  field_simp

theorem amplitude_tendsto : Tendsto FiniteBox.amplitude atTop (𝓝 (Real.pi / 2)) := by
  have hx : Tendsto (fun n : ℕ => Real.pi / (2 * n)) atTop (𝓝 0) := by
    convert tendsto_const_div_atTop_nhds_zero_nat (Real.pi / 2) using 1
    ext n
    ring
  have hs := continuous_sinc.continuousAt.tendsto.comp hx
  have hc := continuous_cos.continuousAt.tendsto.comp hx
  have h := (hs.const_mul (Real.pi / 2)).div hc (by simp : Real.cos (0 : ℝ) ≠ 0)
  simp only [sinc_zero, Real.cos_zero, mul_one, div_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (amplitude_eq_sinc hn).symm

theorem profileScale_tendsto : Tendsto profileScale atTop (𝓝 1) := by
  change Tendsto (fun n : ℕ => (Real.pi / 2) / FiniteBox.amplitude n) atTop (𝓝 1)
  have h := (tendsto_const_nhds (x := Real.pi / 2)).div amplitude_tendsto (by positivity)
  convert h using 1 <;> norm_num [Real.pi_ne_zero]
  ext n
  rfl

theorem positive_multiplier_tendsto (k : ℕ) :
    Tendsto (fun n : ℕ => SchurWeights.weight n (2 * k + 1)) atTop
      (𝓝 (2 * kernelCoefficient (k : ℤ))) := by
  by_cases hk : k = 0
  · subst k
    have hw (n : ℕ) : SchurWeights.weight n 1 = 0 :=
      SchurWeights.weight_eq_zero (by simp [SchurWeights.Active])
    simp [kernelCoefficient, naturalKernelCoefficient, hw]
  · have h := SchurWeights.weight_tendsto_fixed (show Odd (2 * k + 1) from ⟨k, by omega⟩)
      (by omega : 3 ≤ 2 * k + 1)
    convert h using 1
    simp only [kernelCoefficient, naturalKernelCoefficient, if_neg hk,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    congr 1
    field_simp
    ring

def multiplierError (n : ℕ) (scale : ℝ) (k : ℕ) : ℝ :=
  |SchurWeights.weight n (2 * k + 1) -
    2 * kernelCoefficient (k : ℤ) * (scale * sinc ((2 * k + 1 : ℕ) * Real.pi / n))|

theorem multiplierError_tendsto {scale : ℕ → ℝ} (hscale : Tendsto scale atTop (𝓝 1)) (k : ℕ) :
    Tendsto (fun n : ℕ => multiplierError n (scale n) k) atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ => sinc ((2 * k + 1 : ℕ) * Real.pi / n)) atTop (𝓝 1) := by
    simpa only [sinc_zero, Function.comp_def] using
      continuous_sinc.continuousAt.tendsto.comp
        (tendsto_const_div_atTop_nhds_zero_nat ((2 * k + 1 : ℕ) * Real.pi))
  have h := ((positive_multiplier_tendsto k).sub
    ((hscale.mul hs).const_mul (2 * kernelCoefficient (k : ℤ)))).abs
  simpa only [multiplierError, mul_one, sub_self, abs_zero] using h

theorem term_difference_norm_le {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    {A : ℝ} (hA : 0 ≤ A) (hq : ∀ j, |q j| ≤ A)
    (scale : ℝ) (j : Fin n) (k : ℕ) (hk : 2 * k + 1 < n) :
    ‖finiteTerm q j (2 * k + 1) - stepTerm q scale (cellMidpoint n j) k‖ ≤
      multiplierError n scale k * A := by
  have he : finiteTerm q j (2 * k + 1) - stepTerm q scale (cellMidpoint n j) k =
      ((SchurWeights.weight n (2 * k + 1) -
        2 * kernelCoefficient (k : ℤ) * (scale * sinc ((2 * k + 1 : ℕ) * Real.pi / n))) : ℝ) *
        oscillation (-((2 * k + 1 : ℕ) : ℝ)) (cellMidpoint n j) *
        conj (signedMidpointCoefficient q (2 * k + 1)) := by
    unfold finiteTerm stepTerm
    push_cast
    ring
  have ho : ‖oscillation (-((2 * k + 1 : ℕ) : ℝ)) (cellMidpoint n j)‖ = 1 := by
    simp only [oscillation, Complex.norm_exp_ofReal_mul_I]
  rw [he, norm_mul, norm_mul, norm_conj, ho, mul_one,
    Complex.norm_real, Real.norm_eq_abs]
  simpa only [multiplierError, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
    mul_le_mul_of_nonneg_left (midpointCoefficient_norm_le hn q hA hq ⟨2 * k + 1, hk⟩)
      (abs_nonneg (SchurWeights.weight n (2 * k + 1) -
        2 * kernelCoefficient (k : ℤ) * (scale * sinc ((2 * k + 1 : ℕ) * Real.pi / n))))

end
end StructuralNote.FixedDualClassificationMultiplierLimit
