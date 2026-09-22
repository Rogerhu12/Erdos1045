import StructuralNote.FixedDualClassificationKernelL2
import StructuralNote.FixedDualClassificationPairing

/-! The odd-frequency spectrum is realized on the half-circle by modulation.
It is a complete Fourier basis for the actual kernel integral. -/

namespace StructuralNote.FixedDualClassificationOddSpectrum

open Real MeasureTheory Set AddCircle
open FixedDualPrimitive FixedDualClassificationFunctional
open FixedDualClassificationKernelFourier FixedDualClassificationKernelL2
open FixedDualClassificationStep FixedDualClassificationPairing
open scoped BigOperators ComplexConjugate
noncomputable section

def modulated (f : ℝ → ℝ) (u : ℝ) : ℂ := (f u : ℂ) * oscillation (-1) u

def oddCoefficient (f : ℝ → ℝ) (k : ℤ) : ℂ :=
  fourierCoeffOn pi_pos (modulated f) k

theorem modulated_norm (f : ℝ → ℝ) (u : ℝ) : ‖modulated f u‖ = |f u| := by
  simp only [modulated, oscillation, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_exp_ofReal_mul_I, mul_one]

theorem modulated_memLp {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc 0 Real.pi))) :
    MemLp (modulated f) 2 (volume.restrict (Ioc 0 Real.pi)) := by
  apply (memLp_two_iff_integrable_sq_norm ?_).mpr
  · simp_rw [modulated_norm, sq_abs]
    exact hf.integrable_sq
  · exact hf.ofReal.aestronglyMeasurable.mul
      ((oscillation_continuous (-1)).aestronglyMeasurable)

theorem oddCoefficient_integral (f : ℝ → ℝ) (k : ℤ) :
    oddCoefficient f k =
      (∫ u in 0..Real.pi, (f u : ℂ) * oscillation (-(2 * k + 1)) u) / Real.pi := by
  rw [oddCoefficient, fourierCoeffOn_eq_integral]
  simp only [sub_zero, smul_eq_mul, Complex.real_smul, Complex.ofReal_div,
    Complex.ofReal_one]
  simp only [div_eq_inv_mul, mul_one]
  congr 1
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [fourier_coe_apply]
  unfold modulated oscillation
  rw [mul_comm _ ((f u : ℂ) * _), mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  field_simp
  ring

theorem kernel_reflection (u : ℝ) : kernel (Real.pi - u) = -kernel u := by
  unfold kernel
  rw [cos_pi_sub, sin_pi_sub]
  ring

theorem odd_sine_reflection (k : ℕ) (u : ℝ) :
    sin ((2 * k + 1 : ℕ) * (Real.pi - u)) = sin ((2 * k + 1 : ℕ) * u) := by
  rw [mul_sub, sin_sub, sin_nat_mul_pi, cos_nat_mul_pi]
  simp [pow_add, pow_mul]

theorem kernel_odd_sine_integral (k : ℕ) :
    (∫ u in 0..Real.pi, kernel u * sin ((2 * k + 1 : ℕ) * u)) = 0 := by
  have h := intervalIntegral.integral_comp_sub_left
    (fun u => kernel u * sin ((2 * k + 1 : ℕ) * u)) Real.pi (a := 0) (b := Real.pi)
  simp only [kernel_reflection, odd_sine_reflection, neg_mul,
    intervalIntegral.integral_neg, sub_self, sub_zero] at h
  linarith

theorem kernel_oscillation_integrable (p : ℝ) :
    IntervalIntegrable (fun u => (kernel u : ℂ) * oscillation p u) volume 0 Real.pi := by
  exact (show IntervalIntegrable (fun u => (kernel u : ℂ)) volume 0 Real.pi from
    ⟨kernel_intervalIntegrable.1.ofReal, kernel_intervalIntegrable.2.ofReal⟩).mul_continuousOn
    (oscillation_continuous p).continuousOn

theorem kernel_oscillation_re (p : ℝ) :
    (∫ u in 0..Real.pi, (kernel u : ℂ) * oscillation p u).re =
      ∫ u in 0..Real.pi, kernel u * cos (p * u) := by
  have h := intervalIntegral.intervalIntegral_re (kernel_oscillation_integrable p)
  change (∫ u in 0..Real.pi, ((kernel u : ℂ) * oscillation p u).re) =
    (∫ u in 0..Real.pi, (kernel u : ℂ) * oscillation p u).re at h
  rw [← h]
  simp only [oscillation, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re]

theorem kernel_oscillation_im (p : ℝ) :
    (∫ u in 0..Real.pi, (kernel u : ℂ) * oscillation p u).im =
      ∫ u in 0..Real.pi, kernel u * sin (p * u) := by
  have h := intervalIntegral.intervalIntegral_im (kernel_oscillation_integrable p)
  change (∫ u in 0..Real.pi, ((kernel u : ℂ) * oscillation p u).im) =
    (∫ u in 0..Real.pi, (kernel u : ℂ) * oscillation p u).im at h
  rw [← h]
  simp only [oscillation, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, Complex.exp_ofReal_mul_I_im]

def naturalKernelCoefficient (k : ℕ) : ℝ := if k = 0 then 0 else 1 / (4 * (k + 1))

def kernelCoefficient : ℤ → ℝ
  | Int.ofNat k => naturalKernelCoefficient k
  | Int.negSucc k => naturalKernelCoefficient k

theorem kernel_odd_cos_normalized (k : ℕ) :
    (∫ u in 0..Real.pi, kernel u * cos ((2 * k + 1 : ℕ) * u)) / Real.pi =
      naturalKernelCoefficient k := by
  by_cases hk : k = 0
  · subst k
    simpa [naturalKernelCoefficient] using kernel_first_cos_integral
  · rw [kernel_odd_cos_integral (Nat.pos_of_ne_zero hk), naturalKernelCoefficient, if_neg hk]
    field_simp

theorem oddCoefficient_kernel_nat (k : ℕ) :
    oddCoefficient kernel (k : ℤ) = (naturalKernelCoefficient k : ℂ) := by
  rw [oddCoefficient_integral]
  apply Complex.ext
  · rw [Complex.div_ofReal_re, kernel_oscillation_re]
    simp only [neg_mul, cos_neg]
    convert kernel_odd_cos_normalized k using 1 <;> push_cast <;> rfl
  · rw [Complex.div_ofReal_im, kernel_oscillation_im]
    simp only [neg_mul, sin_neg, mul_neg, intervalIntegral.integral_neg, Complex.ofReal_im]
    have h := kernel_odd_sine_integral k
    push_cast at h
    push_cast
    rw [h]
    simp

theorem oddCoefficient_kernel_negSucc (k : ℕ) :
    oddCoefficient kernel (Int.negSucc k) = (naturalKernelCoefficient k : ℂ) := by
  rw [oddCoefficient_integral]
  have he : -(2 * (Int.negSucc k : ℝ) + 1) = ((2 * k + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [he]
  apply Complex.ext
  · rw [Complex.div_ofReal_re, kernel_oscillation_re]
    exact kernel_odd_cos_normalized k
  · rw [Complex.div_ofReal_im, kernel_oscillation_im, kernel_odd_sine_integral]
    simp

theorem oddCoefficient_kernel (k : ℤ) :
    oddCoefficient kernel k = (kernelCoefficient k : ℂ) := by
  cases k with
  | ofNat k => exact oddCoefficient_kernel_nat k
  | negSucc k => exact oddCoefficient_kernel_negSucc k

theorem modulated_pairing (f g : ℝ → ℝ) (u : ℝ) :
    conj (modulated f u) * modulated g u = ((f u * g u : ℝ) : ℂ) := by
  unfold modulated oscillation
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I]
  rw [show (f u : ℂ) * Complex.exp (((-1 * u : ℝ) : ℂ) * -Complex.I) *
      ((g u : ℂ) * Complex.exp (((-1 * u : ℝ) : ℂ) * Complex.I)) =
      ((f u * g u : ℝ) : ℂ) * (Complex.exp (((-1 * u : ℝ) : ℂ) * -Complex.I) *
        Complex.exp (((-1 * u : ℝ) : ℂ) * Complex.I)) by push_cast; ring,
    ← Complex.exp_add]
  simp

theorem kernel_potential_hasSum {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc 0 Real.pi))) :
    HasSum (fun k : ℤ => (2 * kernelCoefficient k : ℂ) * oddCoefficient f k)
      (kernelPotential f : ℂ) := by
  have h := hasSum_prod_fourierCoeffOn pi_pos
    (modulated_memLp kernel_memLp) (modulated_memLp hf)
  change HasSum (fun k => conj (oddCoefficient kernel k) * oddCoefficient f k) _ at h
  simp_rw [oddCoefficient_kernel, Complex.conj_ofReal, modulated_pairing,
    intervalIntegral.integral_ofReal] at h
  have h2 : HasSum (fun k : ℤ => (2 * kernelCoefficient k : ℂ) * oddCoefficient f k)
      ((2 : ℂ) * ((Real.pi - 0)⁻¹ • ((∫ u in 0..Real.pi, kernel u * f u : ℝ) : ℂ))) := by
    simpa only [mul_assoc] using h.mul_left (2 : ℂ)
  have he : (kernelPotential f : ℂ) =
      (2 : ℂ) * ((Real.pi - 0)⁻¹ • ((∫ u in 0..Real.pi, kernel u * f u : ℝ) : ℂ)) := by
    unfold kernelPotential
    simp only [sub_zero, Complex.real_smul]
    push_cast
    rw [show (∫ u in 0..Real.pi, f u * kernel u) =
      ∫ u in 0..Real.pi, kernel u * f u by
        apply intervalIntegral.integral_congr; intro u _; ring]
    ring
  exact he ▸ h2

end
end StructuralNote.FixedDualClassificationOddSpectrum
