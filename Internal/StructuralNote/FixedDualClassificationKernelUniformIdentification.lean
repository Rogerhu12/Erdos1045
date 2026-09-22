import StructuralNote.FixedDualClassificationKernelUniformConvergence
import StructuralNote.FixedDualClassificationSignedCutoff
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Identification of the conditional cosine-series limit with the actual logarithmic kernel. -/

namespace StructuralNote.FixedDualClassificationKernelUniformIdentification

open Real Finset Filter MeasureTheory Set AddCircle
open FixedDualPrimitive FixedDualClassificationStep FixedDualClassificationKernelL2
open FixedDualClassificationOddSpectrum FixedDualClassificationSignedCutoff
open FixedDualClassificationKernelUniformSeries FixedDualClassificationKernelUniformConvergence
open scoped Topology BigOperators ComplexConjugate
noncomputable section

local instance period_pos : Fact (0 < Real.pi) := ⟨pi_pos⟩

theorem liftedKernel_memLp :
    MemLp (AddCircle.liftIoc Real.pi 0 (modulated kernel)) 2 haarAddCircle := by
  have h : MemLp (modulated kernel) 2 (volume.restrict (Set.Ioc 0 (0 + Real.pi))) := by
    simpa only [zero_add] using modulated_memLp kernel_memLp
  exact h.memLp_liftIoc.haarAddCircle

def kernelLp : Lp ℂ 2 (@haarAddCircle Real.pi period_pos) := liftedKernel_memLp.toLp _

theorem kernelLp_coefficient (k : ℤ) : fourierCoeff kernelLp k = (kernelCoefficient k : ℂ) := by
  unfold kernelLp
  rw [fourierCoeff_congr_ae liftedKernel_memLp.coeFn_toLp, fourierCoeff_liftIoc_eq]
  simpa only [zero_add, oddCoefficient] using oddCoefficient_kernel k

def circlePartial (P : ℕ) : Lp ℂ 2 (@haarAddCircle Real.pi period_pos) :=
  ∑ k ∈ signedCutoff P, (kernelCoefficient k : ℂ) • fourierLp 2 k

theorem circlePartial_tendsto : Tendsto circlePartial atTop (𝓝 kernelLp) := by
  have h := hasSum_fourier_series_L2 kernelLp
  simp_rw [kernelLp_coefficient] at h
  exact h.comp signedCutoff_tendsto

theorem circlePartial_coe (P : ℕ) :
    circlePartial P =ᵐ[haarAddCircle] fun x : AddCircle Real.pi =>
      ∑ k ∈ signedCutoff P, (kernelCoefficient k : ℂ) * fourier k x := by
  have hs := Lp.coeFn_fun_finsetSum (signedCutoff P)
    (fun k => (kernelCoefficient k : ℂ) • (fourierLp 2 k : Lp ℂ 2 (@haarAddCircle Real.pi period_pos)))
  have ha : ∀ᵐ x : AddCircle Real.pi ∂haarAddCircle, ∀ k : ℤ,
      (((kernelCoefficient k : ℂ) • fourierLp 2 k : Lp ℂ 2 haarAddCircle) x) =
        (kernelCoefficient k : ℂ) * fourier k x := by
    apply ae_all_iff.mpr
    intro k
    filter_upwards [Lp.coeFn_smul (kernelCoefficient k : ℂ)
      (fourierLp 2 k : Lp ℂ 2 (@haarAddCircle Real.pi period_pos)), coeFn_fourierLp 2 k] with x hx hfour
    simpa only [Pi.smul_apply, smul_eq_mul, hfour] using hx
  filter_upwards [hs, ha] with x hx hxa
  exact hx.trans (sum_congr rfl (fun k _ => hxa k))

theorem half_circle_fourier (k : ℤ) (t : ℝ) :
    fourier k (t : AddCircle Real.pi) = oscillation (2 * k) t := by
  rw [fourier_coe_apply]
  unfold oscillation
  congr 1
  push_cast
  field_simp

theorem oscillation_frequency_add (p q t : ℝ) :
    oscillation p t * oscillation q t = oscillation (p + q) t := by
  unfold oscillation
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem oscillation_cosine_pair (p t : ℝ) :
    oscillation p t + oscillation (-p) t = (2 * cos (p * t) : ℝ) := by
  apply Complex.ext
  · simp only [oscillation, Complex.add_re, Complex.exp_ofReal_mul_I_re,
      Complex.ofReal_re, neg_mul, cos_neg]
    ring
  · simp only [oscillation, Complex.add_im, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_im, neg_mul, sin_neg, add_neg_cancel]

theorem circlePartial_at_real (P : ℕ) (t : ℝ) :
    (∑ k ∈ signedCutoff P, (kernelCoefficient k : ℂ) * fourier k (t : AddCircle Real.pi)) =
      modulated (seriesPartial P) t := by
  rw [sum_signedCutoff]
  unfold modulated seriesPartial
  rw [Complex.ofReal_sum]
  rw [sum_mul]
  apply sum_congr rfl
  intro k _
  rw [half_circle_fourier, half_circle_fourier]
  have hn : 2 * (Int.negSucc k : ℝ) = -(2 * (k : ℝ) + 1) + (-1) := by
    simp only [Int.cast_negSucc]
    push_cast
    ring
  have hp : 2 * ((k : ℤ) : ℝ) = (2 * (k : ℝ) + 1) + (-1) := by push_cast; ring
  rw [hn, hp, ← oscillation_frequency_add (2 * (k : ℝ) + 1) (-1) t,
    ← oscillation_frequency_add (-(2 * (k : ℝ) + 1)) (-1) t]
  change (naturalKernelCoefficient k : ℂ) *
      (oscillation (2 * k + 1) t * oscillation (-1) t) +
    (naturalKernelCoefficient k : ℂ) * (oscillation (-(2 * k + 1)) t * oscillation (-1) t) = _
  rw [show (naturalKernelCoefficient k : ℂ) * (oscillation (2 * k + 1) t * oscillation (-1) t) +
      (naturalKernelCoefficient k : ℂ) * (oscillation (-(2 * k + 1)) t * oscillation (-1) t) =
      (naturalKernelCoefficient k : ℂ) *
        (oscillation (2 * k + 1) t + oscillation (-(2 * k + 1)) t) * oscillation (-1) t by ring,
    oscillation_cosine_pair]
  simp only [kernelCoefficient, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

theorem seriesLimit_ae_eq_kernel :
    seriesLimit =ᵐ[volume.restrict (Set.Ioo 0 Real.pi)] kernel := by
  obtain ⟨ns, hns, hlim⟩ :=
    (tendstoInMeasure_of_tendsto_Lp circlePartial_tendsto).exists_seq_tendsto_ae
  have ha : ∀ᵐ x : AddCircle Real.pi ∂haarAddCircle,
      (∀ P : ℕ, circlePartial P x =
        ∑ k ∈ signedCutoff P, (kernelCoefficient k : ℂ) * fourier k x) ∧
      kernelLp x = AddCircle.liftIoc Real.pi 0 (modulated kernel) x ∧
      Tendsto (fun i => circlePartial (ns i) x) atTop (𝓝 (kernelLp x)) := by
    filter_upwards [ae_all_iff.mpr circlePartial_coe, liftedKernel_memLp.coeFn_toLp, hlim]
      with x hx hk hlimx
    exact ⟨hx, hk, hlimx⟩
  have hav := Measure.ae_smul_measure ha (ENNReal.ofReal Real.pi)
  rw [← volume_eq_smul_haarAddCircle] at hav
  have har := (AddCircle.measurePreserving_mk Real.pi 0).quasiMeasurePreserving.ae hav
  simp only [zero_add] at har
  have hari := ae_restrict_of_ae_restrict_of_subset Set.Ioo_subset_Ioc_self har
  filter_upwards [hari, self_mem_ae_restrict measurableSet_Ioo] with t ht hti
  obtain ⟨hpart, hK, hconv⟩ := ht
  have hsin := (sin_pos_of_pos_of_lt_pi hti.1 hti.2).ne'
  have hactual : Tendsto (fun i => modulated (seriesPartial (ns i)) t) atTop
      (𝓝 (modulated kernel t)) := by
    have hcoe : (t : ℝ) ∈ Set.Ioc 0 (0 + Real.pi) := by
      simpa only [zero_add] using (show t ∈ Set.Ioc 0 Real.pi from ⟨hti.1, hti.2.le⟩)
    rw [hK, liftIoc_coe_apply hcoe] at hconv
    exact hconv.congr (fun i => (hpart (ns i)).trans (circlePartial_at_real (ns i) t))
  have hseries : Tendsto (fun i => modulated (seriesPartial (ns i)) t) atTop
      (𝓝 ((seriesLimit t : ℂ) * oscillation (-1) t)) := by
    exact ((series_tendsto hsin).comp hns.tendsto_atTop).ofReal.mul_const (oscillation (-1) t)
  have he := tendsto_nhds_unique hseries hactual
  have ho : oscillation (-1) t ≠ 0 := Complex.exp_ne_zero _
  have hreal := mul_right_cancel₀ ho he
  exact_mod_cast hreal

theorem kernel_continuousAt {t : ℝ} (ht : t ∈ Set.Ioo 0 Real.pi) :
    ContinuousAt kernel t := by
  have hs := (sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne'
  have hs2 : 2 * sin t ≠ 0 := mul_ne_zero (by norm_num) hs
  unfold kernel
  fun_prop

theorem seriesLimit_eq_kernel {t : ℝ} (ht : t ∈ Set.Ioo 0 Real.pi) :
    seriesLimit t = kernel t := by
  apply Measure.eqOn_open_of_ae_eq seriesLimit_ae_eq_kernel isOpen_Ioo _ _ ht
  · exact fun x hx => (seriesLimit_continuousAt (sin_pos_of_pos_of_lt_pi hx.1 hx.2).ne').continuousWithinAt
  · exact fun x hx => (kernel_continuousAt hx).continuousWithinAt

end
end StructuralNote.FixedDualClassificationKernelUniformIdentification
