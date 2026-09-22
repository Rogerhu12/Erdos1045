import StructuralNote.FixedDualClassificationHerglotz
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! The analytic half has exactly the positive boundary Fourier coefficients. -/

namespace StructuralNote.FixedDualClassificationHerglotzSeries

open Real Complex Set Metric Filter FormalMultilinearSeries
open FixedDualClassificationHerglotz
open scoped Topology
noncomputable section

theorem sphere_ne_zero {ζ : ℂ} (hζ : ζ ∈ sphere 0 1) : ζ ≠ 0 := by
  have hnorm : ‖ζ‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hζ
  intro hz
  simp only [hz, norm_zero] at hnorm
  norm_num at hnorm

theorem cauchy_eq_average (g : ℂ → ℂ) {w : ℂ} :
    (2 * Real.pi * Complex.I)⁻¹ • (∮ ζ in C(0, 1), (ζ - w)⁻¹ • g ζ) =
      circleAverage (fun ζ => (ζ / (ζ - w)) * g ζ) 0 1 := by
  rw [circleAverage_eq_circleIntegral (by norm_num : (1 : ℝ) ≠ 0)]
  congr 1
  apply circleIntegral.integral_congr (by norm_num)
  intro ζ hζ
  have hz := sphere_ne_zero hζ
  simp only [sub_zero, smul_eq_mul]
  field_simp

theorem analyticHalf_eq_cauchy {f : ℂ → ℝ} (hf : CircleIntegrable f 0 1)
    (hmean : circleAverage f 0 1 = 0) {w : ℂ} (hw : w ∈ ball 0 1) :
    analyticHalf f w = (2 * Real.pi * Complex.I)⁻¹ •
      (∮ ζ in C(0, 1), (ζ - w)⁻¹ • (f ζ : ℂ)) := by
  have hfc := boundary_ofReal_integrable hf
  have hkc : CircleIntegrable (fun ζ => herglotzRieszKernel 0 w ζ * (f ζ : ℂ)) 0 1 :=
    hfc.continuousOn_smul (continuousOn_herglotzRieszKernel_sphere hw)
  have hmeanC : circleAverage (fun ζ => (f ζ : ℂ)) 0 1 = 0 := by
    have h := Complex.ofRealCLM.circleAverage_comp_comm hf
    change circleAverage (fun ζ => (f ζ : ℂ)) 0 1 = ((circleAverage f 0 1 : ℝ) : ℂ) at h
    simpa only [hmean, Complex.ofReal_zero] using h
  have he : circleAverage (fun ζ => (ζ / (ζ - w)) * (f ζ : ℂ)) 0 1 =
      (circleAverage (fun ζ => herglotzRieszKernel 0 w ζ * (f ζ : ℂ)) 0 1 +
        circleAverage (fun ζ => (f ζ : ℂ)) 0 1) / 2 := by
    rw [← circleAverage_fun_add hkc hfc]
    have hs := circleAverage_fun_smul (a := (2 : ℂ)⁻¹)
      (f := fun ζ => herglotzRieszKernel 0 w ζ * (f ζ : ℂ) + (f ζ : ℂ))
      (c := 0) (R := 1)
    simp only [smul_eq_mul] at hs
    rw [show _ / (2 : ℂ) = (2 : ℂ)⁻¹ * _ by ring, ← hs]
    apply circleAverage_congr_sphere
    intro ζ hζ
    have hζ' : ζ ∈ sphere (0 : ℂ) 1 := by simpa only [abs_one] using hζ
    have hzw : ζ - w ≠ 0 := sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hζ' hw)
    simp only [herglotzRieszKernel_def, sub_zero]
    field_simp
    ring
  rw [cauchy_eq_average, he, hmeanC, add_zero]
  rfl

theorem analyticHalf_hasFPowerSeries {f : ℂ → ℝ} (hf : CircleIntegrable f 0 1)
    (hmean : circleAverage f 0 1 = 0) :
    HasFPowerSeriesAt (analyticHalf f) (cauchyPowerSeries (fun ζ => (f ζ : ℂ)) 0 1) 0 := by
  have h := (hasFPowerSeriesOn_cauchy_integral (R := 1)
    (boundary_ofReal_integrable hf) (by norm_num)).hasFPowerSeriesAt
  apply h.congr
  filter_upwards [ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with w hw
  exact (analyticHalf_eq_cauchy hf hmean hw).symm

theorem cauchy_coefficient (g : ℂ → ℂ) (k : ℕ) :
    (cauchyPowerSeries g 0 1).coeff k = circleAverage (fun ζ => g ζ / ζ ^ k) 0 1 := by
  change (cauchyPowerSeries g 0 1 k (fun _ => 1)) = _
  rw [cauchyPowerSeries_apply, circleAverage_eq_circleIntegral (by norm_num : (1 : ℝ) ≠ 0)]
  congr 1
  apply circleIntegral.integral_congr (by norm_num)
  intro ζ _
  simp only [sub_zero, smul_eq_mul, div_eq_mul_inv]
  ring

theorem analyticHalf_dslope_coefficient {f : ℂ → ℝ} (hf : CircleIntegrable f 0 1)
    (hmean : circleAverage f 0 1 = 0) (k : ℕ) :
    ((Function.swap dslope 0)^[k] (analyticHalf f)) 0 =
      circleAverage (fun ζ => (f ζ : ℂ) / ζ ^ k) 0 1 := by
  have h := (analyticHalf_hasFPowerSeries hf hmean).has_fpower_series_iterate_dslope_fslope k
  have he : ((fslope^[k]) (cauchyPowerSeries (fun ζ => (f ζ : ℂ)) 0 1)).coeff 0 =
      ((Function.swap dslope 0)^[k] (analyticHalf f)) 0 := h.coeff_zero 1
  rw [coeff_iterate_fslope, zero_add, cauchy_coefficient] at he
  exact he.symm

end
end StructuralNote.FixedDualClassificationHerglotzSeries
