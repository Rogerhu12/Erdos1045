import StructuralNote.FixedDualClassificationCoefficientBound
import Mathlib.Analysis.Complex.Harmonic.Poisson

/-! The analytic half of a bounded real boundary function lies in its actual strip. -/

namespace StructuralNote.FixedDualClassificationHerglotz

open Real MeasureTheory Set Metric InnerProductSpace
noncomputable section

def analyticHalf (f : ℂ → ℝ) (w : ℂ) : ℂ :=
  circleAverage (fun ζ => herglotzRieszKernel 0 w ζ * (f ζ : ℂ)) 0 1 / 2

theorem boundary_ofReal_integrable {f : ℂ → ℝ} (hf : CircleIntegrable f 0 1) :
    CircleIntegrable (fun ζ => (f ζ : ℂ)) 0 1 := by
  exact ⟨hf.1.ofReal, hf.2.ofReal⟩

theorem analyticHalf_analytic {f : ℂ → ℝ} (hf : CircleIntegrable f 0 1) :
    AnalyticOnNhd ℂ (analyticHalf f) (ball 0 1) := by
  have h := analyticOnNhd_circleAverage_herglotzRieszKernel_smul
    (boundary_ofReal_integrable hf)
  intro w hw
  exact (h w hw).div_const

theorem poisson_nonneg {w ζ : ℂ} (hw : w ∈ ball 0 1) (hζ : ζ ∈ sphere 0 1) :
    0 ≤ poissonKernel 0 w ζ := by
  have hw' : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
  have hζ' : ‖ζ‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hζ
  simp only [poissonKernel_def, sub_zero, hζ']
  apply div_nonneg _ (sq_nonneg _)
  nlinarith [norm_nonneg w]

theorem poisson_mass_one {w : ℂ} (hw : w ∈ ball 0 1) :
    circleAverage (poissonKernel 0 w) 0 1 = 1 := by
  have h := (harmonicOnNhd_const (1 : ℝ) :
    InnerProductSpace.HarmonicOnNhd (fun _ : ℂ => (1 : ℝ)) (closedBall 0 1)).circleAverage_poissonKernel_smul hw
  simpa [Pi.smul_def, smul_eq_mul, Pi.mul_def] using h

theorem poisson_continuous {w : ℂ} (hw : w ∈ ball 0 1) :
    ContinuousOn (poissonKernel 0 w) (sphere 0 1) := by
  rw [poissonKernel_eq_re_herglotzRieszKernel]
  apply Complex.continuous_re.comp_continuousOn
  simpa only [abs_one] using continuousOn_herglotzRieszKernel_sphere hw

theorem analyticHalf_re {f : ℂ → ℝ} (hf : CircleIntegrable f 0 1)
    {w : ℂ} (hw : w ∈ ball 0 1) :
    (analyticHalf f w).re = circleAverage (fun ζ => poissonKernel 0 w ζ * f ζ) 0 1 / 2 := by
  have h := re_circleAverage_herglotzRieszKernel_smul hf hw
  change (circleAverage (fun ζ => herglotzRieszKernel 0 w ζ * (f ζ : ℂ)) 0 1).re =
    circleAverage (fun ζ => (herglotzRieszKernel 0 w ζ).re * f ζ) 0 1 at h
  unfold analyticHalf
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_re, h]
  simp only [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply]

theorem analyticHalf_strip {f : ℂ → ℝ} (hf : CircleIntegrable f 0 1)
    {A : ℝ} (hbox : ∀ ζ ∈ sphere 0 1, |f ζ| ≤ A)
    {w : ℂ} (hw : w ∈ ball 0 1) : |(analyticHalf f w).re| ≤ A / 2 := by
  have hk := poisson_continuous hw
  have hprod : CircleIntegrable (fun ζ => poissonKernel 0 w ζ * f ζ) 0 1 := by
    exact hf.continuousOn_smul (by simpa only [abs_one] using hk)
  have hconst : CircleIntegrable (fun ζ => A * poissonKernel 0 w ζ) 0 1 :=
    (continuousOn_const.mul hk).circleIntegrable (by norm_num)
  have hmono := circleAverage_mono hprod.abs hconst (fun ζ hζ => by
    simp only [abs_one] at hζ
    change |poissonKernel 0 w ζ * f ζ| ≤ A * poissonKernel 0 w ζ
    rw [abs_mul, abs_of_nonneg (poisson_nonneg hw hζ), mul_comm A]
    exact mul_le_mul_of_nonneg_left (hbox ζ hζ) (poisson_nonneg hw hζ))
  have hmass : circleAverage (fun ζ => A * poissonKernel 0 w ζ) 0 1 = A := by
    change circleAverage (fun ζ => A • poissonKernel 0 w ζ) 0 1 = A
    rw [circleAverage_fun_smul, poisson_mass_one hw, smul_eq_mul, mul_one]
  have havg := abs_circleAverage_le_circleAverage_abs
    (f := fun ζ => poissonKernel 0 w ζ * f ζ) (c := 0) (R := 1)
  rw [hmass] at hmono
  rw [analyticHalf_re hf hw, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact div_le_div_of_nonneg_right (havg.trans hmono) (by norm_num)

theorem analyticHalf_zero {f : ℂ → ℝ} (hf : CircleIntegrable f 0 1)
    (hmean : circleAverage f 0 1 = 0) : analyticHalf f 0 = 0 := by
  have hcoe := Complex.ofRealCLM.circleAverage_comp_comm hf
  change circleAverage (fun ζ => (f ζ : ℂ)) 0 1 = ((circleAverage f 0 1 : ℝ) : ℂ) at hcoe
  unfold analyticHalf
  have he : circleAverage (fun ζ => herglotzRieszKernel 0 0 ζ * (f ζ : ℂ)) 0 1 =
      circleAverage (fun ζ => (f ζ : ℂ)) 0 1 := by
    apply circleAverage_congr_sphere
    intro ζ hζ
    have hζ' : ζ ≠ 0 := by
      have hz : ‖ζ‖ = 1 := by simpa only [mem_sphere, dist_zero_right, abs_one] using hζ
      intro h
      simp only [h, norm_zero] at hz
      norm_num at hz
    simp only [herglotzRieszKernel_def, sub_zero, add_zero, div_self hζ', one_mul]
  rw [he, hcoe, hmean]
  norm_num

end
end StructuralNote.FixedDualClassificationHerglotz
