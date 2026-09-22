import StructuralNote.FixedDualClassificationHerglotz
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ComplexDeriv

/-! The elementary strip-to-disk map needed for the sharp coefficient constraint. -/

namespace StructuralNote.FixedDualClassificationTanStrip

open Real Set Metric
open FixedDualClassificationHerglotz
noncomputable section

theorem cosine_sine_normSq_difference (z : ℂ) :
    Complex.normSq (Complex.cos z) - Complex.normSq (Complex.sin z) = cos (2 * z.re) := by
  have he : Complex.normSq (Complex.cos z) - Complex.normSq (Complex.sin z) =
      (cos z.re ^ 2 - sin z.re ^ 2) * (cosh z.im ^ 2 - sinh z.im ^ 2) := by
    rw [Complex.cos_eq z, Complex.sin_eq z]
    simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cosh,
      ← Complex.ofReal_sinh, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [he, cosh_sq_sub_sinh_sq, mul_one, cos_two_mul]
  nlinarith [sin_sq_add_cos_sq z.re]

theorem cosine_ne_zero_of_strip {z : ℂ} (hz : |z.re| ≤ Real.pi / 4) : Complex.cos z ≠ 0 := by
  have harg : z.re ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    have hb := abs_le.mp hz
    constructor <;> linarith [pi_pos]
  have hre : (Complex.cos z).re = cos z.re * cosh z.im := by
    rw [Complex.cos_eq z]
    simp [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cosh,
      ← Complex.ofReal_sinh]
  have hp := mul_pos (cos_pos_of_mem_Ioo harg) (cosh_pos z.im)
  intro h
  rw [← hre, h, Complex.zero_re] at hp
  exact (lt_irrefl 0) hp

theorem tangent_norm_le_one_of_strip {z : ℂ} (hz : |z.re| ≤ Real.pi / 4) :
    ‖Complex.tan z‖ ≤ 1 := by
  have harg : 2 * z.re ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    have hb := abs_le.mp hz
    constructor <;> linarith
  have hn := cosine_sine_normSq_difference z
  have hcos := cos_nonneg_of_mem_Icc harg
  have hsq : ‖Complex.sin z‖ ^ 2 ≤ ‖Complex.cos z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    linarith
  have hm := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  rw [Complex.tan, norm_div]
  exact (div_le_one (norm_pos_iff.mpr (cosine_ne_zero_of_strip hz))).mpr hm

def diskMap (f : ℂ → ℝ) (z : ℂ) : ℂ := Complex.tan (analyticHalf f z)

theorem diskMap_differentiable {f : ℂ → ℝ} (hf : CircleIntegrable f 0 1)
    (hbox : ∀ ζ ∈ sphere 0 1, |f ζ| ≤ Real.pi / 2) :
    DifferentiableOn ℂ (diskMap f) (ball 0 1) := by
  intro z hz
  have hs : |(analyticHalf f z).re| ≤ Real.pi / 4 := by
    have h := analyticHalf_strip hf hbox hz
    linarith
  exact ((Complex.differentiableAt_tan.mpr (cosine_ne_zero_of_strip hs)).comp z
    ((analyticHalf_analytic hf z hz).differentiableAt)).differentiableWithinAt

theorem diskMap_mapsTo {f : ℂ → ℝ} (hf : CircleIntegrable f 0 1)
    (hbox : ∀ ζ ∈ sphere 0 1, |f ζ| ≤ Real.pi / 2) :
    MapsTo (diskMap f) (ball 0 1) (closedBall 0 1) := by
  intro z hz
  rw [mem_closedBall, dist_zero_right]
  apply tangent_norm_le_one_of_strip
  have h := analyticHalf_strip hf hbox hz
  linarith

theorem diskMap_zero {f : ℂ → ℝ} (hf : CircleIntegrable f 0 1)
    (hmean : circleAverage f 0 1 = 0) : diskMap f 0 = 0 := by
  rw [diskMap, analyticHalf_zero hf hmean, Complex.tan_zero]

end
end StructuralNote.FixedDualClassificationTanStrip
