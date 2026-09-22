import PositiveRealQuadratic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Derivative growth from the convex exterior analytic criterion

For a normalized analytic, zero-free function D, with D'(0)=0, the condition
Re(1-zD'(z)/D(z)) >= 0 implies |D(z)| <= 1+|z|^2.
This module proves the analytic implication only. It does not assert that
an exterior mapping has the required geometric criterion.
-/

namespace ExteriorReduction

open Complex Metric Set Filter
open scoped Topology ComplexConjugate

noncomputable section

def derivativeCriterion (D : ℂ → ℂ) (z : ℂ) : ℂ :=
  1 - z * deriv D z / D z

theorem analytic_derivativeCriterion {D : ℂ → ℂ}
    (hD : AnalyticOnNhd ℂ D (ball 0 1))
    (hne : ∀ z ∈ ball 0 1, D z ≠ 0) :
    AnalyticOnNhd ℂ (derivativeCriterion D) (ball 0 1) := by
  exact analyticOnNhd_const.sub ((analyticOnNhd_id.mul hD.deriv).div hD hne)

theorem derivativeCriterion_hasDerivAt_zero {D : ℂ → ℂ}
    (hD : AnalyticOnNhd ℂ D (ball 0 1)) (hzero : D 0 = 1)
    (hdzero : deriv D 0 = 0) : HasDerivAt (derivativeCriterion D) 0 0 := by
  have hz : (0 : ℂ) ∈ ball 0 1 := by simp
  have h := (hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub
    (((hasDerivAt_id (0 : ℂ)).mul (hD.deriv 0 hz).differentiableAt.hasDerivAt).div
      (hD 0 hz).differentiableAt.hasDerivAt (by simp [hzero]))
  convert! h using 1
  simp [hzero, hdzero]

theorem logarithmic_derivative_quadratic_bound {D : ℂ → ℂ}
    (hD : AnalyticOnNhd ℂ D (ball 0 1))
    (hne : ∀ z ∈ ball 0 1, D z ≠ 0) (hzero : D 0 = 1)
    (hdzero : deriv D 0 = 0)
    (hpos : ∀ z ∈ ball 0 1, 0 ≤ (derivativeCriterion D z).re)
    {z : ℂ} (hz : z ∈ ball 0 1) :
    (z * deriv D z / D z).re ≤ 2 * ‖z‖ ^ 2 / (1 + ‖z‖ ^ 2) := by
  have h := positive_real_quadratic_lower_bound (analytic_derivativeCriterion hD hne)
    (by simp [derivativeCriterion])
    (derivativeCriterion_hasDerivAt_zero hD hzero hdzero) hpos hz
  simp only [derivativeCriterion, Complex.sub_re, Complex.one_re] at h
  have hp : 0 < 1 + ‖z‖ ^ 2 := by positivity
  rw [div_le_iff₀ hp] at h
  rw [le_div_iff₀ hp]
  nlinarith

theorem re_div_mul_norm_sq (a : ℂ) {b : ℂ} (hb : b ≠ 0) :
    (a / b).re * ‖b‖ ^ 2 = (a * conj b).re := by
  rw [Complex.div_re, Complex.normSq_eq_norm_sq]
  have hn : ‖b‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hb)
  field_simp
  simp [Complex.mul_re]

private theorem norm_mul_real (t : ℝ) (z : ℂ) (ht : 0 ≤ t) :
    ‖(t : ℂ) * z‖ = t * ‖z‖ := by
  simp [abs_of_nonneg ht]

/-- Integrating the growth estimate uses only the smooth norm square. -/
theorem norm_le_one_add_sq_of_logarithmic_derivative_bound {D : ℂ → ℂ}
    (hD : AnalyticOnNhd ℂ D (ball 0 1))
    (hne : ∀ z ∈ ball 0 1, D z ≠ 0) (hzero : D 0 = 1)
    (hlog : ∀ z ∈ ball 0 1,
      (z * deriv D z / D z).re ≤ 2 * ‖z‖ ^ 2 / (1 + ‖z‖ ^ 2))
    {z : ℂ} (hz : z ∈ ball 0 1) : ‖D z‖ ≤ 1 + ‖z‖ ^ 2 := by
  have hzlt : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (t : ℂ) * z ∈ ball 0 1 := by
    rw [mem_ball_zero_iff, norm_mul_real t z ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hzlt
  let S : ℝ → ℝ := fun t => ‖D ((t : ℂ) * z)‖ ^ 2
  let A : ℝ → ℝ := fun t => 1 + t ^ 2 * ‖z‖ ^ 2
  let b : ℝ → ℝ := fun t => (deriv D ((t : ℂ) * z) * z * conj (D ((t : ℂ) * z))).re
  have hS (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt S (2 * b t) t := by
    have hc := ((hD _ (hmem t ht)).differentiableAt.hasDerivAt.comp (t : ℂ)
      ((hasDerivAt_id (t : ℂ)).mul_const z)).comp_ofReal
    simpa [S, b, Complex.inner] using! hc.norm_sq
  have hA (t : ℝ) : HasDerivAt A (2 * t * ‖z‖ ^ 2) t := by
    convert! (((hasDerivAt_id t).pow 2).mul_const (‖z‖ ^ 2)).const_add 1 using 1
    simp
  have hApos (t : ℝ) : 0 < A t := by dsimp [A]; positivity
  have hratio (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t => S t / A t ^ 2)
        ((2 * b t * A t ^ 2 - S t * (2 * A t * (2 * t * ‖z‖ ^ 2))) /
          (A t ^ 2) ^ 2) t := by
    convert! (hS t ht).div ((hA t).pow 2) (pow_ne_zero 2 (hApos t).ne') using 1
    simp
  have hnonpos (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      (2 * b t * A t ^ 2 - S t * (2 * A t * (2 * t * ‖z‖ ^ 2))) /
          (A t ^ 2) ^ 2 ≤ 0 := by
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have he : t * b t = (((t : ℂ) * z) * deriv D ((t : ℂ) * z) /
        D ((t : ℂ) * z)).re * S t := by
      dsimp only [S]
      rw [re_div_mul_norm_sq _ (hne _ (hmem t ht'))]
      simp only [b, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
      ring
    have hbnd := hlog _ (hmem t ht')
    rw [norm_mul_real t z ht.1.le, mul_pow] at hbnd
    have hbnd' : t * b t ≤ (2 * t ^ 2 * ‖z‖ ^ 2 / A t) * S t := by
      rw [he]
      exact mul_le_mul_of_nonneg_right (by simpa [A, mul_assoc] using hbnd) (sq_nonneg _)
    have hbnd'' : b t * A t ≤ 2 * t * ‖z‖ ^ 2 * S t := by
      have hh := (le_div_iff₀ (hApos t)).mp
        (show t * b t ≤ 2 * t ^ 2 * ‖z‖ ^ 2 * S t / A t by
          simpa [div_mul_eq_mul_div] using hbnd')
      nlinarith [ht.1]
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_right hbnd'' (hApos t).le]
  have hc : ContinuousOn (fun t => S t / A t ^ 2) (Icc (0 : ℝ) 1) :=
    fun t ht => (hratio t ht).continuousAt.continuousWithinAt
  have hm : AntitoneOn (fun t => S t / A t ^ 2) (Icc (0 : ℝ) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1) hc
    · intro t ht
      have ht' : t ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using ht
      exact (hratio t ⟨ht'.1.le, ht'.2.le⟩).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using ht
      rw [(hratio t ⟨ht'.1.le, ht'.2.le⟩).deriv]
      exact hnonpos t ht'
  have hend := hm (show (0 : ℝ) ∈ Icc 0 1 by simp)
    (show (1 : ℝ) ∈ Icc 0 1 by simp) zero_le_one
  have hsquare : ‖D z‖ ^ 2 ≤ (1 + ‖z‖ ^ 2) ^ 2 := by
    have : ‖D z‖ ^ 2 / (1 + ‖z‖ ^ 2) ^ 2 ≤ 1 := by simpa [S, A, hzero] using hend
    exact (div_le_one (by positivity)).mp this
  nlinarith [norm_nonneg (D z), sq_nonneg ‖z‖]

theorem normalized_derivative_bound {D : ℂ → ℂ}
    (hD : AnalyticOnNhd ℂ D (ball 0 1))
    (hne : ∀ z ∈ ball 0 1, D z ≠ 0) (hzero : D 0 = 1)
    (hdzero : deriv D 0 = 0)
    (hpos : ∀ z ∈ ball 0 1, 0 ≤ (derivativeCriterion D z).re)
    {z : ℂ} (hz : z ∈ ball 0 1) : ‖D z‖ ≤ 1 + ‖z‖ ^ 2 :=
  norm_le_one_add_sq_of_logarithmic_derivative_bound hD hne hzero
    (fun _ hw => logarithmic_derivative_quadratic_bound hD hne hzero hdzero hpos hw) hz

#print axioms normalized_derivative_bound

/-- Radial comparison entirely inside the disk; boundary derivatives are not used. -/
theorem normalized_derivative_radial_comparison {D : ℂ → ℂ}
    (hD : AnalyticOnNhd ℂ D (ball 0 1))
    (hne : ∀ z ∈ ball 0 1, D z ≠ 0)
    (hpos : ∀ z ∈ ball 0 1, 0 ≤ (derivativeCriterion D z).re)
    {u : ℂ} (hu : ‖u‖ = 1) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    a * ‖D ((b : ℂ) * u)‖ ≤ b * ‖D ((a : ℂ) * u)‖ := by
  let S : ℝ → ℝ := fun t => ‖D ((t : ℂ) * u)‖ ^ 2
  let V : ℝ → ℝ := fun t => (deriv D ((t : ℂ) * u) * u * conj (D ((t : ℂ) * u))).re
  have htpos (t : ℝ) (ht : t ∈ Icc a b) : 0 < t := ha.trans_le ht.1
  have hmem (t : ℝ) (ht : t ∈ Icc a b) : (t : ℂ) * u ∈ ball 0 1 := by
    rw [mem_ball_zero_iff, norm_mul_real t u (htpos t ht).le, hu, mul_one]
    exact ht.2.trans_lt hb
  have hS (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt S (2 * V t) t := by
    have hc := ((hD _ (hmem t ht)).differentiableAt.hasDerivAt.comp (t : ℂ)
      ((hasDerivAt_id (t : ℂ)).mul_const u)).comp_ofReal
    simpa [S, V, Complex.inner] using! hc.norm_sq
  have hratio (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (fun t => S t / t ^ 2)
        ((2 * V t * t ^ 2 - S t * (2 * t)) / (t ^ 2) ^ 2) t := by
    convert! (hS t ht).div ((hasDerivAt_id t).pow 2)
      (pow_ne_zero 2 (htpos t ht).ne') using 1
    simp
  have hnonpos (t : ℝ) (ht : t ∈ Icc a b) :
      (2 * V t * t ^ 2 - S t * (2 * t)) / (t ^ 2) ^ 2 ≤ 0 := by
    have he : t * V t = (((t : ℂ) * u) * deriv D ((t : ℂ) * u) /
        D ((t : ℂ) * u)).re * S t := by
      dsimp only [S]
      rw [re_div_mul_norm_sq _ (hne _ (hmem t ht))]
      simp only [V, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
      ring
    have hp := hpos _ (hmem t ht)
    simp only [derivativeCriterion, Complex.sub_re, Complex.one_re] at hp
    have hh : t * V t ≤ S t := by
      rw [he]
      exact mul_le_of_le_one_left (sq_nonneg _) (by linarith)
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_left hh (htpos t ht).le]
  have hm : AntitoneOn (fun t => S t / t ^ 2) (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
      (fun t ht => (hratio t ht).continuousAt.continuousWithinAt)
    · intro t ht
      exact (hratio t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hratio t (interior_subset ht)).deriv]
      exact hnonpos t (interior_subset ht)
  have hend := hm (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  have habsq : S b * a ^ 2 ≤ S a * b ^ 2 :=
    (div_le_div_iff₀ (sq_pos_of_pos (ha.trans_le hab)) (sq_pos_of_pos ha)).mp hend
  dsimp only [S] at habsq
  have hleft : 0 ≤ a * ‖D ((b : ℂ) * u)‖ := mul_nonneg ha.le (norm_nonneg _)
  have hright : 0 ≤ b * ‖D ((a : ℂ) * u)‖ :=
    mul_nonneg (ha.le.trans hab) (norm_nonneg _)
  nlinarith

#print axioms normalized_derivative_radial_comparison

end
end ExteriorReduction
