import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.Poisson
import Mathlib.Tactic

/-!
# A quadratic Harnack bound without a representation theorem

The extra normalization `P'(0) = 0` improves the ordinary Harnack radius
from `‖z‖` to `‖z‖ ^ 2`. This is the estimate needed for the normalized
exterior derivative. The geometric reason that its logarithmic derivative
has positive real part is a separate, still outstanding, theorem.
-/

namespace ExteriorReduction

open Complex Metric Set Filter
open scoped Topology

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

def positiveCayley (p : ℂ) : ℂ := (p - 1) / (p + 1)

theorem positiveCayley_denominator_ne {p : ℂ} (hp : 0 ≤ p.re) : p + 1 ≠ 0 := by
  intro h
  have h' := congrArg Complex.re h
  simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at h'
  linarith

theorem positiveCayley_norm_le_one {p : ℂ} (hp : 0 ≤ p.re) :
    ‖positiveCayley p‖ ≤ 1 := by
  rw [positiveCayley, norm_div, div_le_one (norm_pos_iff.mpr
    (positiveCayley_denominator_ne hp))]
  have hs : ‖p - 1‖ ^ 2 ≤ ‖p + 1‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
    nlinarith
  nlinarith [norm_nonneg (p - 1), norm_nonneg (p + 1)]

/-- Schwarz with a zero of order at least two, stated in derivative form. -/
theorem schwarz_quadratic {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hzero : f 0 = 0)
    (hderiv : HasDerivAt f 0 0)
    (hbound : ∀ z ∈ ball 0 1, ‖f z‖ ≤ 1) {z : ℂ} (hz : z ∈ ball 0 1) :
    ‖f z‖ ≤ ‖z‖ ^ 2 := by
  have ho : (fun w => f w - f 0) =o[𝓝 0] (fun w : ℂ => ‖w - 0‖ ^ 1) := by
    simpa only [smul_zero, sub_zero, pow_one] using hderiv.isLittleO.norm_right
  have hm : MapsTo f (ball 0 1) (closedBall (f 0) 1) := by
    intro w hw
    simpa only [hzero, mem_closedBall_zero_iff] using hbound w hw
  simpa only [hzero, dist_zero_right, div_one, one_mul] using
    Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO hf hm ho hz

theorem positiveCayley_norm_le_sq {P : ℂ → ℂ}
    (hP : AnalyticOnNhd ℂ P (ball 0 1)) (hzero : P 0 = 1)
    (hderiv : HasDerivAt P 0 0)
    (hre : ∀ z ∈ ball 0 1, 0 ≤ (P z).re)
    {z : ℂ} (hz : z ∈ ball 0 1) :
    ‖positiveCayley (P z)‖ ≤ ‖z‖ ^ 2 := by
  have hd : DifferentiableOn ℂ (fun z => positiveCayley (P z)) (ball 0 1) := by
    exact (hP.differentiableOn.sub_const 1).div (hP.differentiableOn.add_const 1)
      (fun z hz => positiveCayley_denominator_ne (hre z hz))
  have hz0 : positiveCayley (P 0) = 0 := by simp [positiveCayley, hzero]
  have hd0 : HasDerivAt (fun z => positiveCayley (P z)) 0 0 := by
    convert! (hderiv.sub_const 1).div (hderiv.add_const 1) (by simp [hzero])
      using 1
    simp [hzero]
  exact schwarz_quadratic hd hz0 hd0
    (fun z hz => positiveCayley_norm_le_one (hre z hz)) hz

theorem positiveCayley_inverse {p : ℂ} (hp : p + 1 ≠ 0) :
    (1 + positiveCayley p) / (1 - positiveCayley p) = p := by
  unfold positiveCayley
  have hn : 1 - (p - 1) / (p + 1) ≠ 0 := by
    intro h
    have h' : (p - 1) / (p + 1) = 1 := by linear_combination -h
    have h'' := (div_eq_iff hp).mp h'
    have hf : (0 : ℂ) = 2 := by linear_combination h''
    norm_num at hf
  rw [div_eq_iff hn]
  field_simp
  ring

/-- The normalization at infinity yields the quadratic radius in this estimate. -/
theorem positive_real_quadratic_lower_bound {P : ℂ → ℂ}
    (hP : AnalyticOnNhd ℂ P (ball 0 1)) (hzero : P 0 = 1)
    (hderiv : HasDerivAt P 0 0)
    (hre : ∀ z ∈ ball 0 1, 0 ≤ (P z).re)
    {z : ℂ} (hz : z ∈ ball 0 1) :
    (1 - ‖z‖ ^ 2) / (1 + ‖z‖ ^ 2) ≤ (P z).re := by
  have hw := positiveCayley_norm_le_sq hP hzero hderiv hre hz
  have hzlt : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hsq : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
  have hwlt : positiveCayley (P z) ∈ ball (0 : ℂ) 1 :=
    mem_ball_zero_iff.mpr (hw.trans_lt hsq)
  have hk := le_re_herglotzRieszKernel
    (show (1 : ℂ) ∈ sphere (0 : ℂ) 1 by simp) hwlt
  simp only [sub_zero] at hk
  rw [positiveCayley_inverse (positiveCayley_denominator_ne (hre z hz))] at hk
  apply le_trans _ hk
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

#print axioms schwarz_quadratic
#print axioms positive_real_quadratic_lower_bound

end
end ExteriorReduction
