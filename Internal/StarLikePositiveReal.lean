import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Convex.Star
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

/-! # The positive-real-part criterion for a holomorphic star-like image

Only ordinary holomorphic maps and a holomorphic left inverse on an open
star-like target are used. No exterior map or convex-set inversion is asserted.
-/

namespace ExteriorReduction.StarLike

open Set Metric Filter Complex
open scoped Topology ComplexConjugate
noncomputable section

theorem left_max_derivative_nonneg {f : ℝ → ℝ} {v : ℝ}
    (hf : HasDerivAt f v 1) (hmax : ∀ s ∈ Icc (0 : ℝ) 1, f s ≤ f 1) : 0 ≤ v := by
  apply ge_of_tendsto (hf.tendsto_slope.mono_left (nhdsLT_le_nhdsNE 1))
  have hp : ∀ᶠ s : ℝ in nhdsWithin 1 (Iio 1), 0 < s :=
    nhdsWithin_le_nhds (Ioi_mem_nhds zero_lt_one)
  filter_upwards [hp, self_mem_nhdsWithin] with s hs hs1
  rw [slope_def_field]
  exact div_nonneg_of_nonpos (sub_nonpos.mpr (hmax s ⟨hs.le, hs1.le⟩))
    (sub_nonpos.mpr hs1.le)

theorem radial_inverse_norm_le {g G : ℂ → ℂ} {Ω : Set ℂ}
    (hg : DifferentiableOn ℂ g (ball 0 1)) (hG : DifferentiableOn ℂ G Ω)
    (hgmap : MapsTo g (ball 0 1) Ω) (hGmap : MapsTo G Ω (ball 0 1))
    (hleft : ∀ z ∈ ball (0 : ℂ) 1, G (g z) = z)
    (hzero : g 0 = 0) (hstar : StarConvex ℝ 0 Ω)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {z : ℂ} (hz : z ∈ ball 0 1) :
    ‖G ((s : ℂ) * g z)‖ ≤ ‖z‖ := by
  have hsmap : MapsTo (fun w => (s : ℂ) * g w) (ball 0 1) Ω := by
    intro w hw
    simpa only [Complex.real_smul] using hstar.smul_mem (hgmap hw) hs0 hs1
  have hdiff : DifferentiableOn ℂ (fun w => G ((s : ℂ) * g w)) (ball 0 1) :=
    hG.comp (hg.const_mul _) hsmap
  have hmap : MapsTo (fun w => G ((s : ℂ) * g w)) (ball 0 1) (closedBall 0 1) :=
    fun w hw => ball_subset_closedBall (hGmap (hsmap hw))
  have hfix : G ((s : ℂ) * g 0) = 0 := by
    have h := hleft 0 (by simp)
    simpa only [hzero, mul_zero] using h
  exact Complex.norm_le_norm_of_mapsTo_ball hdiff hmap hfix (mem_ball_zero_iff.mp hz)

theorem inverse_derivative_identity {g G : ℂ → ℂ} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g (ball 0 1))
    (hG : DifferentiableOn ℂ G Ω) (hgmap : MapsTo g (ball 0 1) Ω)
    (hleft : ∀ z ∈ ball (0 : ℂ) 1, G (g z) = z)
    {z : ℂ} (hz : z ∈ ball 0 1) : deriv G (g z) * deriv g z = 1 := by
  have hd := (hG.differentiableAt (hΩ.mem_nhds (hgmap hz))).hasDerivAt.comp z
    (hg.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have heq : (fun w : ℂ => w) =ᶠ[nhds z] (fun w => G (g w)) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact (hleft w hw).symm
  exact (hd.congr_of_eventuallyEq heq).unique (hasDerivAt_id z)

theorem derivative_ne_zero {g G : ℂ → ℂ} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g (ball 0 1))
    (hG : DifferentiableOn ℂ G Ω) (hgmap : MapsTo g (ball 0 1) Ω)
    (hleft : ∀ z ∈ ball (0 : ℂ) 1, G (g z) = z)
    {z : ℂ} (hz : z ∈ ball 0 1) : deriv g z ≠ 0 := by
  intro hbad
  have h := inverse_derivative_identity hΩ hg hG hgmap hleft hz
  simp [hbad] at h

theorem value_ne_zero {g G : ℂ → ℂ}
    (hleft : ∀ z ∈ ball (0 : ℂ) 1, G (g z) = z) (hzero : g 0 = 0)
    {z : ℂ} (hz : z ∈ ball 0 1) (hz0 : z ≠ 0) : g z ≠ 0 := by
  intro hbad
  have h := hleft z hz
  have h0 := hleft 0 (by simp)
  rw [hzero] at h0
  rw [hbad, h0] at h
  exact hz0 h.symm

theorem radial_inverse_inner_nonneg {g G : ℂ → ℂ} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g (ball 0 1))
    (hG : DifferentiableOn ℂ G Ω)
    (hgmap : MapsTo g (ball 0 1) Ω) (hGmap : MapsTo G Ω (ball 0 1))
    (hleft : ∀ z ∈ ball (0 : ℂ) 1, G (g z) = z)
    (hzero : g 0 = 0) (hstar : StarConvex ℝ 0 Ω)
    {z : ℂ} (hz : z ∈ ball 0 1) :
    0 ≤ (conj z * (deriv G (g z) * g z)).re := by
  have hGc := (hG.differentiableAt (hΩ.mem_nhds (hgmap hz))).hasDerivAt
  have hc : HasDerivAt (fun w : ℂ => G (w * g z)) (deriv G (g z) * g z) 1 := by
    have hGc' : HasDerivAt G (deriv G (g z)) ((1 : ℂ) * g z) := by
      simpa only [one_mul] using hGc
    convert! hGc'.comp (1 : ℂ) ((hasDerivAt_id (1 : ℂ)).mul_const (g z)) using 1
    simp
  have hr : HasDerivAt (fun s : ℝ => G ((s : ℂ) * g z))
      (deriv G (g z) * g z) 1 := hc.comp_ofReal
  have hsq := hr.norm_sq
  have hmax : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖G ((s : ℂ) * g z)‖ ^ 2 ≤ ‖G ((1 : ℝ) * g z)‖ ^ 2 := by
    intro s hs
    simp only [Complex.ofReal_one, one_mul, hleft z hz]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (radial_inverse_norm_le hg hG hgmap hGmap hleft hzero hstar hs.1 hs.2 hz) 2
  have hnonneg := left_max_derivative_nonneg hsq hmax
  simp only [Complex.ofReal_one, one_mul, hleft z hz,
    real_inner_eq_re_inner ℂ, RCLike.inner_apply'] at hnonneg
  change 0 ≤ 2 * (conj z * (deriv G (g z) * g z)).re at hnonneg
  linarith

/-- The reciprocal form follows directly from the left radial derivative. -/
theorem reciprocal_log_derivative_re_nonneg {g G : ℂ → ℂ} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g (ball 0 1))
    (hG : DifferentiableOn ℂ G Ω)
    (hgmap : MapsTo g (ball 0 1) Ω) (hGmap : MapsTo G Ω (ball 0 1))
    (hleft : ∀ z ∈ ball (0 : ℂ) 1, G (g z) = z)
    (hzero : g 0 = 0) (hstar : StarConvex ℝ 0 Ω)
    {z : ℂ} (hz : z ∈ ball 0 1) (hz0 : z ≠ 0) :
    0 ≤ (g z / (z * deriv g z)).re := by
  have hi := radial_inverse_inner_nonneg hΩ hg hG hgmap hGmap hleft hzero hstar hz
  have hdiv : 0 ≤ ((deriv G (g z) * g z) / z).re := by
    rw [Complex.div_re, ← add_div]
    apply div_nonneg _ (Complex.normSq_nonneg z)
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im] at hi ⊢
    nlinarith
  have hdne := derivative_ne_zero hΩ hg hG hgmap hleft hz
  have hdi : deriv G (g z) = 1 / deriv g z :=
    (eq_div_iff hdne).mpr (inverse_derivative_identity hΩ hg hG hgmap hleft hz)
  rw [hdi] at hdiv
  convert hdiv using 1
  congr 1
  field_simp

/-- The star-like analytic criterion. Derivative nonvanishing is obtained
from the holomorphic inverse and is not a separate hypothesis. -/
theorem log_derivative_re_nonneg {g G : ℂ → ℂ} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g (ball 0 1))
    (hG : DifferentiableOn ℂ G Ω)
    (hgmap : MapsTo g (ball 0 1) Ω) (hGmap : MapsTo G Ω (ball 0 1))
    (hleft : ∀ z ∈ ball (0 : ℂ) 1, G (g z) = z)
    (hzero : g 0 = 0) (hstar : StarConvex ℝ 0 Ω)
    {z : ℂ} (hz : z ∈ ball 0 1) (hz0 : z ≠ 0) :
    0 ≤ (z * deriv g z / g z).re := by
  have h := reciprocal_log_derivative_re_nonneg hΩ hg hG hgmap hGmap hleft hzero hstar hz hz0
  have hi : 0 ≤ (g z / (z * deriv g z))⁻¹.re := by
    rw [Complex.inv_re]
    exact div_nonneg h (Complex.normSq_nonneg _)
  simpa only [inv_div] using hi

end
end ExteriorReduction.StarLike
