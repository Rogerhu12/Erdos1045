import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# A square-root-free capacity-energy estimate

This independent pilot proves the scalar and integral part of a replacement
for the boundary square-root argument. It does not construct an exterior map,
prove the concavity criterion, or pass from radial circles to the boundary.
All hypotheses below are explicit ordinary hypotheses, not new axioms.
-/

namespace ExteriorReduction

open MeasureTheory Set

noncomputable section

private def gap (B x : ℝ) : ℝ :=
  2 * (B + 1) * (x - 1 - Real.log x) - (x ^ 2 - 1 - 2 * Real.log x)

private theorem gap_deriv (B : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (gap B) (2 * (x - 1) * (B - x) / x) x := by
  have h := (((hasDerivAt_id x).sub_const 1).sub
    (Real.hasDerivAt_log hx.ne')).const_mul (2 * (B + 1))
  have h' := (((hasDerivAt_id x).pow 2).sub_const 1).sub
    ((Real.hasDerivAt_log hx.ne').const_mul 2)
  convert h.sub h' using 1 <;> try rfl
  simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  field_simp
  ring

/-- A bound with the sharp limiting coefficient 4 as B tends to 1. -/
theorem scalar_log_moment_bound {x B : ℝ} (hx : 0 < x) (hB : 1 ≤ B)
    (hxB : x ≤ B) :
    x ^ 2 - 1 - 2 * Real.log x ≤
      2 * (B + 1) * (x - 1 - Real.log x) := by
  have hzero : gap B 1 = 0 := by simp [gap]
  have hcont {a b : ℝ} (ha : 0 < a) : ContinuousOn (gap B) (Icc a b) := by
    intro y hy
    exact (gap_deriv B (ha.trans_le hy.1)).continuousAt.continuousWithinAt
  have hdiff {a b : ℝ} (ha : 0 < a) :
      DifferentiableOn ℝ (gap B) (interior (Icc a b)) := by
    intro y hy
    exact (gap_deriv B (ha.trans_le (interior_subset hy).1)).differentiableAt.differentiableWithinAt
  have hg : 0 ≤ gap B x := by
    by_cases hx1 : x ≤ 1
    · have hm : AntitoneOn (gap B) (Icc x 1) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc x 1) (hcont hx) (hdiff hx)
        intro y hy
        have hy' := interior_subset hy
        have hyp : 0 < y := hx.trans_le hy'.1
        rw [(gap_deriv B hyp).deriv]
        apply div_nonpos_of_nonpos_of_nonneg _ hyp.le
        exact mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (sub_nonpos.mpr hy'.2))
          (sub_nonneg.mpr (hy'.2.trans hB))
      have := hm ⟨le_rfl, hx1⟩ ⟨hx1, le_rfl⟩ hx1
      simpa [hzero] using this
    · have h1x : 1 ≤ x := le_of_lt (lt_of_not_ge hx1)
      have hm : MonotoneOn (gap B) (Icc 1 B) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc 1 B)
          (hcont (by norm_num : (0 : ℝ) < 1)) (hdiff (by norm_num : (0 : ℝ) < 1))
        intro y hy
        have hy' := interior_subset hy
        have hyp : 0 < y := lt_of_lt_of_le (by norm_num) hy'.1
        rw [(gap_deriv B hyp).deriv]
        exact div_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hy'.1))
            (sub_nonneg.mpr hy'.2)) hyp.le
      have := hm ⟨le_rfl, hB⟩ ⟨h1x, hxB⟩ h1x
      simpa [hzero] using this
  dsimp [gap] at hg
  linarith

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

/-- Positive data of geometric mean 1: second moment from first moment. -/
theorem integral_moment_bound (X : α → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hX : ∀ᵐ t ∂μ, 0 < X t ∧ X t ≤ B)
    (h1 : Integrable X μ) (h2 : Integrable (fun t => X t ^ 2) μ)
    (hlog : Integrable (fun t => Real.log (X t)) μ)
    (hmean : (∫ t, Real.log (X t) ∂μ) = 0) :
    (∫ t, X t ^ 2 ∂μ) - 1 ≤ 2 * (B + 1) * ((∫ t, X t ∂μ) - 1) := by
  have hi := integral_mono_ae
    ((h2.sub (integrable_const 1)).sub (hlog.const_mul 2))
    (((h1.sub (integrable_const 1)).sub hlog).const_mul (2 * (B + 1)))
    (hX.mono fun t ht => scalar_log_moment_bound ht.1 hB ht.2)
  change (∫ t, X t ^ 2 - 1 - 2 * Real.log (X t) ∂μ) ≤
    (∫ t, 2 * (B + 1) * (X t - 1 - Real.log (X t)) ∂μ) at hi
  rw [integral_sub (f := fun t => X t ^ 2 - 1) (g := fun t => 2 * Real.log (X t))
      (h2.sub (integrable_const 1)) (hlog.const_mul 2),
    integral_sub (f := fun t => X t ^ 2) (g := fun _ => (1 : ℝ)) h2 (integrable_const 1),
    integral_const_mul, integral_const_mul,
    integral_sub (f := fun t => X t - 1) (g := fun t => Real.log (X t))
      (h1.sub (integrable_const 1)) hlog,
    integral_sub (f := X) (g := fun _ => (1 : ℝ)) h1 (integrable_const 1)] at hi
  simpa [hmean] using hi

/-- Complex mean 1 turns the same estimate into an L2 distance estimate. -/
theorem complex_energy_bound (F : α → ℂ) {B : ℝ} (hB : 1 ≤ B)
    (hF : ∀ᵐ t ∂μ, F t ≠ 0 ∧ ‖F t‖ ≤ B)
    (h1 : Integrable (fun t => ‖F t‖) μ)
    (h2 : Integrable (fun t => ‖F t‖ ^ 2) μ)
    (hre : Integrable (fun t => (F t).re) μ)
    (hlog : Integrable (fun t => Real.log ‖F t‖) μ)
    (hmean : (∫ t, (F t).re ∂μ) = 1)
    (hlogmean : (∫ t, Real.log ‖F t‖ ∂μ) = 0) :
    (∫ t, ‖F t - 1‖ ^ 2 ∂μ) ≤
      2 * (B + 1) * ((∫ t, ‖F t‖ ∂μ) - 1) := by
  have hs (z : ℂ) : ‖z - 1‖ ^ 2 = ‖z‖ ^ 2 - 2 * z.re + 1 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  have hid : (∫ t, ‖F t - 1‖ ^ 2 ∂μ) = (∫ t, ‖F t‖ ^ 2 ∂μ) - 1 := by
    simp_rw [hs]
    rw [integral_add (f := fun t => ‖F t‖ ^ 2 - 2 * (F t).re)
        (g := fun _ => (1 : ℝ)) (h2.sub (hre.const_mul 2)) (integrable_const 1),
      integral_sub (f := fun t => ‖F t‖ ^ 2) (g := fun t => 2 * (F t).re)
        h2 (hre.const_mul 2), integral_const_mul, hmean]
    simp
    ring
  rw [hid]
  exact integral_moment_bound (fun t => ‖F t‖) hB
    (hF.mono fun t ht => ⟨norm_pos_iff.mpr ht.1, ht.2⟩) h1 h2 hlog hlogmean

/-- The normalized radial length is L = c times the mean modulus.
This form yields 12*pi*c*(1-c) for B=2 and tends to 8*pi*c*(1-c)
as B tends to 1, after the geometric radial limit L tends to 1. -/
theorem scaled_energy_bound (F : α → ℂ) {B c L : ℝ} (hB : 1 ≤ B)
    (hF : ∀ᵐ t ∂μ, F t ≠ 0 ∧ ‖F t‖ ≤ B)
    (h1 : Integrable (fun t => ‖F t‖) μ)
    (h2 : Integrable (fun t => ‖F t‖ ^ 2) μ)
    (hre : Integrable (fun t => (F t).re) μ)
    (hlog : Integrable (fun t => Real.log ‖F t‖) μ)
    (hmean : (∫ t, (F t).re ∂μ) = 1)
    (hlogmean : (∫ t, Real.log ‖F t‖ ∂μ) = 0)
    (hlength : L = c * (∫ t, ‖F t‖ ∂μ)) :
    2 * Real.pi * c ^ 2 * (∫ t, ‖F t - 1‖ ^ 2 ∂μ) ≤
      4 * Real.pi * c * (B + 1) * (L - c) := by
  have h := mul_le_mul_of_nonneg_left
    (complex_energy_bound F hB hF h1 h2 hre hlog hmean hlogmean)
    (show 0 ≤ 2 * Real.pi * c ^ 2 by positivity)
  calc
    _ ≤ 2 * Real.pi * c ^ 2 *
        (2 * (B + 1) * ((∫ t, ‖F t‖ ∂μ) - 1)) := h
    _ = 4 * Real.pi * c * (B + 1) * (L - c) := by rw [hlength]; ring

/-- The existing library supplies the logarithmic mean on every interior circle.
No boundary logarithm or square root is being assumed. -/
theorem analytic_log_mean_zero {F : ℂ → ℂ} {r : ℝ}
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall 0 |r|))
    (hne : ∀ z ∈ Metric.closedBall 0 |r|, F z ≠ 0) (hzero : F 0 = 1) :
    Real.circleAverage (fun z => Real.log ‖F z‖) 0 r = 0 := by
  rw [hF.circleAverage_log_norm_of_ne_zero hne, hzero]
  simp

#print axioms scalar_log_moment_bound
#print axioms integral_moment_bound
#print axioms complex_energy_bound
#print axioms scaled_energy_bound
#print axioms analytic_log_mean_zero

end
end ExteriorReduction
