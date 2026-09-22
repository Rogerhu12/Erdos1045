import ExteriorEnvelopeCurve
import BoundaryPolygonLength
import ExteriorEnvelopeModel
import RadialEnergy
import Erdos1045.ClosedHullSupport

/-! The actual exterior circle has a globally defined continuous normal angle.
Its angular derivative is precisely the analytic convexity criterion. -/

namespace ExteriorReduction.ExteriorEnvelope

open Complex Metric Set Filter MeasureTheory
open Erdos1045.ExteriorBoundary Erdos1045.HullGeometry
open scoped Topology

noncomputable section

theorem exp_eq_norm_mul_exp_im (z : ℂ) :
    Complex.exp z = (‖Complex.exp z‖ : ℂ) * Complex.exp ((z.im : ℂ) * I) := by
  rw [Complex.norm_exp, Complex.ofReal_exp, ← Complex.exp_add, Complex.re_add_im]

theorem inverseCircle_eq_inv {r : ℝ} (t : ℝ) :
    inverseCircle r⁻¹ (t : ℂ) = ((r : ℂ) * unit t)⁻¹ := by
  simp only [inverseCircle, unit, Complex.ofReal_inv, mul_inv_rev, Complex.exp_neg]
  ring

theorem inverseCircle_periodic (ρ : ℝ) :
    Function.Periodic (fun t : ℝ => inverseCircle ρ (t : ℂ)) (2 * Real.pi) := by
  intro t
  simp only [inverseCircle, Complex.ofReal_add, add_mul, neg_add, Complex.exp_add]
  have he : Complex.exp (-(((2 * Real.pi : ℝ) : ℂ) * I)) = 1 := by
    rw [Complex.exp_neg]
    push_cast
    rw [Complex.exp_two_pi_mul_I, inv_one]
  rw [he, mul_one]

theorem normalAngle_period (L : ℂ → ℂ) (ρ t : ℝ) :
    normalAngle L ρ (t + 2 * Real.pi) = normalAngle L ρ t + 2 * Real.pi := by
  unfold normalAngle
  have he : inverseCircle ρ ((t + 2 * Real.pi : ℝ) : ℂ) =
      inverseCircle ρ (t : ℂ) := inverseCircle_periodic ρ t
  rw [he]
  ring

theorem rotatingProjection_period_two_pi {γ : ℝ → ℂ} {θ : ℝ → ℝ}
    (hγ : γ (2 * Real.pi) = γ 0) (hθ : θ (2 * Real.pi) = θ 0 + 2 * Real.pi) :
    rotatingProjection γ θ (2 * Real.pi) = rotatingProjection γ θ 0 := by
  simp only [rotatingProjection, hγ, hθ, Complex.ofReal_add, add_mul, neg_add,
    Complex.exp_add]
  have he : Complex.exp (-(((2 * Real.pi : ℝ) : ℂ) * I)) = 1 := by
    rw [Complex.exp_neg]
    push_cast
    rw [Complex.exp_two_pi_mul_I, inv_one]
  rw [he, mul_one]

theorem model_circle_tangent {q L : ℂ → ℂ} {A : ℂ} {c r : ℝ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (hq0 : q 0 = (c : ℂ))
    (hc : 0 < c) (hr : 1 < r)
    (hLexp : ∀ z ∈ ball (0 : ℂ) 1, Complex.exp (L z) = modelDerivative q z)
    (t : ℝ) :
    HasDerivAt (fun s : ℝ => exteriorFromModel q A ((r : ℂ) * unit s))
      (I * (r * c * ‖modelDerivative q (inverseCircle r⁻¹ (t : ℂ))‖ : ℝ) *
        Complex.exp ((normalAngle L r⁻¹ t : ℂ) * I)) t := by
  have hqne : q 0 ≠ 0 := by rw [hq0]; exact_mod_cast hc.ne'
  have hw := exterior_circle_mem hr t
  have hΨ : DifferentiableOn ℂ (exteriorFromModel q A) exteriorDisk :=
    fun w hw => (exteriorFromModel_hasDerivAt hq A hw).differentiableAt.differentiableWithinAt
  have hh := exterior_circle_hasDerivAt hΨ hr t
  rw [exteriorFromModel_normalized_deriv hq hqne A hw, hq0, ← inverseCircle_eq_inv] at hh
  have hz := inverseCircle_mem_disk (le_of_lt (inv_pos.mpr (lt_trans zero_lt_one hr)))
    (inv_lt_one_of_one_lt₀ hr) t
  have he := exp_eq_norm_mul_exp_im (L (inverseCircle r⁻¹ (t : ℂ)))
  rw [hLexp _ hz] at he
  rw [he] at hh
  convert hh using 1
  simp only [normalAngle, Complex.ofReal_add, add_mul, Complex.exp_add,
    Complex.ofReal_mul, unit]
  ring

theorem model_circle_length_le_support {q : ℂ → ℂ} {A : ℂ} {c r ε : ℝ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (hq0 : q 0 = (c : ℂ))
    (hc : 0 < c)
    (hDne : ∀ z ∈ ball (0 : ℂ) 1, modelDerivative q z ≠ 0)
    (hcrit : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ (derivativeCriterion (modelDerivative q) z).re)
    (hr : 1 < r) {S : ℝ → ℝ} (hS : Continuous S)
    (hSperiod : Function.Periodic S (2 * Real.pi))
    (hbound : ∀ t θ : ℝ, (exteriorFromModel q A ((r : ℂ) * unit t) *
      Complex.exp (-((θ : ℂ) * I))).re ≤ S θ + ε) :
    exteriorCircleLength (exteriorFromModel q A) r ≤
      (∫ t in (0 : ℝ)..(2 * Real.pi), S t) + 2 * Real.pi * ε := by
  have hqne : q 0 ≠ 0 := by rw [hq0]; exact_mod_cast hc.ne'
  have hD := modelDerivative_analytic hq hqne
  obtain ⟨L, _, hLexp, hLderiv⟩ := exists_analytic_log_on_disk hD hDne
  let γ : ℝ → ℂ := fun t => exteriorFromModel q A ((r : ℂ) * unit t)
  let θ : ℝ → ℝ := normalAngle L r⁻¹
  let v : ℝ → ℝ := fun t => r * c * ‖modelDerivative q (inverseCircle r⁻¹ (t : ℂ))‖
  let a : ℝ → ℝ := fun t => (derivativeCriterion (modelDerivative q)
    (inverseCircle r⁻¹ (t : ℂ))).re
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hz (t : ℝ) : inverseCircle r⁻¹ (t : ℂ) ∈ ball (0 : ℂ) 1 :=
    inverseCircle_mem_disk (inv_pos.mpr hr0).le (inv_lt_one_of_one_lt₀ hr) t
  have hzc : Continuous (fun t : ℝ => inverseCircle r⁻¹ (t : ℂ)) := by
    unfold inverseCircle
    fun_prop
  have hγ (t : ℝ) : HasDerivAt γ (I * (v t : ℂ) * Complex.exp ((θ t : ℂ) * I)) t :=
    model_circle_tangent hq hq0 hc hr hLexp t
  have hθ (t : ℝ) : HasDerivAt θ (a t) t :=
    normalAngle_hasDerivAt hLderiv (inv_pos.mpr hr0).le (inv_lt_one_of_one_lt₀ hr) t
  have hv : Continuous v :=
    (hD.continuousOn.comp_continuous hzc hz).norm.const_mul _
  have ha : Continuous a := Complex.continuous_re.comp
    ((analytic_derivativeCriterion hD hDne).continuousOn.comp_continuous hzc hz)
  have hγperiod : γ (2 * Real.pi) = γ 0 := by
    dsimp [γ]
    rw [show unit (2 * Real.pi) = unit 0 by simpa using unit_two_pi_periodic 0]
  have hθperiod : θ (2 * Real.pi) = θ 0 + 2 * Real.pi := by
    simpa only [zero_add] using normalAngle_period L r⁻¹ 0
  have hlen : exteriorCircleLength (exteriorFromModel q A) r = ∫ t in (0 : ℝ)..(2 * Real.pi), v t := by
    unfold exteriorCircleLength
    apply intervalIntegral.integral_congr
    intro t _
    change ‖deriv (exteriorFromModel q A) ((r : ℂ) * unit t)‖ * r = v t
    rw [exteriorFromModel_normalized_deriv hq hqne A (exterior_circle_mem hr t),
      hq0, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc,
      ← inverseCircle_eq_inv]
    dsimp [v]
    ring
  rw [hlen]
  exact curve_length_le_support_integral (by positivity) hγ hθ hv ha
    (rotatingProjection_period_two_pi hγperiod hθperiod) hθperiod hS hSperiod
    (fun t _ => hcrit _ (hz t)) (fun t _ => hbound t (θ t))

#print axioms model_circle_tangent
#print axioms model_circle_length_le_support

end
end ExteriorReduction.ExteriorEnvelope
