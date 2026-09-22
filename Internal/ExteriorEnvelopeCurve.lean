import ExteriorEnvelopeAngle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! The upper Cauchy perimeter inequality needed for exterior circles.
Only an upper support estimate and a nondecreasing tangent lift are used. -/

namespace ExteriorReduction.ExteriorEnvelope

open Complex Metric Set Filter MeasureTheory
open scoped Topology

noncomputable section

def rotatingProjection (γ : ℝ → ℂ) (θ : ℝ → ℝ) (t : ℝ) : ℂ :=
  γ t * Complex.exp (-((θ t : ℂ) * I))

theorem rotatingProjection_im_hasDerivAt {γ : ℝ → ℂ} {θ : ℝ → ℝ}
    {v a t : ℝ}
    (hγ : HasDerivAt γ (I * (v : ℂ) * Complex.exp ((θ t : ℂ) * I)) t)
    (hθ : HasDerivAt θ a t) :
    HasDerivAt (fun s => (rotatingProjection γ θ s).im)
      (v - a * (rotatingProjection γ θ t).re) t := by
  have he := ((hθ.ofReal_comp.mul_const I).neg).cexp
  have hp := hγ.mul he
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hp
  have hc : I * (v : ℂ) * Complex.exp ((θ t : ℂ) * I) *
      Complex.exp (-((θ t : ℂ) * I)) + γ t *
        (Complex.exp (-((θ t : ℂ) * I)) * -((a : ℂ) * I)) =
      I * (v : ℂ) - (a : ℂ) * rotatingProjection γ θ t * I := by
    rw [mul_assoc (I * (v : ℂ)), ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    simp only [mul_one, rotatingProjection]
    ring
  change HasDerivAt (fun s => (rotatingProjection γ θ s).im)
    (I * (v : ℂ) * Complex.exp ((θ t : ℂ) * I) *
      Complex.exp (-((θ t : ℂ) * I)) + γ t *
        (Complex.exp (-((θ t : ℂ) * I)) * -((a : ℂ) * I))).im t at hi
  rw [hc] at hi
  simpa only [Complex.sub_im, Complex.I_mul_im, Complex.ofReal_re,
    Complex.mul_I_im, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero] using hi

theorem rotatingProjection_im_integral {γ : ℝ → ℂ} {θ v a : ℝ → ℝ} {T : ℝ}
    (hγ : ∀ t, HasDerivAt γ (I * (v t : ℂ) * Complex.exp ((θ t : ℂ) * I)) t)
    (hθ : ∀ t, HasDerivAt θ (a t) t)
    (hv : Continuous v) (ha : Continuous a)
    (hperiod : rotatingProjection γ θ T = rotatingProjection γ θ 0) :
    (∫ t in (0 : ℝ)..T, v t) =
      ∫ t in (0 : ℝ)..T, (rotatingProjection γ θ t).re * a t := by
  have hγc : Continuous γ := continuous_iff_continuousAt.mpr
    (fun t => (hγ t).continuousAt)
  have hθc : Continuous θ := continuous_iff_continuousAt.mpr
    (fun t => (hθ t).continuousAt)
  have hp : Continuous (fun t => (rotatingProjection γ θ t).re) := by
    unfold rotatingProjection
    fun_prop
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ uIcc 0 T) => rotatingProjection_im_hasDerivAt (hγ t) (hθ t))
    ((hv.sub (ha.mul hp)).intervalIntegrable 0 T)
  rw [hperiod, sub_self] at hh
  rw [intervalIntegral.integral_sub (f := v)
    (g := fun t => a t * (rotatingProjection γ θ t).re)
    (hv.intervalIntegrable 0 T) ((ha.mul hp).intervalIntegrable 0 T)] at hh
  have hzero := sub_eq_zero.mp hh
  simpa only [mul_comm] using hzero

theorem curve_length_le_support_integral {γ : ℝ → ℂ} {θ v a S : ℝ → ℝ}
    {T ε : ℝ} (hT : 0 ≤ T)
    (hγ : ∀ t, HasDerivAt γ (I * (v t : ℂ) * Complex.exp ((θ t : ℂ) * I)) t)
    (hθ : ∀ t, HasDerivAt θ (a t) t)
    (hv : Continuous v) (ha : Continuous a)
    (hperiod : rotatingProjection γ θ T = rotatingProjection γ θ 0)
    (hθperiod : θ T = θ 0 + T)
    (hS : Continuous S) (hSperiod : Function.Periodic S T)
    (ha0 : ∀ t ∈ Icc 0 T, 0 ≤ a t)
    (hbound : ∀ t ∈ Icc 0 T, (rotatingProjection γ θ t).re ≤ S (θ t) + ε) :
    (∫ t in (0 : ℝ)..T, v t) ≤ (∫ t in (0 : ℝ)..T, S t) + T * ε := by
  have hγc : Continuous γ := continuous_iff_continuousAt.mpr
    (fun t => (hγ t).continuousAt)
  have hθc : Continuous θ := continuous_iff_continuousAt.mpr
    (fun t => (hθ t).continuousAt)
  have hp : Continuous (fun t => (rotatingProjection γ θ t).re) := by
    unfold rotatingProjection
    fun_prop
  rw [rotatingProjection_im_integral hγ hθ hv ha hperiod]
  calc
    _ ≤ ∫ t in (0 : ℝ)..T, (S (θ t) + ε) * a t :=
      intervalIntegral.integral_mono_on hT ((hp.mul ha).intervalIntegrable 0 T)
        (((hS.comp hθc).add_const ε).mul ha |>.intervalIntegrable 0 T)
        (fun t ht => mul_le_mul_of_nonneg_right (hbound t ht) (ha0 t ht))
    _ = (∫ t in (0 : ℝ)..T, S t) + T * ε := by
      have hsub := intervalIntegral.integral_comp_mul_deriv
        (fun t (_ : t ∈ uIcc 0 T) => hθ t) ha.continuousOn (hS.add_const ε)
      change (∫ t in (0 : ℝ)..T, (S (θ t) + ε) * a t) = _ at hsub
      rw [hsub, hθperiod]
      have hsp : Function.Periodic (fun t => S t + ε) T := fun t => by
        change S (t + T) + ε = S t + ε
        rw [hSperiod t]
      rw [hsp.intervalIntegral_add_eq (θ 0) 0]
      simp only [zero_add]
      rw [intervalIntegral.integral_add (hS.intervalIntegrable 0 T)
        (continuous_const.intervalIntegrable 0 T), intervalIntegral.integral_const]
      simp

#print axioms curve_length_le_support_integral

end
end ExteriorReduction.ExteriorEnvelope
