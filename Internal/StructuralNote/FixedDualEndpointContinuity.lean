import StructuralNote.FixedDualPrimitive
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The primitive has genuine endpoint limits despite the logarithmic singularities of its derivative. -/

namespace StructuralNote.FixedDualPrimitive

open Real Set MeasureTheory Filter
open scoped Topology Interval
noncomputable section

theorem primitive_continuous (b : ℝ) : Continuous (primitive b) := by
  have he : (fun u : ℝ => sin u * log (2 * sin u)) =
      fun u => ((2 * sin u) * log (2 * sin u)) / 2 := by funext u; ring
  have hc : Continuous (fun u : ℝ => sin u * log (2 * sin u)) := by
    rw [he]
    exact (continuous_mul_log.comp (continuous_const.mul continuous_sin)).div_const 2
  unfold primitive
  fun_prop

theorem primitive_reflection (b u : ℝ) :
    primitive b (Real.pi - u) = primitive (-b) u := by
  simp only [primitive, sin_three_mul, cos_three_mul, sin_pi_sub, cos_pi_sub]
  ring

theorem primitive_pi (b : ℝ) : primitive b Real.pi = Real.pi / 2 + b / 3 := by
  have h := primitive_reflection b 0
  rw [sub_zero, primitive_zero] at h
  rw [h]
  ring

theorem primitive_endpoint_limits (b : ℝ) :
    Tendsto (primitive b) (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi / 2 - b / 3)) ∧
      Tendsto (primitive b) (𝓝[<] Real.pi) (𝓝 (Real.pi / 2 + b / 3)) := by
  constructor
  · simpa only [primitive_zero] using (primitive_continuous b).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  · simpa only [primitive_pi] using (primitive_continuous b).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[<] Real.pi ≤ 𝓝 Real.pi)

/-- On a sign interval the actual primitive proves integrability of the singular witness. -/
theorem witness_integral_on_sign_interval (b : ℝ) {a c : ℝ}
    (ha : 0 ≤ a) (hc : c ≤ Real.pi) (hac : a ≤ c)
    (hs : (∀ x ∈ Ioo a c, 0 ≤ witness b x) ∨ (∀ x ∈ Ioo a c, witness b x ≤ 0)) :
    IntervalIntegrable (witness b) volume a c ∧
      (∫ x in a..c, witness b x) = primitive b c - primitive b a := by
  have hd : ∀ x ∈ Ioo a c, HasDerivAt (primitive b) (witness b x) x := by
    intro x hx
    exact primitive_hasDerivAt_on_interval b ⟨lt_of_le_of_lt ha hx.1, lt_of_lt_of_le hx.2 hc⟩
  have hi : IntervalIntegrable (witness b) volume a c := by
    rcases hs with hpos | hneg
    · apply intervalIntegral.intervalIntegrable_deriv_of_nonneg
        ((primitive_continuous b).continuousOn)
      · simpa only [min_eq_left hac, max_eq_right hac] using hd
      · simpa only [min_eq_left hac, max_eq_right hac] using hpos
    · have hi' : IntervalIntegrable (fun x => -witness b x) volume a c := by
        apply intervalIntegral.intervalIntegrable_deriv_of_nonneg
          ((primitive_continuous b).neg.continuousOn)
        · intro x hx
          simp only [min_eq_left hac, max_eq_right hac] at hx
          exact (hd x hx).neg
        · intro x hx
          simp only [min_eq_left hac, max_eq_right hac] at hx
          exact neg_nonneg.mpr (hneg x hx)
      convert hi'.neg using 1
      funext x
      simp only [Pi.neg_apply, neg_neg]
  exact ⟨hi, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hac
    (primitive_continuous b).continuousOn hd hi⟩

end
end StructuralNote.FixedDualPrimitive
