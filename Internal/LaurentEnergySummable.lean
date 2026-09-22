import RadialParseval
import LaurentDerivativeSeries
import EnergyFromCriterion
import Erdos1045.ClosedLaurent

/-! Bounded analytic derivatives give the actual Laurent H1 coefficients.
This preliminary summability needs no perimeter limit or boundary extension. -/

namespace ExteriorReduction

open Complex Metric Set Filter
open FaberKernel
open scoped Topology BigOperators
noncomputable section

theorem summable_of_uniform_radial_bound {a : ℕ → ℝ} {B : ℝ}
    (ha : ∀ n, 0 ≤ a n)
    (hs : ∀ r : ℝ, 0 ≤ r → r < 1 → Summable (fun n => a n * r ^ (2 * n)))
    (hB : ∀ r : ℝ, 0 ≤ r → r < 1 → (∑' n, a n * r ^ (2 * n)) ≤ B) :
    Summable a ∧ (∑' n, a n) ≤ B := by
  have hfin (s : Finset ℕ) : ∑ n ∈ s, a n ≤ B := by
    have hc : Continuous (fun r : ℝ => ∑ n ∈ s, a n * r ^ (2 * n)) := by fun_prop
    have ht : Tendsto (fun r : ℝ => ∑ n ∈ s, a n * r ^ (2 * n))
        (𝓝[<] (1 : ℝ)) (𝓝 (∑ n ∈ s, a n)) := by
      simpa only [one_pow, mul_one] using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
    apply le_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with r hr hr0
    exact ((hs r hr0.le hr).sum_le_tsum s
      (fun n _ => mul_nonneg (ha n) (pow_nonneg hr0.le _))).trans (hB r hr0.le hr)
  exact ⟨summable_of_sum_le ha hfin, Real.tsum_le_of_sum_le ha hfin⟩

theorem bounded_analytic_taylor_square_summable {q : ℂ → ℂ} {B : ℝ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1))
    (hbound : ∀ z ∈ ball (0 : ℂ) 1, ‖q z‖ ≤ B) :
    Summable (fun n => ‖taylorCoefficients q n‖ ^ 2) ∧
      (∑' n, ‖taylorCoefficients q n‖ ^ 2) ≤ B ^ 2 := by
  apply summable_of_uniform_radial_bound (fun _ => sq_nonneg _)
    (fun _ hr0 hr1 => (analytic_circle_parseval hq hr0 hr1).1)
  intro r hr0 hr1
  rw [← (analytic_circle_parseval hq hr0 hr1).2]
  have hsub : sphere (0 : ℂ) |r| ⊆ ball 0 1 := by
    rw [abs_of_nonneg hr0]
    exact sphere_subset_ball hr1
  have hc : ContinuousOn (fun z => ‖q z‖ ^ 2) (sphere 0 |r|) :=
    (hq.continuousOn.mono hsub).norm.pow 2
  have hi := Real.circleAverage_mono (f₁ := fun z => ‖q z‖ ^ 2)
    (f₂ := fun _ => B ^ 2) hc.circleIntegrable'
    (circleIntegrable_const (B ^ 2) 0 r)
    (fun z hz => pow_le_pow_left₀ (norm_nonneg _) (hbound z (hsub hz)) 2)
  simpa only [Real.circleAverage_const, Pi.pow_apply] using hi

theorem weighted_laurent_coefficient_identity {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (hq0 : q 0 ≠ 0) (m : ℕ) :
    (m : ℝ) ^ 2 * ‖modelLaurentCoefficient q m‖ ^ 2 =
      ‖q 0‖ ^ 2 * ‖taylorCoefficients (modelDerivative q) (m + 1)‖ ^ 2 := by
  rw [modelDerivative_taylor_succ hq hq0]
  simp only [norm_div, norm_mul, norm_neg, Complex.norm_natCast, div_pow, mul_pow]
  have hn := norm_ne_zero_iff.mpr hq0
  field_simp

theorem model_laurent_sobolev_of_derivative_bound {q : ℂ → ℂ} {B : ℝ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (hq0 : q 0 ≠ 0)
    (hbound : ∀ z ∈ ball (0 : ℂ) 1, ‖modelDerivative q z‖ ≤ B) :
    Erdos1045.ExteriorClassical.SobolevCoefficients (modelLaurentCoefficient q) := by
  have hs := (bounded_analytic_taylor_square_summable
    (modelDerivative_analytic hq hq0) hbound).1
  have hw : Summable (fun m : ℕ => (m : ℝ) ^ 2 * ‖modelLaurentCoefficient q m‖ ^ 2) := by
    have hshift := hs.comp_injective (i := fun m : ℕ => m + 1)
      (fun _ _ h => Nat.add_right_cancel h)
    apply (hshift.mul_left (‖q 0‖ ^ 2)).congr
    intro m
    exact (weighted_laurent_coefficient_identity hq hq0 m).symm
  have hu : Summable (fun m => ‖modelLaurentCoefficient q m‖ ^ 2) := by
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ hw
    intro m
    by_cases hm : m = 0
    · simp [hm]
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    exact le_mul_of_one_le_left (sq_nonneg _) (by nlinarith : 1 ≤ (m : ℝ) ^ 2)
  refine ⟨modelLaurentCoefficient_zero q, ?_⟩
  convert hu.add hw using 1
  funext m
  ring

theorem model_laurent_sobolev_of_criterion {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (hq0 : q 0 ≠ 0)
    (hne : ∀ z ∈ ball (0 : ℂ) 1, modelDerivative q z ≠ 0)
    (hpos : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ (derivativeCriterion (modelDerivative q) z).re) :
    Erdos1045.ExteriorClassical.SobolevCoefficients (modelLaurentCoefficient q) := by
  exact model_laurent_sobolev_of_derivative_bound hq hq0
    (fun _ hz => normalized_derivative_le_two (modelDerivative_analytic hq hq0) hne
      (modelDerivative_zero hq0) (modelDerivative_hasDerivAt_zero (hq 0 (by simp))).deriv hpos hz)

#print axioms bounded_analytic_taylor_square_summable
#print axioms model_laurent_sobolev_of_criterion

end
end ExteriorReduction
