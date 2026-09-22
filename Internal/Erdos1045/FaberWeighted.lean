import Erdos1045.FaberFourier
import Erdos1045.FaberRadial

namespace Erdos1045.FaberFourier

open scoped BigOperators
open Erdos1045.FaberSampling
noncomputable section

/-- The actual weighted coefficient estimate (4.4), including convergence
of its infinite series. The constant is explicit and independent of `n`. -/
theorem weighted_coefficient_estimate (facts : ClassicalFourierFacts)
    (classicalMoment : ClassicalGeometricMoment)
    {n : ℕ} (hn : 0 < n) {τ c C : ℝ} (hτ : 0 < τ) (hc : 0 < c) (hC : 0 ≤ C)
    (a : ℕ → ℂ) (θ : Fin n → ℝ) (hsampling : H1Sampling θ C)
    (ha : Summable (fun m : ℕ => (1 + (m : ℝ) ^ 2) * ‖a m‖ ^ 2)) :
    Summable (fun k => ((k + 1 : ℕ) : ℝ) ^ 2 * radialWeight n τ (k + 1) *
      (∑ j, ‖coefficient c a θ j (k + 1)‖ ^ 2)) ∧
    (∑' k, ((k + 1 : ℕ) : ℝ) ^ 2 * radialWeight n τ (k + 1) *
      (∑ j, ‖coefficient c a θ j (k + 1)‖ ^ 2)) ≤
      (2 * Real.pi * C / c ^ 2) * (2 * radialConstant τ * (n : ℝ) ^ 2 *
        (∑' m : ℕ, (m : ℝ) ^ 2 * ‖a m‖ ^ 2)) := by
  apply weighted_sample_bound hn (fun _ => radialWeight_nonneg hn hτ)
    (fun _ => radialWeight_le_one hn hτ) (le_max_left _ _)
    (radial_moment_bound classicalMoment hn hτ)
    (fun m => sq_nonneg _) (fun k => Finset.sum_nonneg fun j _ => sq_nonneg _)
    (coefficient_energies_summable ha).2
  · positivity
  · exact coefficient_sampling_kernel facts hn hc hC a θ hsampling ha

end

end Erdos1045.FaberFourier
