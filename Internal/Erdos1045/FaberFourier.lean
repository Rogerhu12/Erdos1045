import Erdos1045.DirectFourierSampling
import Erdos1045.DirectCircleSampling

/-! # Actual sampled tail coefficients without general Sobolev realization

The circle sampling interface is constructed from interval estimates. Parseval
is proved from finite orthogonality, and application to an infinite analytic
series is proved through smooth finite truncations. No external circle-analysis
assumption remains. -/

namespace Erdos1045.FaberFourier

open MeasureTheory
open scoped BigOperators
noncomputable section

structure ClassicalFourierFacts : Prop where
  /-- Standard disjoint-interval Sobolev sampling on the circle. -/
  sampling : ∀ γ : ℝ, 0 < γ → ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ), 0 < n → ∀ θ : Fin n → ℝ, Separated θ γ → H1Sampling θ C

/-- The former external circle-analysis package is now constructed. Its H1
realization field has been eliminated by the finite-truncation argument. -/
theorem classicalFourierFacts : ClassicalFourierFacts := ⟨circle_sampling_proved⟩

/-- Compatibility theorem: Parseval is proved and is no longer a field of the
classical interface. -/
theorem ClassicalFourierFacts.parseval (_facts : ClassicalFourierFacts)
    (d : ℕ → ℂ) (hd : Summable (fun m => ‖d m‖)) :
    Summable (fun m => ‖d m‖ ^ 2) ∧
    Integrable (fun t => ‖series d t‖ ^ 2) circleMeasure ∧
      energy (series d) = 2 * Real.pi * (∑' m, ‖d m‖ ^ 2) :=
  DirectFourier.parseval d hd

/-- The tail estimate uses sampling only on smooth finite polynomials and
passes to the limit, avoiding any H1 realization assertion. -/
theorem coefficient_sampling (_facts : ClassicalFourierFacts)
    {n : ℕ} (_hn : 0 < n) {c C : ℝ} (hc : 0 < c) (_hC : 0 ≤ C)
    (a : ℕ → ℂ) (θ : Fin n → ℝ) (hsampling : H1Sampling θ C)
    (ha : Summable (fun m : ℕ => (1 + (m : ℝ) ^ 2) * ‖a m‖ ^ 2)) (k : ℕ) :
    (∑ j, ‖coefficient c a θ j k‖ ^ 2) ≤ (2 * Real.pi * C / c ^ 2) *
      ((n : ℝ) * (∑' m, ‖a (m + k)‖ ^ 2) +
        (∑' m : ℕ, (m : ℝ) ^ 2 * ‖a (m + k)‖ ^ 2) / n) :=
  DirectFourier.coefficient_sampling hc a θ hsampling ha k

theorem coefficient_sampling_kernel (facts : ClassicalFourierFacts)
    {n : ℕ} (hn : 0 < n) {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (a : ℕ → ℂ) (θ : Fin n → ℝ) (hsampling : H1Sampling θ C)
    (ha : Summable (fun m : ℕ => (1 + (m : ℝ) ^ 2) * ‖a m‖ ^ 2)) (k : ℕ) :
    (∑ j, ‖coefficient c a θ j (k + 1)‖ ^ 2) ≤ (2 * Real.pi * C / c ^ 2) *
      (∑' m, Erdos1045.FaberSampling.samplingKernel n k m * ‖a m‖ ^ 2) := by
  rw [samplingKernel_tsum_eq_tail n k ha, ← tail_energy_eq n (k + 1) ha]
  exact coefficient_sampling facts hn hc hC a θ hsampling ha (k + 1)

end
end Erdos1045.FaberFourier
