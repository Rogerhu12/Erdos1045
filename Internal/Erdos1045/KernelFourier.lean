import Erdos1045.KernelDiscrete

open scoped BigOperators Topology
open Filter

namespace Erdos1045.KernelWeights

noncomputable section
open CyclicAngles

def circlePowerSum (n : ℕ) (θ : ℕ → ℝ) (k : ℕ) : ℂ :=
  ∑ j ∈ Finset.range n, Complex.exp (-((((k : ℝ) * θ j : ℝ) : ℂ) * Complex.I))

/-- Two standard Fourier identities, stated for arbitrary finite angles and
arbitrary summable coefficient sequences. Neither field refers to the special
weights, circle energy, point separation, an asymptotic estimate, or an extremizer. -/
structure ClassicalCosineFourier : Prop where
  gram : ∀ (n : ℕ) (θ : ℕ → ℝ) (k : ℕ),
    ‖circlePowerSum n θ k‖ ^ 2 =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, Real.cos ((k : ℝ) * (θ i - θ j))
  sampling : ∀ (n : ℕ), 0 < n → ∀ a : ℕ → ℝ, Summable a →
    ((∑ j ∈ Finset.range n, ∑' k, a k * Real.cos ((k : ℝ) * (2 * Real.pi * j / n))) / n) =
      ∑' q, a (q * n)

/-- The manuscript's exact weighted Fourier square sum, with zero weights at
frequencies zero and one. -/
def fourierSquareSum {n : ℕ} (a : Angles n) : ℝ :=
  (∑' k, weight n k * ‖circlePowerSum n (fun i => a.angle i) k‖ ^ 2) / (n : ℝ) ^ 2

theorem fourierSquareSum_eq_angularKernelEnergy (H : ClassicalCosineFourier)
    {n : ℕ} (a : Angles n) (hn : 2 ≤ n) :
    fourierSquareSum a = angularKernelEnergy a := by
  have hterm (i j : ℕ) : Summable (fun k => weight n k * Real.cos ((k : ℝ) * (a.angle i - a.angle j))) :=
    summable_weight_cos hn _
  have houter (i : ℕ) : Summable (fun k => ∑ j ∈ Finset.range n,
      weight n k * Real.cos ((k : ℝ) * (a.angle i - a.angle j))) :=
    summable_sum (fun j _ => hterm i j)
  rw [angularKernelEnergy_pair_form]
  unfold fourierSquareSum
  congr 1
  calc
    (∑' k, weight n k * ‖circlePowerSum n (fun i => a.angle i) k‖ ^ 2) =
        ∑' k, ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          weight n k * Real.cos ((k : ℝ) * (a.angle i - a.angle j)) := by
      apply tsum_congr
      intro k
      rw [H.gram]
      simp_rw [Finset.mul_sum]
    _ = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        kernel n (a.angle i - a.angle j) := by
      rw [Summable.tsum_finsetSum (fun i _ => houter i)]
      apply Finset.sum_congr rfl
      intro i hi
      exact Summable.tsum_finsetSum (fun j _ => hterm i j)

theorem regularGridEnergy_eq_regularEnergy (H : ClassicalCosineFourier)
    {n : ℕ} (hn : 2 ≤ n) : regularGridEnergy n = regularEnergy n := by
  have hs := H.sampling n (by omega) (weight n) (summable_weight hn)
  have hshift : HasSum (fun q : ℕ => weight n ((q + 1) * n)) (regularEnergy n) := by
    simpa only [weight_multiple_eq_regularTerm hn, regularEnergy] using (summable_regularTerm hn).hasSum
  have hfull := (hasSum_nat_add_iff (f := fun q : ℕ => weight n (q * n)) 1).mp hshift
  have heq : (∑' q, weight n (q * n)) = regularEnergy n := by
    simpa using hfull.tsum_eq
  rw [heq] at hs
  exact hs

/-- Section 5.2 for odd sizes tending to infinity. All weight estimates, local
comparison, offset tails, and the regular numerical limit are proved internally.
Only the two universal identities in `ClassicalCosineFourier` are external inputs. -/
theorem fourierSquareSum_tendsto (H : ClassicalCosineFourier) {N : ℕ → ℕ}
    (hN3 : ∀ j, 3 ≤ N j) (hOdd : ∀ j, Odd (N j)) (hN : Tendsto N atTop atTop)
    (a : ∀ j, Angles (N j)) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ j, energy (a j) ≤ C) :
    Tendsto (fun j => fourierSquareSum (a j)) atTop (𝓝 (Real.pi ^ 2 / 6)) := by
  have hdiff := angleRows_regular_comparison hN3 hN a hC0 hC
  have hdouble := hdiff.const_mul 2
  have hregular := regularEnergy_tendsto.comp hN
  have hsum := hdouble.add hregular
  have heq (j : ℕ) :
      2 * (triangularEnergy (N j) (angleRows (a j)) - triangularEnergy (N j) regularRows) +
      regularEnergy (N j) = fourierSquareSum (a j) := by
    rw [fourierSquareSum_eq_angularKernelEnergy H (a j) (by have := hN3 j; omega),
      ← regularGridEnergy_eq_regularEnergy H (by have := hN3 j; omega),
      angularKernelEnergy_of_odd (hOdd j), regularGridEnergy_of_odd (hOdd j)]
    ring
  simpa only [Function.comp_def, mul_zero, zero_add, heq] using hsum

theorem fourierSquareSum_tendsto_eventually (H : ClassicalCosineFourier) {N : ℕ → ℕ}
    (hN3 : ∀ j, 3 ≤ N j) (hOdd : ∀ j, Odd (N j)) (hN : Tendsto N atTop atTop)
    (a : ∀ j, Angles (N j)) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ᶠ j in atTop, energy (a j) ≤ C) :
    Tendsto (fun j => fourierSquareSum (a j)) atTop (𝓝 (Real.pi ^ 2 / 6)) := by
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp hC
  apply (tendsto_add_atTop_iff_nat J).mp
  exact fourierSquareSum_tendsto H (fun j => hN3 (j + J))
    (fun j => hOdd (j + J)) (hN.comp (tendsto_add_atTop_nat J))
    (fun j => a (j + J)) hC0 (fun j => hJ (j + J) (by omega))

end

end Erdos1045.KernelWeights
