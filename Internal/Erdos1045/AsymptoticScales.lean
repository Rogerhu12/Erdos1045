import Erdos1045.Bootstrap
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Consequences of the second-order capacity bootstrap

All estimates are along an arbitrary sequence of dimensions tending to
infinity. In particular they can be applied to a sequence of odd dimensions
selected by contradiction. No rate statement is an external classical input.
-/

namespace Erdos1045.AsymptoticScales

open Filter
open scoped Topology
noncomputable section

theorem inv_dimension {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) :
    Tendsto (fun j => (1 : ℝ) / N j) atTop (𝓝 0) := by
  have hc : Tendsto (fun j => (N j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp hc

theorem eventual_real_dimension {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (B : ℝ) : ∀ᶠ j in atTop, B ≤ (N j : ℝ) := by
  exact (tendsto_natCast_atTop_atTop.comp hN).eventually (eventually_ge_atTop B)

theorem bootstrap_eventually {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {δ E : ℕ → ℝ} {A B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hδ : ∀ᶠ j in atTop, 0 ≤ δ j)
    (he : ∀ᶠ j in atTop, E j ^ 2 ≤ C * δ j)
    (ht : ∀ᶠ j in atTop, 0 ≤ -(N j : ℝ) * (N j - 1) * δ j +
      A * N j * E j + B * N j * E j ^ 2) :
    ∀ᶠ j in atTop, (N j : ℝ) ^ 2 * δ j ≤ 4 * A ^ 2 * C ∧
      (N j : ℝ) ^ 2 * E j ^ 2 ≤ 4 * A ^ 2 * C ^ 2 := by
  filter_upwards [eventual_real_dimension hN 4,
    eventual_real_dimension hN (4 * B * C), hδ, he, ht] with j hn hl hd he ht
  exact Bootstrap.quantitative_bootstrap hn hd hB hC he hl (by nlinarith [ht])

theorem inv_square_bound {n x K : ℝ} (hn : 0 < n) (h : n ^ 2 * x ≤ K) :
    x ≤ K * (1 / n) ^ 2 := by
  have h' : x ≤ K / n ^ 2 := (le_div_iff₀ (sq_pos_of_pos hn)).2 (by nlinarith)
  convert h' using 1; ring

theorem inverse_square_tendsto {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {x : ℕ → ℝ} {K : ℝ}
    (hx : ∀ᶠ j in atTop, 0 ≤ x j)
    (hb : ∀ᶠ j in atTop, (N j : ℝ) ^ 2 * x j ≤ K) :
    Tendsto x atTop (𝓝 0) := by
  have hu : Tendsto (fun j => K * ((1 : ℝ) / N j) ^ 2) atTop (𝓝 0) := by
    simpa using ((inv_dimension hN).pow 2).const_mul K
  apply squeeze_zero' hx _ hu
  filter_upwards [eventual_real_dimension hN 1, hb] with j hn hb
  exact inv_square_bound (by linarith) hb

theorem dimension_times_tendsto {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {x : ℕ → ℝ} {K : ℝ}
    (hx : ∀ᶠ j in atTop, 0 ≤ x j)
    (hb : ∀ᶠ j in atTop, (N j : ℝ) ^ 2 * x j ≤ K) :
    Tendsto (fun j => (N j : ℝ) * x j) atTop (𝓝 0) := by
  have hu : Tendsto (fun j => K * ((1 : ℝ) / N j)) atTop (𝓝 0) := by
    simpa using (inv_dimension hN).const_mul K
  apply squeeze_zero' (hx.mono fun j hj => mul_nonneg (Nat.cast_nonneg _) hj) _ hu
  filter_upwards [eventual_real_dimension hN 1, hb] with j hn hb
  have hn0 : (0 : ℝ) < N j := by linarith
  have h' : (N j : ℝ) * x j ≤ K / N j :=
    (le_div_iff₀ hn0).2 (by nlinarith)
  convert h' using 1; ring

theorem energy_sqrt_dimension_tendsto {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {E : ℕ → ℝ} {K : ℝ} (hE : ∀ᶠ j in atTop, 0 ≤ E j)
    (hb : ∀ᶠ j in atTop, (N j : ℝ) ^ 2 * E j ^ 2 ≤ K) :
    Tendsto (fun j => E j * Real.sqrt (N j : ℝ)) atTop (𝓝 0) := by
  have hs := dimension_times_tendsto hN
    (Eventually.of_forall fun j => sq_nonneg (E j)) hb
  have ht := (Real.continuous_sqrt.tendsto 0).comp hs
  simp only [Real.sqrt_zero, Function.comp_def] at ht
  apply ht.congr'
  filter_upwards [hE] with j hj
  rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hj]
  ring

theorem cubic_fourth_bound {n E K : ℝ} (hn : 0 < n)
    (hb : n ^ 2 * E ^ 2 ≤ K) : n ^ 3 * E ^ 4 ≤ K ^ 2 / n := by
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ n ^ 2 * E ^ 2) hb 2
  apply (le_div_iff₀ hn).2
  nlinarith [hs]

theorem cubic_fourth_tendsto {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {E : ℕ → ℝ} {K : ℝ}
    (hb : ∀ᶠ j in atTop, (N j : ℝ) ^ 2 * E j ^ 2 ≤ K) :
    Tendsto (fun j => (N j : ℝ) ^ 3 * E j ^ 4) atTop (𝓝 0) := by
  have hu : Tendsto (fun j => K ^ 2 / (N j : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (inv_dimension hN).const_mul (K ^ 2)
  apply squeeze_zero' (Eventually.of_forall fun j => by positivity) _ hu
  filter_upwards [eventual_real_dimension hN 1, hb] with j hn hb
  exact cubic_fourth_bound (by linarith) hb

/-- The SC upper-side error on the single radius `1+1/n` vanishes. -/
theorem radial_error_tendsto {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {E : ℕ → ℝ} {K : ℝ} (hE : ∀ᶠ j in atTop, 0 ≤ E j)
    (hb : ∀ᶠ j in atTop, (N j : ℝ) ^ 2 * E j ^ 2 ≤ K) :
    Tendsto (fun j => 1 / (N j : ℝ) +
      E j * Real.sqrt (N j : ℝ) / Real.sqrt Real.pi) atTop (𝓝 0) := by
  simpa using (inv_dimension hN).add
    ((energy_sqrt_dimension_tendsto hN hE hb).div_const (Real.sqrt Real.pi))

end
end Erdos1045.AsymptoticScales
