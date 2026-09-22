import EventualExact.LogDiscriminantGradient
import Erdos1045.ClosedGeometricSine

/-! The near/far estimate tends to zero uniformly over all vertices. -/

namespace Erdos1045.EventualExact.LocalGradient

open Complex Configuration Filter
open scoped BigOperators Topology
noncomputable section

def gradientError (n : ℕ) (u : ℕ → ℂ) : ℝ :=
  ‖fun i : Fin n => realGradient (fun j : Fin n => LocalPhase.regularRoot n ^ (j : ℕ) + u j) i -
    ((n : ℂ) - 1) * LocalPhase.regularRoot n ^ (i : ℕ)‖ / (n : ℝ)

theorem gradientError_nonneg (n : ℕ) (u : ℕ → ℂ) : 0 ≤ gradientError n u := by
  exact div_nonneg (norm_nonneg _) (Nat.cast_nonneg n)

theorem gradientError_bound {n K : ℕ} (hn : 0 < n) (hK : 0 < K)
    (u : ℕ → ℂ) (hu : Function.Periodic u n) {η : ℝ} (hη : 0 ≤ η)
    (hsmall : η ≤ 1 / 2)
    (hpair : ∀ i : Fin n, ∀ h ∈ Finset.Ico 1 n, ‖LocalDFT.pairRatio n u i h‖ ≤ η) :
    gradientError n u ≤ 2 * (η * (harmonic K : ℝ) +
      Real.sqrt (2 * LocalDFT.energyA n u) * Real.sqrt (1 / (K : ℝ))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hH : 0 ≤ (harmonic K : ℝ) := by unfold harmonic; positivity
  unfold gradientError
  apply (div_le_iff₀ hnR).2
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  have h := realGradient_difference_bound hn hK u hu hη hsmall hpair i
  rw [realGradient_regular hn i] at h
  exact (div_le_iff₀ hnR).1 h

theorem gradientError_tendsto {N : ℕ → ℕ} {u : ℕ → ℕ → ℂ} {η : ℕ → ℝ} {C : ℝ}
    (hη : Tendsto η atTop (𝓝 0))
    (hgood : ∀ᶠ j in atTop, 0 < N j ∧ Function.Periodic (u j) (N j) ∧ 0 ≤ η j ∧
      (∀ i : Fin (N j), ∀ h ∈ Finset.Ico 1 (N j),
        ‖LocalDFT.pairRatio (N j) (u j) i h‖ ≤ η j) ∧ LocalDFT.energyA (N j) (u j) ≤ C) :
    Tendsto (fun j => gradientError (N j) (u j)) atTop (𝓝 0) := by
  have htail : Tendsto (fun K : ℕ => 2 * Real.sqrt (2 * C) * Real.sqrt (1 / (K : ℝ)))
      atTop (𝓝 0) := by
    have hi : Tendsto (fun K : ℕ => 1 / (K : ℝ)) atTop (𝓝 0) := by
      simpa only [one_div, Function.comp_def] using
        tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_def, Real.sqrt_zero, mul_zero] using
      ((Real.continuous_sqrt.tendsto 0).comp hi).const_mul (2 * Real.sqrt (2 * C))
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Eventually.of_forall (fun j => hb.trans_le (gradientError_nonneg _ _))
  · intro ε hε
    have hKlarge := htail.eventually (eventually_lt_nhds (show (0 : ℝ) < ε / 2 by linarith))
    rcases (hKlarge.and (eventually_gt_atTop 0)).exists with ⟨K, hKbound, hK⟩
    have hnear : Tendsto (fun j => 2 * η j * (harmonic K : ℝ)) atTop (𝓝 0) := by
      simpa only [mul_zero, zero_mul] using (hη.const_mul 2).mul_const (harmonic K : ℝ)
    have hnlarge := hnear.eventually (eventually_lt_nhds (show (0 : ℝ) < ε / 2 by linarith))
    have hsmall := hη.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
    filter_upwards [hgood, hnlarge, hsmall] with j hj hjnear hjsmall
    have hb := gradientError_bound hj.1 hK (u j) hj.2.1 hj.2.2.1 hjsmall.le hj.2.2.2.1
    have hs := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hj.2.2.2.2 (by norm_num : (0 : ℝ) ≤ 2))
    have ht := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg (1 / (K : ℝ)))
    nlinarith

/-- The original adjacent-edge control already implies every pair quotient bound. -/
theorem gradientError_tendsto_of_edges {N : ℕ → ℕ} {u : ℕ → ℕ → ℂ}
    {η : ℕ → ℝ} {C : ℝ} (hη : Tendsto η atTop (𝓝 0))
    (hgood : ∀ᶠ j in atTop, 4 ≤ N j ∧ Function.Periodic (u j) (N j) ∧ 0 ≤ η j ∧
      (∀ i : ℕ, ‖u j (i + 1) - u j i‖ ≤ η j * ‖LocalPhase.regularRoot (N j) - 1‖) ∧
      LocalDFT.energyA (N j) (u j) ≤ C) :
    Tendsto (fun j => gradientError (N j) (u j)) atTop (𝓝 0) := by
  apply gradientError_tendsto (η := fun j => 2 * η j) (C := C)
    (by simpa only [mul_zero] using hη.const_mul 2)
  filter_upwards [hgood] with j hj
  refine ⟨by omega, hj.2.1, mul_nonneg (by norm_num) hj.2.2.1, ?_, hj.2.2.2.2⟩
  intro i h hh
  apply LocalMaximum.pair_ratio_bound ClosedFourier.geometricSine hj.1 (u j) hj.2.1 hj.2.2.1 hj.2.2.2.1
  have ht := Finset.mem_Ico.mp hh
  exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr ht.2⟩

theorem vertex_gradient_le_error {n : ℕ} (u : ℕ → ℂ) (i : Fin n) :
    ‖realGradient (fun j : Fin n => LocalPhase.regularRoot n ^ (j : ℕ) + u j) i -
      ((n : ℂ) - 1) * LocalPhase.regularRoot n ^ (i : ℕ)‖ / (n : ℝ) ≤ gradientError n u :=
  div_le_div_of_nonneg_right (norm_le_pi_norm
    (fun i : Fin n => realGradient (fun j : Fin n => LocalPhase.regularRoot n ^ (j : ℕ) + u j) i -
      ((n : ℂ) - 1) * LocalPhase.regularRoot n ^ (i : ℕ)) i) (Nat.cast_nonneg n)

end
end Erdos1045.EventualExact.LocalGradient
