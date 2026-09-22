import EventualExact.ExteriorSupportBounds
import EventualExact.PhysicalSeparation
import EventualExact.CoarseFeketeFamilyProved
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The already proved inverse-square exterior energy yields half-power geometry. -/

namespace Erdos1045.EventualExact.ExteriorSupport

open Filter ExteriorClassical ExteriorBoundary Configuration
open scoped Topology
noncomputable section

def geometricEpsilon {n : ℕ} {z : Points n} (d : ExteriorData z) : ℝ :=
  48 * Real.sqrt (errorRadius d)

theorem geometricEpsilon_nonneg {n : ℕ} {z : Points n} (d : ExteriorData z) :
    0 ≤ geometricEpsilon d := by unfold geometricEpsilon; positivity

theorem errorRadius_le_inverse {n : ℕ} {z : Points n} (d : ExteriorData z)
    (hn : 0 < n) {K : ℝ} (hbound : (n : ℝ) ^ 2 * d.energySquared ≤ K) :
    errorRadius d ≤ (6 * Real.sqrt K) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : ((n : ℝ) * Real.sqrt d.energySquared) ^ 2 ≤ K := by
    rw [mul_pow, Real.sq_sqrt d.energySquared_nonneg]
    exact hbound
  have hh := Real.le_sqrt_of_sq_le hs
  apply (le_div_iff₀ hnR).mpr
  unfold errorRadius
  nlinarith

theorem geometricEpsilon_le_half_power {n : ℕ} {z : Points n} (d : ExteriorData z)
    (hn : 0 < n) {K : ℝ} (hbound : (n : ℝ) ^ 2 * d.energySquared ≤ K) :
    geometricEpsilon d ≤ (48 * Real.sqrt (6 * Real.sqrt K)) *
      (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hr := Real.sqrt_le_sqrt (errorRadius_le_inverse d hn hbound)
  rw [Real.sqrt_div (by positivity)] at hr
  have hm := mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 48)
  unfold geometricEpsilon
  rw [Real.rpow_neg hnR.le, ← Real.sqrt_eq_rpow]
  simpa only [div_eq_mul_inv, mul_assoc] using hm

theorem errorRadius_tendsto_zero {N : ℕ → ℕ} {z : ∀ j, Points (N j)}
    (d : ∀ j, ExteriorData (z j)) (hN : Tendsto N atTop atTop) {K : ℝ}
    (hbound : ∀ᶠ j in atTop, (N j : ℝ) ^ 2 * (d j).energySquared ≤ K) :
    Tendsto (fun j => errorRadius (d j)) atTop (𝓝 0) := by
  have hNr : Tendsto (fun j => (N j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  have hu : Tendsto (fun j => (6 * Real.sqrt K) / N j) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hNr).const_mul (6 * Real.sqrt K)
  apply squeeze_zero' (Eventually.of_forall fun j => errorRadius_nonneg (d j)) _ hu
  filter_upwards [hbound, hN.eventually (eventually_ge_atTop 1)] with j hj hn
  exact errorRadius_le_inverse (d j) hn hj

end
end Erdos1045.EventualExact.ExteriorSupport

namespace Erdos1045.EventualExact.CoarseFekete

open Filter ExteriorSupport
open scoped Topology
noncomputable section

/-- All geometric scales and physical separation are consequences of a genuine
normalized Fekete family; no area or boundary slope integral is an input. -/
theorem Family.eventual_geometric_bounds (s : Family) :
    ∃ C γ : ℝ, 0 < C ∧ 0 < γ ∧ ∀ᶠ j in atTop,
      (1 / 2 : ℝ) ≤ (s.data j).capacity ∧ errorRadius (s.data j) ≤ 1 / 4 ∧
      geometricEpsilon (s.data j) ≤ C * (s.size j : ℝ) ^ (-(1 / 2 : ℝ)) ∧
      ∀ i k : Fin (s.size j), i ≠ k → γ / s.size j ≤ ‖s.points j i - s.points j k‖ := by
  obtain ⟨K, hK, henergy⟩ := s.inverse_square_energy_bounded
  let C : ℝ := 1 + 48 * Real.sqrt (6 * Real.sqrt K)
  let A : ℝ := max 1 (256 * (18 * Real.pi * Real.log 4))
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hsmall := (errorRadius_tendsto_zero s.data s.size_tendsto henergy).eventually_le_const
    (by norm_num : (0 : ℝ) < 1 / 4)
  refine ⟨C, A / (8 * Real.exp A), by dsimp [C]; positivity, by positivity, ?_⟩
  filter_upwards [s.capacity_half classicalBackground_proved.toClassicalAnalysis,
    henergy, hsmall] with j hc he hs
  have hn : 0 < s.size j := by have := s.size_ge j; omega
  refine ⟨hc, hs, ?_, ?_⟩
  · have hb := geometricEpsilon_le_half_power (s.data j) hn he
    have hC : 48 * Real.sqrt (6 * Real.sqrt K) ≤ C := by dsimp [C]; linarith
    exact hb.trans (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (by positivity) _))
  · intro i k hik
    exact PhysicalSeparation.separated (s.data j) (s.identities j) (by have := s.size_ge j; omega)
      (s.injective j) (s.fekete j) hA hc
      (s.initial_energy classicalBackground_proved.toClassicalAnalysis j) (le_max_right _ _) i k hik

end
end Erdos1045.EventualExact.CoarseFekete
