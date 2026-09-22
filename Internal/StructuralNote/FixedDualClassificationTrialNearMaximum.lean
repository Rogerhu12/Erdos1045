import StructuralNote.FixedDualClassificationTrialLowerBound
import StructuralNote.ThirdSchwarzDefect

/-! Actual near maxima cross the third-harmonic threshold uniformly, with a
uniform potential comparison. No energy-threshold premise remains. -/

namespace StructuralNote.FixedDualClassificationTrialNearMaximum

open Real Complex Filter Erdos1045.EventualExact FourierMultiplier FiniteBox
open FixedDualClassificationTrialLowerBound FixedDualClassificationGridComparison
open FixedDualClassificationStep FixedDualClassificationStepEnergy
open FixedDualClassificationMultiplierLimit FixedDualClassificationStepPotential
open ThirdSchwarzDefect
open scoped Topology
noncomputable section

theorem inverse_square_deficit_tendsto (C₀ : ℝ) :
    Tendsto (fun m : ℕ => C₀ / (2 * m : ℝ) ^ 2) atTop (𝓝 0) := by
  have h := ((tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).pow 2).const_mul (C₀ / 4)
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at h
  convert h using 1
  funext m
  ring

theorem eventual_near_maximum_entry (C₀ : ℝ) : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (q : Fin (2 * m) → ℝ), q ∈ Q hm →
      B hm - normalizedBoxEnergy (operator (2 * m)) q ≤ C₀ / (2 * m : ℝ) ^ 2 →
      (531 : ℝ) / 2000 < continuousEnergy q (profileScale (2 * m)) ∧
      (24 : ℝ) / 25 < ‖profileCoefficient (stepProfile q (profileScale (2 * m))) 3‖ ∧
      ∀ j : Fin (2 * m), |operator (2 * m) q j -
        continuousPotential q (profileScale (2 * m)) (cellMidpoint (2 * m) j)| ≤ 1 / 100 := by
  obtain ⟨N, hN⟩ := uniform_grid_comparison (by norm_num : (0 : ℝ) < 1 / 400000)
  have hsmall := (inverse_square_deficit_tendsto C₀).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 400000))
  filter_upwards [eventual_B_fixed_gap, hsmall, eventually_ge_atTop N]
    with m hB hC hmN hm q hq hdef
  obtain ⟨henergy, hpotential⟩ := hN m hmN hm q hq
  have hthreshold : (531 : ℝ) / 2000 < continuousEnergy q (profileScale (2 * m)) := by
    have hbound := hB hm
    have herr := (abs_lt.mp henergy).2
    linarith
  refine ⟨hthreshold, normalized_third_sharp hm q hq hthreshold, fun j => ?_⟩
  have h := hpotential j
  linarith

theorem eventual_near_maximum_third (C₀ : ℝ) : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (q : Fin (2 * m) → ℝ), q ∈ Q hm →
      B hm - normalizedBoxEnergy (operator (2 * m)) q ≤ C₀ / (2 * m : ℝ) ^ 2 →
      (24 : ℝ) / 25 < ‖profileCoefficient (stepProfile q (profileScale (2 * m))) 3‖ := by
  filter_upwards [eventual_near_maximum_entry C₀] with m h hm q hq hdef
  exact (h hm q hq hdef).2.1

end
end StructuralNote.FixedDualClassificationTrialNearMaximum
