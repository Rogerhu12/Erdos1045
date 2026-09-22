import StructuralNote.FixedDualClassificationUniformPotential
import StructuralNote.FixedDualClassificationUniformEnergy
import EventualExact.WholeBoxObjective

/-! Equation (8.15) for the actual finite box Q_n and the canonical
normalization A/A_n of its periodic step profile. -/

namespace StructuralNote.FixedDualClassificationGridComparison

open Real Complex MeasureTheory Erdos1045.EventualExact FourierMultiplier FiniteBox
open FixedDualClassificationStep FixedDualClassificationStepPotential
open FixedDualClassificationPeriodicStep FixedDualClassificationCircleShift
open FixedDualClassificationOddSpectrum FixedDualClassificationStepEnergy
open FixedDualClassificationMultiplierLimit FixedDualClassificationUniformPotential
open FixedDualClassificationUniformEnergy
open scoped BigOperators
noncomputable section

local instance period_pos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem normalized_profile_bound {m : ℕ} (hm : 0 < m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ Q hm) : ∀ x : Torus, |circleProfile q (profileScale (2 * m)) x| ≤ Real.pi / 2 := by
  have hA := amplitude_pos (n := 2 * m) (by omega)
  have h := circleProfile_bound q (profileScale (2 * m)) (amplitude (2 * m)) hA.le hq.2
  have he : |profileScale (2 * m)| * amplitude (2 * m) = Real.pi / 2 := by
    rw [profileScale, abs_of_nonneg (div_nonneg (by positivity) hA.le), div_mul_cancel₀ _ hA.ne']
  simpa only [he] using h

theorem positiveWeight_exact (k : ℕ) :
    positiveWeight k = if k = 0 then 0 else 1 / ((2 * k + 1 : ℕ) + 1 : ℝ) := by
  by_cases hk : k = 0
  · subst k; norm_num [positiveWeight, kernelCoefficient, naturalKernelCoefficient]
  · simp only [positiveWeight, kernelCoefficient, naturalKernelCoefficient, if_neg hk]
    push_cast
    field_simp
    ring

/-- The energy here is exactly the manuscript's series in standard circle Fourier coefficients. -/
theorem energy_eq_standard_fourier {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) (scale : ℝ) :
    continuousEnergy q scale = ∑' k : ℕ,
      if k = 0 then 0 else
        ‖fourierCoeff (fun x => (circleProfile q scale x : ℂ)) (2 * k + 1)‖ ^ 2 /
          ((2 * k + 1 : ℕ) + 1 : ℝ) := by
  apply tsum_congr
  intro k
  rw [energyTerm, positiveWeight_exact, profileCoefficient_eq hn, circleProfile_fourierCoeff hn]
  split_ifs
  · simp only [zero_mul]
  · simp only [one_div]
    ring

/-- Both uniform comparisons of (8.15), with membership in the actual finite box as the only profile input. -/
theorem uniform_grid_comparison {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ hm : 0 < m, ∀ q : Fin (2 * m) → ℝ,
      q ∈ Q hm →
        |normalizedBoxEnergy (operator (2 * m)) q - continuousEnergy q (profileScale (2 * m))| < ε ∧
        ∀ j : Fin (2 * m), |operator (2 * m) q j -
          continuousPotential q (profileScale (2 * m)) (cellMidpoint (2 * m) j)| < ε := by
  obtain ⟨N₁, hN₁⟩ := normalized_potential_comparison (by norm_num : (0 : ℝ) ≤ 4) hε
  obtain ⟨N₂, hN₂⟩ := normalized_energy_comparison (by norm_num : (0 : ℝ) ≤ 4) hε
  refine ⟨max N₁ N₂, fun m hmN hm q hq => ?_⟩
  have hb (j : Fin (2 * m)) : |q j| ≤ 4 :=
    (hq.2 j).trans (WholeBoxObjective.amplitude_le_four (by omega))
  exact ⟨hN₂ (2 * m) (by omega) (even_two_mul m) q hb,
    hN₁ m (by omega) hm q hq.1 hb⟩

end
end StructuralNote.FixedDualClassificationGridComparison
