import StructuralNote.RewrittenEvenSeriesLimit

/-! Identification of the balanced spectral limit with the manuscript's
positive odd-index series. -/

namespace StructuralNote.RewrittenOddSeries

open Real Filter RewrittenBalancedEnergyPartial RewrittenBalancedEnergyLimit
open RewrittenEvenSeriesLimit FixedDualClassificationStepEnergy
open FixedDualClassificationOddSpectrum
open scoped BigOperators Topology
noncomputable section

def oddTerm (j : ℕ) : ℝ :=
  1 / (((2 * j + 1 : ℕ) : ℝ) ^ 2 * (3 * (2 * j + 1 : ℕ) + 1))

theorem limitTerm_three_mul (j : ℕ) : limitTerm (3 * j) = 0 := by
  have hc : Real.cos (Real.pi * ((2 * (3 * j) + 1 : ℕ) : ℝ) / 3) = 1 / 2 := by
    have he : Real.pi * ((2 * (3 * j) + 1 : ℕ) : ℝ) / 3 =
        Real.pi / 3 + (j : ℝ) * (2 * Real.pi) := by push_cast; ring
    rw [he, Real.cos_add_nat_mul_two_pi, Real.cos_pi_div_three]
  simp only [limitTerm, hc]
  norm_num

theorem limitTerm_three_mul_add_two (j : ℕ) : limitTerm (3 * j + 2) = 0 := by
  have hc : Real.cos (Real.pi * ((2 * (3 * j + 2) + 1 : ℕ) : ℝ) / 3) = 1 / 2 := by
    have he : Real.pi * ((2 * (3 * j + 2) + 1 : ℕ) : ℝ) / 3 =
        ((j + 1 : ℕ) : ℝ) * (2 * Real.pi) - Real.pi / 3 := by push_cast; ring
    rw [he, Real.cos_nat_mul_two_pi_sub, Real.cos_pi_div_three]
  simp only [limitTerm, hc]
  norm_num

theorem limitTerm_three_mul_add_one (j : ℕ) : limitTerm (3 * j + 1) = oddTerm j := by
  have hc : Real.cos (Real.pi * ((2 * (3 * j + 1) + 1 : ℕ) : ℝ) / 3) = -1 := by
    have he : Real.pi * ((2 * (3 * j + 1) + 1 : ℕ) : ℝ) / 3 =
        (j : ℝ) * (2 * Real.pi) + Real.pi := by push_cast; ring
    rw [he, Real.cos_nat_mul_two_pi_add_pi]
  simp only [limitTerm, hc, positiveWeight, kernelCoefficient, naturalKernelCoefficient,
    if_neg (by omega : 3 * j + 1 ≠ 0), oddTerm]
  push_cast
  field_simp
  ring

theorem limitTerm_support : Function.support limitTerm ⊆ Set.range (fun j : ℕ => 3 * j + 1) := by
  intro k hk
  have hn : limitTerm k ≠ 0 := hk
  have hmod := Nat.mod_lt k (by norm_num : 0 < 3)
  have hdiv := Nat.div_add_mod k 3
  rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with h0 | h1 | h2
  · have he : k = 3 * (k / 3) := by omega
    exact False.elim (hn (he ▸ limitTerm_three_mul (k / 3)))
  · exact ⟨k / 3, by dsimp only; omega⟩
  · have he : k = 3 * (k / 3) + 2 := by omega
    exact False.elim (hn (he ▸ limitTerm_three_mul_add_two (k / 3)))

theorem oddTerm_summable : Summable oddTerm := by
  have h := limitTerm_summable.comp_injective
    (show Function.Injective (fun j : ℕ => 3 * j + 1) by intro i j h; dsimp only at h; omega)
  simpa only [Function.comp_def, limitTerm_three_mul_add_one] using h

theorem limitEnergy_eq_odd_series : limitEnergy = ∑' j, oddTerm j := by
  have h := (show Function.Injective (fun j : ℕ => 3 * j + 1) by
    intro i j h; dsimp only at h; omega).tsum_eq limitTerm_support
  simpa only [limitTerm_three_mul_add_one, limitEnergy] using h.symm

/-- Formula (10.3), indexed by the positive odd integers r = 2j+1. -/
theorem even_log_maximum_odd_series_tendsto :
    Tendsto logMaximum atTop (𝓝 (∑' j, oddTerm j)) := by
  rw [← limitEnergy_eq_odd_series]
  exact even_log_maximum_tendsto

end
end StructuralNote.RewrittenOddSeries
