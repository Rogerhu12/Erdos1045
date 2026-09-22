import StructuralNote.RewrittenOddSeries
import StructuralNote.RewrittenDifferenceSeries
import Mathlib.NumberTheory.ZetaValues

/-! The closed-form even-order normalized limit of the genuine diameter maximum. -/

namespace StructuralNote.RewrittenEvenLimit

open Real Filter RewrittenOddSeries RewrittenDifferenceSeries
open RewrittenBalancedEnergyLimit RewrittenEvenSeriesLimit
open scoped BigOperators Topology
noncomputable section

def oddSquareTerm (j : ℕ) : ℝ := 1 / ((2 * j + 1 : ℕ) : ℝ) ^ 2

theorem oddSquareTerm_summable : Summable oddSquareTerm := by
  exact hasSum_zeta_two.summable.comp_injective
    (show Function.Injective (fun j : ℕ => 2 * j + 1) by intro i j h; dsimp only at h; omega)

theorem even_square_hasSum :
    HasSum (fun j : ℕ => 1 / ((2 * j : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 24) := by
  rw [show Real.pi ^ 2 / 24 = (Real.pi ^ 2 / 6) / 4 by ring]
  apply (hasSum_zeta_two.div_const 4).congr
  intro j
  dsimp only
  push_cast
  ring

theorem odd_square_series : ∑' j, oddSquareTerm j = Real.pi ^ 2 / 8 := by
  have he := even_square_hasSum
  have h := tsum_even_add_odd (f := fun j : ℕ => (1 : ℝ) / (j : ℝ) ^ 2)
    he.summable oddSquareTerm_summable
  rw [he.tsum_eq, hasSum_zeta_two.tsum_eq] at h
  change Real.pi ^ 2 / 24 + (∑' j, oddSquareTerm j) = Real.pi ^ 2 / 6 at h
  linarith

theorem oddTerm_decomposition (j : ℕ) :
    oddTerm j = oddSquareTerm j - 3 * differenceTerm j := by
  unfold oddTerm oddSquareTerm differenceTerm
  push_cast
  field_simp
  ring

def evenLogLimit : ℝ :=
  Real.pi ^ 2 / 8 - Real.sqrt 3 * Real.pi / 4 + (9 / 4) * Real.log 3 - 3 * Real.log 2

theorem odd_series_evaluation : ∑' j, oddTerm j = evenLogLimit := by
  simp_rw [oddTerm_decomposition]
  rw [oddSquareTerm_summable.tsum_sub (differenceTerm_summable.mul_left 3),
    tsum_mul_left, odd_square_series, difference_series_eq]
  have hs : Real.sqrt 3 ≠ 0 := by positivity
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold evenLogLimit
  field_simp
  ring_nf
  rw [hs2]
  ring

theorem limitEnergy_eq : limitEnergy = evenLogLimit :=
  limitEnergy_eq_odd_series.trans odd_series_evaluation

theorem even_log_maximum_tendsto_closed :
    Tendsto logMaximum atTop (𝓝 evenLogLimit) := by
  rw [← limitEnergy_eq]
  exact even_log_maximum_tendsto

theorem even_normalized_maximum_tendsto :
    Tendsto (fun m : ℕ => M (2 * m) / (2 * m : ℝ) ^ (2 * m))
      atTop (𝓝 (Real.exp evenLogLimit)) := by
  rw [← limitEnergy_eq]
  exact even_normalized_maximum_series_tendsto

theorem exp_evenLogLimit : Real.exp evenLogLimit =
    (3 : ℝ) ^ (9 / 4 : ℝ) / 8 *
      Real.exp ((Real.pi ^ 2 - 2 * Real.sqrt 3 * Real.pi) / 8) := by
  have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have he : evenLogLimit = (Real.log 3 * (9 / 4) - Real.log 8) +
      (Real.pi ^ 2 - 2 * Real.sqrt 3 * Real.pi) / 8 := by
    rw [h8]
    unfold evenLogLimit
    ring
  rw [he, Real.exp_add, Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 8),
    ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]

/-- Corollary 1.3, even parity, in the manuscript's closed form. -/
theorem even_normalized_maximum_closed_form :
    Tendsto (fun m : ℕ => M (2 * m) / (2 * m : ℝ) ^ (2 * m))
      atTop (𝓝 ((3 : ℝ) ^ (9 / 4 : ℝ) / 8 *
        Real.exp ((Real.pi ^ 2 - 2 * Real.sqrt 3 * Real.pi) / 8))) := by
  rw [← exp_evenLogLimit]
  exact even_normalized_maximum_tendsto

end
end StructuralNote.RewrittenEvenLimit
