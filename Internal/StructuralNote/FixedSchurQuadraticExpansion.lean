import StructuralNote.CommonFiberSchurExpansion
import EventualExact.SchurOperatorBounds
import EventualExact.SchurWeightBounds

/-! Exact scalar Schur expansion and a quadratic remainder bound for the
linear angular field plus its actual normal error. -/

namespace StructuralNote.FixedSchurQuadraticExpansion

open Erdos1045.EventualExact FourierMultiplier SchurLiftBounds SchurOperatorBounds
open CommonFiberSchurExpansion
open scoped BigOperators

noncomputable section

def angularField {n : ℕ} (σ η : Fin n → ℝ) : Fin n → ℝ :=
  fun j => (n : ℝ) / 2 * σ j * η j

theorem energy_le_meanSquare {n : ℕ} (hn : 0 < n) (heven : Even n) (q : Fin n → ℝ) :
    0 ≤ normalizedBoxEnergy (operator n) q ∧
      normalizedBoxEnergy (operator n) q ≤ meanSquare q / 4 := by
  rw [spectral_energy hn]
  have hweight (p : Fin n) : SchurWeights.weight n p ≤ 1 / 2 := by
    have h := SchurWeights.weight_le_endpoints p.isLt.le heven
    linarith [SchurWeights.endpointReciprocal_le_quarter n p,
      SchurWeights.endpointReciprocal_le_quarter n (n - p)]
  constructor
  · exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun p _ =>
      mul_nonneg (SchurWeights.weight_nonneg _ _) (Complex.normSq_nonneg _)))
  · have hs := Finset.sum_le_sum (s := Finset.univ) (fun p _ =>
      mul_le_mul_of_nonneg_right (hweight p) (Complex.normSq_nonneg (realCoefficient q p)))
    rw [← Finset.mul_sum, realCoefficient_parseval hn] at hs
    linarith

theorem meanSquare_add_le {n : ℕ} (f g : Fin n → ℝ) :
    meanSquare (f + g) ≤ 2 * meanSquare f + 2 * meanSquare g := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    show (f j + g j) ^ 2 ≤ 2 * f j ^ 2 + 2 * g j ^ 2 by nlinarith [sq_nonneg (f j - g j)])
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  unfold meanSquare
  simp only [Pi.add_apply]
  have h := div_le_div_of_nonneg_right hs (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  exact h.trans_eq (by ring)

theorem angularField_meanSquare {n : ℕ} (σ η : Fin n → ℝ)
    (hσ : ∀ j, σ j = 1 ∨ σ j = -1) :
    meanSquare (angularField σ η) = (n : ℝ) ^ 2 / 4 * meanSquare η := by
  have hsq (j : Fin n) : (angularField σ η j) ^ 2 = (n : ℝ) ^ 2 / 4 * η j ^ 2 := by
    rcases hσ j with h | h <;> simp only [angularField, h] <;> ring
  simp only [meanSquare, hsq, ← Finset.mul_sum]
  ring

theorem quadratic_error_le {n : ℕ} (hn : 0 < n) (heven : Even n)
    (σ η e : Fin n → ℝ) (hσ : ∀ j, σ j = 1 ∨ σ j = -1) :
    |normalizedBoxEnergy (operator n) (angularField σ η + e)| ≤
      (n : ℝ) ^ 2 / 8 * meanSquare η + meanSquare e / 2 := by
  have he := energy_le_meanSquare hn heven (angularField σ η + e)
  rw [abs_of_nonneg he.1]
  have hm := meanSquare_add_le (angularField σ η) e
  rw [angularField_meanSquare σ η hσ] at hm
  linarith only [he.2, hm]

theorem exact_expansion {n : ℕ} (hn : 0 < n) (f σ η e : Fin n → ℝ) :
    normalizedBoxEnergy (operator n) (f + angularField σ η + e) =
      normalizedBoxEnergy (operator n) f +
        (∑ j, σ j * operator n f j * η j) / 2 +
        finitePairing (operator n f) e / n +
        normalizedBoxEnergy (operator n) (angularField σ η + e) := by
  rw [add_assoc, normalized_energy_add, finitePairing_add_right]
  have hpair : finitePairing (operator n f) (angularField σ η) =
      (n : ℝ) / 2 * ∑ j, σ j * operator n f j * η j := by
    simp only [finitePairing, angularField, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [hpair]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

end
end StructuralNote.FixedSchurQuadraticExpansion
