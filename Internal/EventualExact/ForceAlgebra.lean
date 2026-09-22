import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

/-!
# A finite force-square identity

The combinatorial identity only uses antisymmetry and one identity for three
distinct indices. Its circle specialization has no asymptotic or geometric
assumptions: distinct angles modulo a full turn suffice.
-/

namespace Erdos1045.EventualExact

open scoped BigOperators

noncomputable section

section Finite

variable {ι : Type*}

/-- An antisymmetric interaction is zero on the diagonal. -/
theorem interaction_diagonal_zero (c : ι → ι → ℝ)
    (hskew : ∀ i j, c j i = -c i j) (i : ι) : c i i = 0 := by
  have h := hskew i i
  linarith

/-- The three-index expression, including repeated indices. -/
theorem interaction_triple_all [DecidableEq ι] (c : ι → ι → ℝ)
    (hskew : ∀ i j, c j i = -c i j)
    (htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      c i j * c i k + c j i * c j k + c k i * c k j = -1)
    (i j k : ι) :
    c i j * c i k + c j i * c j k + c k i * c k j =
      -1 + (if i = j then 1 + c i k ^ 2 else 0) +
        (if i = k then 1 + c i j ^ 2 else 0) +
        (if j = k then 1 + c i j ^ 2 else 0) -
        (if i = j ∧ j = k then 2 else 0) := by
  classical
  have hz := interaction_diagonal_zero c hskew
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      norm_num [hz]
    · simp [hik, hz, hskew i k, pow_two]
  · by_cases hik : i = k
    · subst k
      simp [hij, Ne.symm hij, hz, hskew i j, pow_two]
    · by_cases hjk : j = k
      · subst k
        simp [hij, hz, pow_two]
      · simp [hij, hik, hjk, htriple i j k hij hik hjk]

/-- Summing the triple identity counts all interactions, without choosing an
ordering on the finite index type. -/
theorem finite_force_square_identity [Fintype ι] (c : ι → ι → ℝ)
    (hskew : ∀ i j, c j i = -c i j)
    (htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      c i j * c i k + c j i * c j k + c k i * c k j = -1) :
    (∑ i, (∑ j, c i j) ^ 2) = (∑ i, ∑ j, c i j ^ 2) -
      (Fintype.card ι : ℝ) * (Fintype.card ι - 1) * (Fintype.card ι - 2) / 3 := by
  classical
  have ht := congrArg (fun f : ι → ι → ι → ℝ => ∑ i, ∑ j, ∑ k, f i j k)
    (funext fun i => funext fun j => funext fun k =>
      interaction_triple_all c hskew htriple i j k)
  have hfirst : (∑ i, ∑ j, ∑ k, c i j * c i k) = ∑ i, (∑ j, c i j) ^ 2 := by
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul, pow_two]
  have hsecond : (∑ i, ∑ j, ∑ k, c j i * c j k) = ∑ i, (∑ j, c i j) ^ 2 := by
    rw [Finset.sum_comm]
    exact hfirst
  have hthird : (∑ i, ∑ j, ∑ k, c k i * c k j) = ∑ i, (∑ j, c i j) ^ 2 := by
    calc
      _ = ∑ i, ∑ k, ∑ j, c k i * c k j := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := by rw [Finset.sum_comm]; exact hfirst
  have hdiag₁ : (∑ i, ∑ j, ∑ k, if i = j then 1 + c i k ^ 2 else 0) =
      (Fintype.card ι : ℝ) ^ 2 + ∑ i, ∑ k, c i k ^ 2 := by
    simp_rw [Finset.sum_ite_irrel, Finset.sum_add_distrib]
    simp [Finset.sum_add_distrib, pow_two]
  have hdiag₂ : (∑ i, ∑ j, ∑ k, if i = k then 1 + c i j ^ 2 else 0) =
      (Fintype.card ι : ℝ) ^ 2 + ∑ i, ∑ j, c i j ^ 2 := by
    simp [Finset.sum_add_distrib, pow_two]
  have hdiag₃ : (∑ i, ∑ j, ∑ k, if j = k then 1 + c i j ^ 2 else 0) =
      (Fintype.card ι : ℝ) ^ 2 + ∑ i, ∑ j, c i j ^ 2 := by
    simp [Finset.sum_add_distrib, pow_two]
  have hall : (∑ i : ι, ∑ j : ι, ∑ k : ι, if i = j ∧ j = k then (2 : ℝ) else 0) =
      2 * Fintype.card ι := by
    simp [ite_and, mul_comm]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at ht
  rw [hfirst, hsecond, hthird, hdiag₁, hdiag₂, hdiag₃, hall] at ht
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at ht
  nlinarith

end Finite

end

end Erdos1045.EventualExact
