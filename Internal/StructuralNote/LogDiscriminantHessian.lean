import StructuralNote.LogDiscriminantSecondDerivative

/-! Splitting the exact second derivative into its velocity quadratic form and
the pairing of the actual gradient with the path acceleration. -/

namespace StructuralNote.LogDiscriminantHessian

open Erdos1045 Erdos1045.EventualExact Complex Configuration
open LogDiscriminantSecondDerivative
open scoped BigOperators ComplexConjugate
noncomputable section

def quadratic {n : ℕ} (z v : Fin n → ℂ) : ℝ :=
  -(∑ i, ∑ j, (((v i - v j) / (z i - z j)) ^ 2).re)

def accelerationPairing {n : ℕ} (z a : Fin n → ℂ) : ℝ :=
  ∑ j, inner ℝ (LocalGradient.realGradient z j) (a j)

theorem first_eq_double_sum {n : ℕ} (z a : Fin n → ℂ) :
    first z a = 2 * (∑ i, ∑ j, (a i / (z i - z j)).re) := by
  have hp (i j : Fin n) : (a i / (z j - z i)).re = -(a i / (z i - z j)).re := by
    rw [← neg_sub (z i) (z j), div_neg, neg_re]
  have hs : (∑ i, ∑ j, (a j / (z i - z j)).re) =
      -(∑ i, ∑ j, (a i / (z i - z j)).re) := by
    rw [Finset.sum_comm]
    simp only [hp, Finset.sum_neg_distrib]
  unfold first
  simp only [sub_div, sub_re, Finset.sum_sub_distrib]
  rw [hs]
  ring

theorem gradient_pairing_eq_double_sum {n : ℕ} (z a : Fin n → ℂ) :
    accelerationPairing z a = 2 * (∑ i, ∑ j, (a i / (z i - z j)).re) := by
  unfold accelerationPairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [LocalGradient.realGradient_inner]
  simp only [FeketeStationarity.nodeGradient, conj_conj, Finset.sum_mul, Complex.re_sum]
  congr 1
  have hz : (a i / (z i - z i)).re = 0 := by simp
  calc
    _ = ∑ j ∈ Finset.univ.erase i, (a i / (z i - z j)).re := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      rw [div_eq_mul_inv, mul_comm]
    _ = ∑ j, (a i / (z i - z j)).re := Finset.sum_erase _ hz

theorem first_eq_gradient {n : ℕ} (z a : Fin n → ℂ) :
    first z a = accelerationPairing z a := by
  rw [first_eq_double_sum, gradient_pairing_eq_double_sum]

theorem second_eq_quadratic_add_acceleration {n : ℕ} (z v a : Fin n → ℂ) :
    second z v a = quadratic z v + accelerationPairing z a := by
  rw [← first_eq_gradient]
  simp only [second, first, quadratic, sub_re, Finset.sum_sub_distrib]
  ring

end
end StructuralNote.LogDiscriminantHessian
