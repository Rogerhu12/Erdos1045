import EventualExact.FiniteMultiplier

/-! The actual finite Schur kernel and its exact convolution representation. -/

namespace StructuralNote.FixedDualClassificationKernel

open Real Erdos1045.EventualExact Erdos1045.EventualExact.FourierMultiplier
open scoped BigOperators
noncomputable section

def finiteKernel (n : ℕ) (t : ℝ) : ℝ :=
  (1 / 2) * ∑ p : Fin n, SchurWeights.weight n p * cos (p * t)

def gridAngle {n : ℕ} (j : Fin n) : ℝ := 2 * Real.pi * j / n

theorem finiteKernel_even (n : ℕ) (t : ℝ) : finiteKernel n (-t) = finiteKernel n t := by
  simp only [finiteKernel, mul_neg, cos_neg]

theorem kernel_rank_identity {n : ℕ} (i j : Fin n) :
    2 * finiteKernel n (gridAngle i - gridAngle j) =
      ∑ p : Fin n, SchurWeights.weight n p *
        (cosine n p i * cosine n p j + sine n p i * sine n p j) := by
  unfold finiteKernel
  rw [show (2 : ℝ) * ((1 / 2) * ∑ p : Fin n, SchurWeights.weight n p *
      cos (p * (gridAngle i - gridAngle j))) =
      ∑ p : Fin n, SchurWeights.weight n p * cos (p * (gridAngle i - gridAngle j)) by ring]
  apply Finset.sum_congr rfl
  intro p _
  rw [cosine_eq_cos, cosine_eq_cos, sine_eq_sin, sine_eq_sin]
  congr 1
  rw [show (p : ℝ) * (gridAngle i - gridAngle j) =
      2 * Real.pi * p * i / n - 2 * Real.pi * p * j / n by unfold gridAngle; ring,
    cos_sub]

theorem operator_convolution {n : ℕ} (q : Fin n → ℝ) (i : Fin n) :
    operator n q i = (2 / n : ℝ) * ∑ j : Fin n, q j * finiteKernel n (gridAngle i - gridAngle j) := by
  rw [operator_apply]
  simp only [finitePairing, Finset.sum_mul, ← Finset.sum_add_distrib]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [show (2 / n : ℝ) * (q j * finiteKernel n (gridAngle i - gridAngle j)) =
      (q j / n) * (2 * finiteKernel n (gridAngle i - gridAngle j)) by ring,
    kernel_rank_identity, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

end
end StructuralNote.FixedDualClassificationKernel
