import StructuralNote.FixedDualClassificationFiniteTail
import StructuralNote.FixedDualClassificationStepPotential

/-! Exact finite synthesis in the same reflected midpoint phase convention
as the actual continuous convolution. -/

namespace StructuralNote.FixedDualClassificationMidpointSynthesis

open Real Complex Erdos1045 Erdos1045.EventualExact FourierMultiplier SchurLiftBounds
open StructuralNote.FixedDualClassificationStep StructuralNote.FixedDualClassificationFiniteTail
open scoped BigOperators ComplexConjugate
noncomputable section

def finiteTerm {n : ℕ} (q : Fin n → ℝ) (j : Fin n) (p : ℕ) : ℂ :=
  (SchurWeights.weight n p : ℂ) * oscillation (-(p : ℝ)) (cellMidpoint n j) *
    conj (signedMidpointCoefficient q p)

theorem midpoint_oscillation (n p j : ℕ) :
    oscillation p (cellMidpoint n j) = LocalPhase.phase n p * character n p j := by
  rw [midpointCharacter_eq_exp]
  unfold oscillation cellMidpoint
  congr 1
  push_cast
  ring

theorem midpoint_product {n : ℕ} (q : Fin n → ℝ) (p j : Fin n) :
    midpointCoefficient q p * oscillation p (cellMidpoint n j) =
      realCoefficient q p * character n p j := by
  rw [midpointCoefficient_eq, midpoint_oscillation]
  have hh : conj (LocalPhase.phase n p) * LocalPhase.phase n p = 1 := by
    rw [mul_comm, Complex.mul_conj, LocalPhase.phase_normSq, Complex.ofReal_one]
  calc
    _ = realCoefficient q p * (conj (LocalPhase.phase n p) * LocalPhase.phase n p) *
        character n p j := by ring
    _ = _ := by rw [hh, mul_one]

theorem finiteTerm_eq_conj {n : ℕ} (q : Fin n → ℝ) (p j : Fin n) :
    finiteTerm q j p =
      conj ((SchurWeights.weight n p : ℂ) * realCoefficient q p * character n p j) := by
  rw [finiteTerm, signedMidpointCoefficient_nat, oscillation_neg,
    mul_assoc, ← map_mul, mul_comm (oscillation _ _) (midpointCoefficient q p), midpoint_product]
  simp only [map_mul, Complex.conj_ofReal]
  ring

theorem finiteTerm_neg {n : ℕ} [NeZero n] (hn : Even n)
    (q : Fin n → ℝ) (p j : Fin n) : finiteTerm q j (-p).val = conj (finiteTerm q j p.val) := by
  rw [finiteTerm_eq_conj, finiteTerm_eq_conj, weight_neg hn, realCoefficient_neg, character_neg]
  simp only [map_mul, Complex.conj_ofReal, starRingEnd_self_apply]

theorem finiteTerm_re_pair {n : ℕ} [NeZero n] (hn : Even n)
    (q : Fin n → ℝ) (p j : Fin n) :
    finiteTerm q j p.val + finiteTerm q j (-p).val = (2 * (finiteTerm q j p.val).re : ℝ) := by
  rw [finiteTerm_neg hn]
  simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using Complex.add_conj (finiteTerm q j p.val)

theorem operator_eq_midpointSum {n : ℕ} (hn : 0 < n) (heven : Even n)
    (q : Fin n → ℝ) (j : Fin n) :
    (operator n q j : ℂ) = ∑ p : Fin n, finiteTerm q j p := by
  have h := congrArg (conj : ℂ → ℂ) (operator_eq_synthesis hn heven q j)
  simp only [Complex.conj_ofReal, synthesis, map_sum] at h
  simpa only [finiteTerm_eq_conj] using h

theorem partialPotential_conj {n : ℕ} (q : Fin n → ℝ) (s : Finset (Fin n)) (j : Fin n) :
    (∑ p ∈ s, finiteTerm q j p) = conj (partialPotential q s j) := by
  simp only [partialPotential, map_sum, finiteTerm_eq_conj]

theorem midpoint_lowFrequency_error {n P : ℕ} (hn : 0 < n) (heven : Even n)
    (q : Fin n → ℝ) (j : Fin n) :
    ‖(operator n q j : ℂ) - ∑ p ∈ lowFrequencies n P, finiteTerm q j p‖ ^ 2 ≤
      8 / ((P : ℝ) + 1) * meanSquare q := by
  rw [partialPotential_conj, ← Complex.conj_ofReal (operator n q j), ← map_sub,
    Complex.norm_conj]
  exact operator_lowFrequency_error hn heven q j

theorem midpointCoefficient_norm_le {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    {A : ℝ} (hA : 0 ≤ A) (hq : ∀ j, |q j| ≤ A) (p : Fin n) :
    ‖signedMidpointCoefficient q p.val‖ ≤ A := by
  rw [signedMidpointCoefficient_nat]
  apply (sq_le_sq₀ (norm_nonneg _) hA).mp
  rw [← Complex.normSq_eq_norm_sq, midpointCoefficient_normSq]
  have h := Finset.single_le_sum (fun r (_ : r ∈ Finset.univ) =>
    Complex.normSq_nonneg (realCoefficient q r)) (Finset.mem_univ p)
  exact h.trans ((SchurOperatorBounds.realCoefficient_parseval hn q).trans_le
    (meanSquare_le_of_bound hn q hA hq))

end
end StructuralNote.FixedDualClassificationMidpointSynthesis
