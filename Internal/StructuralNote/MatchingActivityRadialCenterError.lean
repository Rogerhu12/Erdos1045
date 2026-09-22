import StructuralNote.MatchingActivityRadialStepEnergy

/-! Assembly of the true center derivative, denominator replacement, physical
derotation, and canonical Schur residual. Every error is controlled by energy. -/

namespace StructuralNote.MatchingActivityRadialCenterError

open Erdos1045 Erdos1045.EventualExact Complex Configuration
open GeometricRelativeRemainder SignedPressureAngular SchurSpectrum FourierMultiplier SchurLift FiniteFourierLift
open MatchingActivityRadialCenterFirst MatchingActivityRadialSchurFirst
open MatchingActivityRadialDenominatorFirst MatchingActivityRadialStepEnergy
open scoped BigOperators
noncomputable section

theorem centerFirst_energy_error {n : ℕ} (hn : 4 ≤ n) (e : Equiv.Perm (Fin n)) (D C U : Points n)
    (hD : Function.Injective D) (hDa : ∀ j, D (e j) = -D j)
    (hC : ∀ j, C (e j) = C j) (hU : ∀ j, U (e j) = U j)
    {r : ℝ} (hr : 0 ≤ r) (hs : r ≤ 1 / 2) (hsmall : ∀ p, ‖quotient C D p‖ ≤ r)
    (hden : ∀ p, ‖quotient (D - root n) (root n) p‖ ≤ 1 / 2) :
    |centerFirst D C U - quadraticFirst D C U| ≤
      16 * r ^ 2 * Real.sqrt (pairEnergy (by omega) C) * Real.sqrt (pairEnergy (by omega) U) := by
  have he := centerFirst_error e D C U hD hDa hC hU hr hs hsmall
  simp only [show centerFirst D C U + ∑ p : Fin n × Fin n, (quotient C D p * quotient U D p).re = centerFirst D C U - quadraticFirst D C U by simp only [quadraticFirst, sub_neg_eq_add]] at he
  have hp := mul_le_mul (sqrt_true_energy hn D C hden) (sqrt_true_energy hn D U hden)
    (Real.sqrt_nonneg _) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg _))
  have hp' : Real.sqrt (∑ p : Fin n × Fin n, ‖quotient C D p‖ ^ 2) *
      Real.sqrt (∑ p : Fin n × Fin n, ‖quotient U D p‖ ^ 2) ≤
      8 * Real.sqrt (pairEnergy (by omega) C) * Real.sqrt (pairEnergy (by omega) U) := by
    calc
      _ ≤ (2 * Real.sqrt (2 * pairEnergy (by omega) C)) * (2 * Real.sqrt (2 * pairEnergy (by omega) U)) := hp
      _ = 4 * (Real.sqrt (2 * pairEnergy (by omega) C) * Real.sqrt (2 * pairEnergy (by omega) U)) := by ring
      _ = _ := by rw [GeometricDenominatorEnergy.sqrt_double_product]; ring
  exact (he.trans (mul_le_mul_of_nonneg_left hp' (by positivity))).trans_eq (by ring)

theorem centerFirst_schur_error {m : ℕ} (hm : 2 ≤ m) (D C c U : Points (2 * m))
    (hD : Function.Injective D) (hDa : ∀ j, D (halfTurn (by omega) j) = -D j)
    (hC : HalfPeriodic (by omega) C) (hc : HalfPeriodic (by omega) c) (hU : HalfPeriodic (by omega) U)
    {r δ : ℝ} (hr : 0 ≤ r) (hrs : r ≤ 1 / 2) (hsmall : ∀ p, ‖quotient C D p‖ ≤ r)
    (hδ : 0 ≤ δ) (hδs : δ ≤ 1 / 2) (hden : ∀ p, ‖quotient (D - root (2 * m)) (root (2 * m)) p‖ ≤ δ) :
    |centerFirst D C U - finitePairing (operator (2 * m) (constraint (by omega) c))
      (constraint (by omega) U) / (2 * m : ℝ)| ≤
      ((16 * r ^ 2 + 20 * δ) * Real.sqrt (pairEnergy (by omega) C) +
        2 * Real.sqrt (pairEnergy (by omega) (C - c)) +
        2 * Real.sqrt (StrongObjectiveEstimate.residualEnergy (by omega) c)) *
          Real.sqrt (pairEnergy (by omega) U) := by
  have h₁ := centerFirst_energy_error (show 4 ≤ 2 * m by omega)
    (Equiv.ofBijective (halfTurn (show 0 < m by omega)) (halfTurn_involutive (by omega)).bijective)
    D C U hD hDa hC hU hr hrs hsmall (fun p => (hden p).trans hδs)
  have h₂ := quadraticFirst_denominator_error (show 4 ≤ 2 * m by omega) D C U hδ hδs hden
  have h₃ := first_argument_error (show 0 < 2 * m by omega) C c U
  have h₄ := physical_schur_error hm c U hc hU
  have hsum := (abs_sub_le (centerFirst D C U) (quadraticFirst D C U)
    (finitePairing (operator (2 * m) (constraint (by omega) c)) (constraint (by omega) U) / (2 * m : ℝ))).trans
    (add_le_add h₁ ((abs_sub_le (quadraticFirst D C U) (quadraticFirst (root (2 * m)) C U) _).trans
      (add_le_add h₂ ((abs_sub_le (quadraticFirst (root (2 * m)) C U) (quadraticFirst (root (2 * m)) c U) _).trans
        (add_le_add h₃ h₄)))))
  exact hsum.trans_eq (by ring)

end
end StructuralNote.MatchingActivityRadialCenterError
