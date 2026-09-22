import StructuralNote.MatchingActivityRadialSmallness
import StructuralNote.CommonFiberHessianGeometryChord
import StructuralNote.MatchingActivityRadialDenominatorFirst

/-! Coarse energy bounds from adjacent steps. These retain the inverse-order
factor needed for the radial first-variation error. -/

namespace StructuralNote.MatchingActivityRadialStepEnergy

open Erdos1045 Erdos1045.EventualExact Complex
open FiniteFourierLift FourierMultiplier SchurSpectrum LensClosure
open GeometricRelativeRemainder SignedPressureAngular AngularFirstEnergy
open CommonFiberHessianGeometryChord
open scoped BigOperators
noncomputable section

theorem sqrt_energy_of_step {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) {B : ℝ}
    (hB : 0 ≤ B) (hstep : ∀ j, ‖difference hn c j‖ ≤ B) :
    Real.sqrt (pairEnergy hn c) ≤ (n : ℝ) ^ 2 * B := by
  have hq (p : Fin n × Fin n) : ‖quotient c (root n) p‖ ≤ (n : ℝ) * B := by
    have hh := quotient_of_step hn c hB hstep p.1 p.2
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun p _ => pow_le_pow_left₀ (norm_nonneg _) (hq p) 2)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_mul] at hs
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity, ?_⟩
  rw [pairEnergy_eq_quotient_sum]
  nlinarith [sq_nonneg ((n : ℝ) ^ 2 * B)]

theorem derotation_step {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) (c : Fin n → ℂ)
    {P T S V : ℝ} (hP : ∀ j, ‖c j‖ ≤ P) (hT : ∀ j, |θ j| ≤ T)
    (hS : ∀ j, ‖difference hn c j‖ ≤ S)
    (hV : ∀ j, |θ (successor hn j) - θ j| ≤ V) (j : Fin n) :
    ‖difference hn (fun k => (unit (θ k) - 1) * c k) j‖ ≤ T * S + P * V := by
  have he : difference hn (fun k => (unit (θ k) - 1) * c k) j =
      (unit (θ (successor hn j)) - 1) * difference hn c j +
        (unit (θ (successor hn j)) - unit (θ j)) * c j := by
    unfold difference
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_mul]
  have hT0 : 0 ≤ T := (abs_nonneg _).trans (hT j)
  have hV0 : 0 ≤ V := (abs_nonneg _).trans (hV j)
  have hleft := mul_le_mul ((unit_sub_one (θ (successor hn j))).trans (hT (successor hn j))) (hS j) (norm_nonneg _) hT0
  have hright := mul_le_mul ((norm_unit_sub_le _ _).trans (hV j)) (hP j) (norm_nonneg _) hV0
  exact (add_le_add hleft hright).trans_eq (by ring)

theorem quotient_true_le_twice {n : ℕ} (hn : 4 ≤ n) (D C : Fin n → ℂ)
    (hD : ∀ p, ‖quotient (D - root n) (root n) p‖ ≤ 1 / 2) (p : Fin n × Fin n) :
    ‖quotient C D p‖ ≤ 2 * ‖quotient C (root n) p‖ := by
  rw [MatchingActivityRadialDenominatorFirst.quotient_denominator_factor D (root n) C
    (HessianAngularReference.root_injective hn), norm_div]
  have hl : 1 / 2 ≤ ‖1 + quotient (D - root n) (root n) p‖ := by
    have hh := norm_add_le (1 + quotient (D - root n) (root n) p) (-quotient (D - root n) (root n) p)
    simp only [add_neg_cancel_right, norm_one, norm_neg] at hh
    linarith [hD p]
  apply (div_le_iff₀ (by linarith : 0 < ‖1 + quotient (D - root n) (root n) p‖)).2
  nlinarith [norm_nonneg (quotient C (root n) p)]

theorem sqrt_true_energy {n : ℕ} (hn : 4 ≤ n) (D C : Fin n → ℂ)
    (hD : ∀ p, ‖quotient (D - root n) (root n) p‖ ≤ 1 / 2) :
    Real.sqrt (∑ p : Fin n × Fin n, ‖quotient C D p‖ ^ 2) ≤
      2 * Real.sqrt (2 * pairEnergy (by omega) C) := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun p _ => pow_le_pow_left₀ (norm_nonneg _)
    (quotient_true_le_twice hn D C hD p) 2)
  simp only [mul_pow, ← Finset.mul_sum] at hs
  have he : (∑ p : Fin n × Fin n, ‖quotient C (root n) p‖ ^ 2) = 2 * pairEnergy (by omega) C := by
    rw [pairEnergy_eq_quotient_sum]
    ring
  rw [he] at hs
  have hh := Real.sqrt_le_sqrt hs
  simpa only [Real.sqrt_mul (show (0 : ℝ) ≤ 2 ^ 2 by positivity), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] using hh

end
end StructuralNote.MatchingActivityRadialStepEnergy
