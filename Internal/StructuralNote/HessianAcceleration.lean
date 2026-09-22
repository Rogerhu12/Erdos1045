import StructuralNote.CommonFiberFullSecond
import StructuralNote.HessianReferencePotential

/-! The regular gradient annihilates the actual half-periodic center
acceleration. Only the small gradient remainder contributes to that term. -/

namespace StructuralNote.HessianAcceleration

open Erdos1045 Erdos1045.EventualExact Complex FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open CommonFiberSecondDerivative LogDiscriminantHessian HessianReferencePotential
open scoped BigOperators
noncomputable section

theorem integral_repeat_halfPeriodic {m : ℕ} (hm : 0 < m) (d : Fin m → ℂ) (hz : ∑ j, d j = 0) :
    HalfPeriodic hm (integral (BoxLensLift.repeatHalf hm d)) := by
  have hd : difference (by omega) (integral (BoxLensLift.repeatHalf hm d)) =
      BoxLensLift.repeatHalf hm d := by
    apply difference_integral
    rw [BoxLensLift.repeatHalf_sum, hz, mul_zero]
  have he : (fun j => integral (BoxLensLift.repeatHalf hm d) (halfTurn hm j)) =
      integral (BoxLensLift.repeatHalf hm d) := by
    apply integral_unique (by omega)
    · have hs := Equiv.sum_comp (Equiv.ofBijective (halfTurn hm) (halfTurn_involutive hm).bijective)
        (integral (BoxLensLift.repeatHalf hm d))
      exact hs.trans (integral_mean_zero (by omega) _)
    · funext k
      change integral (BoxLensLift.repeatHalf hm d) (halfTurn hm (successor _ k)) -
        integral (BoxLensLift.repeatHalf hm d) (halfTurn hm k) = _
      rw [halfTurn_successor]
      change difference (by omega) (integral (BoxLensLift.repeatHalf hm d)) (halfTurn hm k) = _
      rw [hd]
      exact BoxLensLift.repeatHalf_halfTurn hm d k
  exact fun j => congrFun he j

theorem centerAcceleration_halfPeriodic {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ) (η : Fin (2 * m) → ℝ)
    (h : Fin (2 * m) → ℂ) (ξ' ξ'' : ℂ)
    (hz : (∑ j, acceleration hm θ v σ ξ η h ξ' ξ'' j) = 0) :
    HalfPeriodic hm (centerAcceleration hm θ v σ ξ η h ξ' ξ'') :=
  integral_repeat_halfPeriodic hm _ hz

theorem paired_inner_zero {n : ℕ} (p : Equiv.Perm (Fin n)) (g a : Fin n → ℂ)
    (hg : ∀ j, g (p j) = -g j) (ha : ∀ j, a (p j) = a j) :
    (∑ j, inner ℝ (g j) (a j)) = 0 := by
  have hs := Equiv.sum_comp p (fun j => inner ℝ (g j) (a j))
  simp only [hg, ha, inner_neg_left, Finset.sum_neg_distrib] at hs
  linarith

theorem regular_pairing_zero {m : ℕ} (hm : 0 < m) (a : Fin (2 * m) → ℂ)
    (ha : HalfPeriodic hm a) : accelerationPairing (root (2 * m)) a = 0 := by
  apply paired_inner_zero (Equiv.ofBijective (halfTurn hm) (halfTurn_involutive hm).bijective)
  · intro j
    have hr : root (2 * m) (halfTurn hm j) = -root (2 * m) j := by
      simpa only [root, character, Nat.mul_one] using character_halfTurn hm (by decide : Odd 1) j
    change LocalGradient.realGradient (root (2 * m)) (halfTurn hm j) =
      -LocalGradient.realGradient (root (2 * m)) j
    have hg (k : Fin (2 * m)) : LocalGradient.realGradient (root (2 * m)) k =
        (((2 * m : ℕ) : ℂ) - 1) * root (2 * m) k :=
      LocalGradient.realGradient_regular (by omega) k
    rw [hg, hg, hr]
    ring
  · exact ha

theorem accelerationPairing_error {n : ℕ} (z w a : Fin n → ℂ) {G : ℝ}
    (hG : ∀ j, ‖LocalGradient.realGradient z j - LocalGradient.realGradient w j‖ ≤ G) :
    |accelerationPairing z a - accelerationPairing w a| ≤ G * ∑ j, ‖a j‖ := by
  have he : accelerationPairing z a - accelerationPairing w a =
      ∑ j, inner ℝ (LocalGradient.realGradient z j - LocalGradient.realGradient w j) (a j) := by
    simp only [accelerationPairing, inner_sub_left, Finset.sum_sub_distrib]
  rw [he, Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (hG j) (norm_nonneg _))

theorem halfPeriodic_acceleration_error {m : ℕ} (hm : 0 < m) (z a : Fin (2 * m) → ℂ)
    {G : ℝ} (ha : HalfPeriodic hm a)
    (hG : ∀ j, ‖LocalGradient.realGradient z j - LocalGradient.realGradient (root (2 * m)) j‖ ≤ G) :
    |accelerationPairing z a| ≤ G * ∑ j, ‖a j‖ := by
  have hh := accelerationPairing_error z (root (2 * m)) a hG
  rwa [regular_pairing_zero hm a ha, sub_zero] at hh

end
end StructuralNote.HessianAcceleration
