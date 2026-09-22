import StructuralNote.LogDiscriminantHessian
import StructuralNote.CommonFiberGeometry

/-! Exact cancellation between antiperiodic angular velocities and half-periodic
center velocities. This is an identity of the actual finite Hessian. -/

namespace StructuralNote.HessianAntipodal

open Erdos1045 Erdos1045.EventualExact Complex FourierMultiplier FiniteFourierLift SchurSpectrum SchurLift
open LogDiscriminantHessian CommonFiberGeometry
open scoped BigOperators
noncomputable section

theorem paired_mixed_zero {n : ℕ} (p : Equiv.Perm (Fin n)) (w u h : Fin n → ℂ)
    (hw : ∀ j, w (p j) = -w j) (hu : ∀ j, u (p j) = -u j) (hh : ∀ j, h (p j) = h j) :
    (∑ i, ∑ j, (((u i - u j) / (w i - w j)) * ((h i - h j) / (w i - w j))).re) = 0 := by
  let F (i j : Fin n) := (((u i - u j) / (w i - w j)) * ((h i - h j) / (w i - w j))).re
  have hp (i j : Fin n) : F (p i) (p j) = -F i j := by
    have hwd : w (p i) - w (p j) = -(w i - w j) := by rw [hw, hw]; ring
    have hud : u (p i) - u (p j) = -(u i - u j) := by rw [hu, hu]; ring
    simp only [F, hwd, hud, hh, div_neg, neg_div, neg_neg, mul_neg, neg_re]
  have hs : (∑ i, ∑ j, F (p i) (p j)) = ∑ i, ∑ j, F i j := by
    simp only [Equiv.sum_comp p]
    exact Equiv.sum_comp p (fun i => ∑ j, F i j)
  simp only [hp, Finset.sum_neg_distrib] at hs
  change (∑ i, ∑ j, F i j) = 0
  linarith

theorem paired_quadratic_add {n : ℕ} (p : Equiv.Perm (Fin n)) (w u h : Fin n → ℂ)
    (hw : ∀ j, w (p j) = -w j) (hu : ∀ j, u (p j) = -u j) (hh : ∀ j, h (p j) = h j) :
    quadratic w (u + h) = quadratic w u + quadratic w h := by
  have hz := paired_mixed_zero p w u h hw hu hh
  have hp (i j : Fin n) : (((u + h) i - (u + h) j) / (w i - w j)) ^ 2 =
      ((u i - u j) / (w i - w j)) ^ 2 + ((h i - h j) / (w i - w j)) ^ 2 +
      2 * (((u i - u j) / (w i - w j)) * ((h i - h j) / (w i - w j))) := by
    simp only [Pi.add_apply]
    ring
  have htwo (z : ℂ) : (2 * z).re = 2 * z.re := by simp [mul_re]
  simp only [quadratic, hp, add_re, htwo,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hz]
  ring

theorem angular_center_mixed_zero {m : ℕ} (hm : 0 < m) (θ η : Fin (2 * m) → ℝ)
    (h : Fin (2 * m) → ℂ) (hθ : HalfPeriodic hm (fun j => (θ j : ℂ)))
    (hη : HalfPeriodic hm (fun j => (η j : ℂ))) (hh : HalfPeriodic hm h) :
    quadratic (diameterVector θ) (fun j => I * diameterVector θ j * (η j : ℂ) + h j) =
      quadratic (diameterVector θ) (fun j => I * diameterVector θ j * (η j : ℂ)) +
        quadratic (diameterVector θ) h := by
  apply paired_quadratic_add (Equiv.ofBijective (halfTurn hm) (halfTurn_involutive hm).bijective)
  · exact diameterVector_halfTurn hm θ hθ
  · intro j
    change I * diameterVector θ (halfTurn hm j) * (η (halfTurn hm j) : ℂ) =
      -(I * diameterVector θ j * (η j : ℂ))
    have hηj : (η (halfTurn hm j) : ℂ) = η j := hη j
    rw [diameterVector_halfTurn hm θ hθ, hηj]
    ring
  · exact hh

end
end StructuralNote.HessianAntipodal
