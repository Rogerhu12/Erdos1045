import StructuralNote.HessianAcceleration
import StructuralNote.HessianVelocityEnergy

/-! The angular acceleration error is controlled by the actual gradient and
diameter-vector errors, using the mean-zero angular energy. -/

namespace StructuralNote.HessianAngularAcceleration

open Erdos1045 Erdos1045.EventualExact Complex SchurSpectrum
open LogDiscriminantHessian HessianReferencePotential HessianVelocityEnergy
open scoped BigOperators
noncomputable section

theorem regular_gradient_bound {n : ℕ} (hn : 1 ≤ n) (j : Fin n) :
    ‖LocalGradient.realGradient (root n) j‖ ≤ (n : ℝ) + 1 := by
  have hg : LocalGradient.realGradient (root n) j =
      ((n : ℂ) - 1) * root n j := LocalGradient.realGradient_regular (by omega) j
  rw [hg, norm_mul]
  have hw : ‖root n j‖ = 1 := by
    simp only [root, norm_pow, ClosedFourier.root_norm, one_pow]
  rw [hw, mul_one]
  exact (norm_sub_le _ _).trans_eq (by simp)

theorem pairing_error {n : ℕ} (z w d : Fin n → ℂ) (η : Fin n → ℝ) {G M r : ℝ}
    (hM : 0 ≤ M)
    (hd : ∀ j, ‖d j‖ = 1) (hr : ∀ j, ‖d j - w j‖ ≤ r)
    (hg : ∀ j, ‖LocalGradient.realGradient z j - LocalGradient.realGradient w j‖ ≤ G)
    (hw : ∀ j, ‖LocalGradient.realGradient w j‖ ≤ M) :
    |accelerationPairing z (fun j => -d j * (η j : ℂ) ^ 2) -
      accelerationPairing w (fun j => -w j * (η j : ℂ) ^ 2)| ≤
      (G + M * r) * ∑ j, η j ^ 2 := by
  have hp (j : Fin n) :
      |inner ℝ (LocalGradient.realGradient z j) (-d j * (η j : ℂ) ^ 2) -
        inner ℝ (LocalGradient.realGradient w j) (-w j * (η j : ℂ) ^ 2)| ≤
        (G + M * r) * η j ^ 2 := by
    have he : inner ℝ (LocalGradient.realGradient z j) (-d j * (η j : ℂ) ^ 2) -
        inner ℝ (LocalGradient.realGradient w j) (-w j * (η j : ℂ) ^ 2) =
        inner ℝ (LocalGradient.realGradient z j - LocalGradient.realGradient w j)
          (-d j * (η j : ℂ) ^ 2) + inner ℝ (LocalGradient.realGradient w j)
          (-(d j - w j) * (η j : ℂ) ^ 2) := by
      rw [show -(d j - w j) * (η j : ℂ) ^ 2 =
        -d j * (η j : ℂ) ^ 2 - -w j * (η j : ℂ) ^ 2 by ring]
      simp only [inner_sub_left, inner_sub_right]
      ring
    have hn : ‖-d j * (η j : ℂ) ^ 2‖ = η j ^ 2 := by
      simp only [norm_mul, norm_neg, hd, norm_pow, norm_real, Real.norm_eq_abs,
        sq_abs, one_mul]
    have hn' : ‖-(d j - w j) * (η j : ℂ) ^ 2‖ ≤ r * η j ^ 2 := by
      simp only [norm_mul, norm_neg, norm_pow, norm_real, Real.norm_eq_abs, sq_abs]
      exact mul_le_mul_of_nonneg_right (hr j) (sq_nonneg _)
    have hfirst := (abs_real_inner_le_norm
      (LocalGradient.realGradient z j - LocalGradient.realGradient w j)
      (-d j * (η j : ℂ) ^ 2)).trans
        (mul_le_mul_of_nonneg_right (hg j) (norm_nonneg _))
    rw [hn] at hfirst
    have hsecond := (abs_real_inner_le_norm (LocalGradient.realGradient w j)
      (-(d j - w j) * (η j : ℂ) ^ 2)).trans
        (mul_le_mul (hw j) hn' (norm_nonneg _) hM)
    rw [he]
    exact (abs_add_le _ _).trans (by nlinarith only [hfirst, hsecond])
  rw [accelerationPairing, accelerationPairing, ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum (fun j _ => hp j)).trans_eq (Finset.mul_sum _ _ _).symm)

theorem regular_angular_error {n : ℕ} (hn : 2 ≤ n) (z d : Fin n → ℂ) (η : Fin n → ℝ)
    {G r : ℝ} (hG : 0 ≤ G) (hr0 : 0 ≤ r) (hmean : ∑ j, (η j : ℂ) = 0)
    (hd : ∀ j, ‖d j‖ = 1) (hr : ∀ j, ‖d j - root n j‖ ≤ r)
    (hg : ∀ j, ‖LocalGradient.realGradient z j - LocalGradient.realGradient (root n) j‖ ≤ G) :
    |accelerationPairing z (fun j => -d j * (η j : ℂ) ^ 2) -
      accelerationPairing (root n) (fun j => -root n j * (η j : ℂ) ^ 2)| ≤
      4 * (G / n + 2 * r) * pairEnergy (by omega) (fun j => (η j : ℂ)) := by
  have hp := pairing_error z (root n) d η (by positivity : 0 ≤ (n : ℝ) + 1)
    hd hr hg (regular_gradient_bound (by omega))
  have hm := mean_zero_mass hn (fun j => (η j : ℂ)) hmean
  simp only [normSq_ofReal, ← pow_two] at hm
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs : (∑ j, η j ^ 2) ≤ 4 * pairEnergy (by omega) (fun j => (η j : ℂ)) / n :=
    (le_div_iff₀ hn0).mpr (by nlinarith only [hm])
  have hc : G + ((n : ℝ) + 1) * r ≤ G + 2 * n * r := by
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) - 1 by linarith) hr0]
  have hh := mul_le_mul hc hs (Finset.sum_nonneg (fun j _ => sq_nonneg (η j)))
    (by positivity : 0 ≤ G + 2 * n * r)
  apply hp.trans (hh.trans_eq ?_)
  field_simp

end
end StructuralNote.HessianAngularAcceleration
