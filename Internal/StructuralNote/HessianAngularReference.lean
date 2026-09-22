import StructuralNote.HessianReferencePotential
import StructuralNote.HessianAntipodal

/-! At the regular configuration the angular velocity and acceleration combine
to exactly minus twice the angular energy. -/

namespace StructuralNote.HessianAngularReference

open Erdos1045 Erdos1045.EventualExact Complex SchurSpectrum
open LogDiscriminantSecondDerivative LogDiscriminantHessian HessianReferencePotential
open AngularObjectiveCurvature
open scoped BigOperators
noncomputable section

theorem root_injective {n : ℕ} (hn : 4 ≤ n) : Function.Injective (root n) := by
  have he : root n = Configuration.regular n := funext (fun j => LocalRigidity.root_power_eq_regular n j)
  rw [he]
  exact LocalConfiguration.regular_injective hn ClosedFourier.geometricSine

theorem pair_angular_second {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : x ≠ y)
    (a b : ℝ) :
    (((-x * (a : ℂ) ^ 2 - -y * (b : ℂ) ^ 2) / (x - y)) -
      ((I * x * (a : ℂ) - I * y * (b : ℂ)) / (x - y)) ^ 2).re =
        -(a - b) ^ 2 / ‖x - y‖ ^ 2 := by
  have he : ((-x * (a : ℂ) ^ 2 - -y * (b : ℂ) ^ 2) / (x - y)) -
      ((I * x * (a : ℂ) - I * y * (b : ℂ)) / (x - y)) ^ 2 =
      x * y / (x - y) ^ 2 * ((a - b : ℝ) : ℂ) ^ 2 := by
    push_cast
    field_simp [sub_ne_zero.mpr hxy]
    ring_nf
    simp only [I_sq]
    ring
  rw [he, unit_pair_kernel hx hy hxy]
  simp only [← ofReal_pow, ← ofReal_mul, ofReal_re]
  ring

theorem angular_second_eq_energy {n : ℕ} (hn : 4 ≤ n) (η : Fin n → ℝ) :
    second (root n) (fun j => I * root n j * (η j : ℂ))
      (fun j => -root n j * (η j : ℂ) ^ 2) = -2 * pairEnergy (by omega) (fun j => (η j : ℂ)) := by
  have hi := root_injective hn
  have hp (i j : Fin n) :
      (((-root n i * (η i : ℂ) ^ 2 - -root n j * (η j : ℂ) ^ 2) / (root n i - root n j)) -
        ((I * root n i * (η i : ℂ) - I * root n j * (η j : ℂ)) / (root n i - root n j)) ^ 2).re =
          -(η i - η j) ^ 2 / ‖root n i - root n j‖ ^ 2 := by
    by_cases hij : i = j
    · subst j
      simp
    · apply pair_angular_second _ _ (hi.ne hij)
      · simp only [root, norm_pow, ClosedFourier.root_norm, one_pow]
      · simp only [root, norm_pow, ClosedFourier.root_norm, one_pow]
  calc
    _ = -(∑ i, ∑ j, (η i - η j) ^ 2 / ‖root n i - root n j‖ ^ 2) := by
      dsimp only [second]
      simp only [hp, neg_div, Finset.sum_neg_distrib]
    _ = _ := by
      rw [pairEnergy_eq_chord_sum]
      simp only [← ofReal_sub, normSq_eq_norm_sq, norm_real, Real.norm_eq_abs, sq_abs, root]
      ring

theorem angular_quadratic_acceleration {n : ℕ} (hn : 4 ≤ n) (η : Fin n → ℝ) :
    quadratic (root n) (fun j => I * root n j * (η j : ℂ)) +
      accelerationPairing (root n) (fun j => -root n j * (η j : ℂ) ^ 2) =
        -2 * pairEnergy (by omega) (fun j => (η j : ℂ)) := by
  rw [← second_eq_quadratic_add_acceleration]
  exact angular_second_eq_energy hn η

end
end StructuralNote.HessianAngularReference
