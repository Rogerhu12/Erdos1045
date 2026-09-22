import StructuralNote.HessianReferenceCoercivity
import StructuralNote.HessianAngularAcceleration
import StructuralNote.HessianPerturbationBudget

/-! A quantitative Hessian comparison retaining both actual acceleration
terms. The geometric estimates can be substituted independently. -/

namespace StructuralNote.HessianComparison

open Erdos1045 Erdos1045.EventualExact Complex SchurSpectrum
open LogDiscriminantSecondDerivative LogDiscriminantHessian HessianReferencePotential
open HessianAcceleration HessianReferenceCoercivity HessianVelocityEnergy
open HessianAngularAcceleration HessianPerturbationBudget CommonTangentialParameters
open scoped BigOperators
noncomputable section

def errorCoefficient (n : ℕ) (δ ε G K r : ℝ) : ℝ :=
  20 * δ * (24 + 2 * ε ^ 2) + 16 * ε + 2 * ε ^ 2 + G * K + 4 * (G / n + 2 * r)

theorem second_upper_bound {m : ℕ} (hm : 2 ≤ m)
    (z d c a : Fin (2 * m) → ℂ) (η : Fin (2 * m) → ℝ) (h : Fin (2 * m) → ℂ)
    {δ ε G K r : ℝ} (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 2)
    (hε : 0 ≤ ε) (hG : 0 ≤ G) (hr0 : 0 ≤ r)
    (hη : HalfPeriodic (by omega) (fun j => (η j : ℂ))) (hmean : ∑ j, (η j : ℂ) = 0)
    (hh : ParameterSpace (by omega) h) (ha : HalfPeriodic (by omega) a)
    (hd : ∀ j, ‖d j‖ = 1) (hr : ∀ j, ‖d j - root (2 * m) j‖ ≤ r)
    (hg : ∀ j, ‖LocalGradient.realGradient z j - LocalGradient.realGradient (root (2 * m)) j‖ ≤ G)
    (hrelative : ∀ i j, i ≠ j →
      ‖(z i - z j) / (root (2 * m) i - root (2 * m) j) - 1‖ ≤ δ)
    (hvelocity : pairEnergy (by omega)
      (fun j => I * (d j - root (2 * m) j) * (η j : ℂ) + (c j - h j)) ≤
        ε ^ 2 * (pairEnergy (by omega) (fun j => (η j : ℂ)) + pairEnergy (by omega) h))
    (hacc : (∑ j, ‖a j‖) ≤
      K * (pairEnergy (by omega) (fun j => (η j : ℂ)) + pairEnergy (by omega) h)) :
    second z (fun j => I * d j * (η j : ℂ) + c j)
      (fun j => -d j * (η j : ℂ) ^ 2 + a j) ≤
        -pairEnergy (by omega) h / 32 - 2 * pairEnergy (by omega) (fun j => (η j : ℂ)) +
        errorCoefficient (2 * m) δ ε G K r *
          (pairEnergy (by omega) (fun j => (η j : ℂ)) + pairEnergy (by omega) h) := by
  let E := pairEnergy (by omega : 0 < 2 * m) (fun j => (η j : ℂ))
  let A := pairEnergy (by omega : 0 < 2 * m) h
  have hE : 0 ≤ E := pairEnergy_nonneg _ _
  have hA : 0 ≤ A := pairEnergy_nonneg _ _
  let u : Fin (2 * m) → ℂ := fun j => I * root (2 * m) j * (η j : ℂ) + h j
  let e : Fin (2 * m) → ℂ :=
    fun j => I * (d j - root (2 * m) j) * (η j : ℂ) + (c j - h j)
  have hu : pairEnergy (by omega) u ≤ 12 * (E + A) :=
    reference_velocity_energy (by omega) η h hmean
  have hq := quadratic_perturbation (by omega : 4 ≤ 2 * m) z u e hδ hδsmall hε
    (add_nonneg hE hA) hrelative hu hvelocity
  have hve : u + e = (fun j => I * d j * (η j : ℂ) + c j) := by
    funext j
    dsimp [u, e]
    ring
  rw [hve] at hq
  have hangular := regular_angular_error (by omega : 2 ≤ 2 * m) z d η hG hr0 hmean hd hr hg
  have hcenter := halfPeriodic_acceleration_error (by omega) z a ha hg
  have hcenter' := mul_le_mul_of_nonneg_left hacc hG
  have hreference := reference_negative hm η h a hη hh ha
  rw [second_eq_quadratic_add_acceleration] at hreference ⊢
  have he (w v : Fin (2 * m) → ℂ) :
      accelerationPairing w (fun j => -v j * (η j : ℂ) ^ 2 + a j) =
      accelerationPairing w (fun j => -v j * (η j : ℂ) ^ 2) + accelerationPairing w a :=
    accelerationPairing_add w _ a
  rw [he, regular_pairing_zero (by omega) a ha, add_zero] at hreference
  rw [he]
  have hq' := (le_abs_self _).trans hq
  have hang' := (le_abs_self _).trans hangular
  have hc' := (le_abs_self _).trans (hcenter.trans hcenter')
  have hcoef : 0 ≤ 4 * (G / (2 * m : ℕ) + 2 * r) := by positivity
  have hextra := mul_nonneg hcoef hA
  change _ ≤ -A / 32 - 2 * E + errorCoefficient (2 * m) δ ε G K r * (E + A)
  change quadratic (root (2 * m)) u + _ ≤ -A / 32 - 2 * E at hreference
  change _ ≤ 4 * (G / (2 * m : ℕ) + 2 * r) * E at hang'
  unfold errorCoefficient
  nlinarith only [hreference, hq', hang', hc', hextra]

theorem absorb_error {A E F ρ : ℝ} (hA : 0 ≤ A) (hE : 0 ≤ E) (hρ : ρ ≤ 1 / 64)
    (hF : F ≤ -A / 32 - 2 * E + ρ * (E + A)) : F ≤ -A / 64 - E := by
  have hm := mul_le_mul_of_nonneg_right hρ (add_nonneg hE hA)
  nlinarith only [hm, hF, hE]

end
end StructuralNote.HessianComparison
