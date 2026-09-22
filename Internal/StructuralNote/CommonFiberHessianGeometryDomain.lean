import StructuralNote.CommonFiberHessianGeometryGradient
import StructuralNote.HessianAngularReference

/-! Relative denominators and injectivity of the actual common fiber. -/

namespace StructuralNote.CommonFiberHessianGeometryDomain

open Erdos1045 Erdos1045.EventualExact Complex LensClosure
open CommonClosureEnergy CommonTangentialParameters CommonDomainClosure CommonDomainRadius
open CommonFiberGeometry CommonFiberHessianGeometryChord SignedPressureAngular
open scoped BigOperators
noncomputable section

theorem relative_denominator_eq {n : ℕ} (z w : Fin n → ℂ) (i j : Fin n)
    (hij : w i ≠ w j) :
    (z i - z j) / (w i - w j) - 1 =
      GeometricRelativeRemainder.quotient (fun k => z k - w k) w (i, j) := by
  dsimp [GeometricRelativeRemainder.quotient]
  field_simp [sub_ne_zero.mpr hij]
  ring

theorem domain_relative_denominator {m : ℕ} (hm : 8 ≤ m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ)
    (hdom : InDomain (by omega) θ v) (hσ : ∀ j, |σ j| ≤ 1)
    (hξ : ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2)
    (hz : closure (phase (by omega) θ) (fun j => 2 * Real.cos (halfAngle (by omega) θ j)) σ (coordinates (by omega) v) ξ = 0)
    (horder : 10 * (logOrder (2 * m) : ℝ) + 1024 ≤ 2 * m)
    (i j : Fin (2 * m)) (hij : i ≠ j) :
    ‖(configuration (by omega) θ v σ ξ i - configuration (by omega) θ v σ ξ j) /
      (root (2 * m) i - root (2 * m) j) - 1‖ ≤
      300 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) := by
  have hw : Function.Injective (root (2 * m)) := HessianAngularReference.root_injective (by omega)
  rw [relative_denominator_eq _ _ i j (hw.ne hij)]
  exact domain_relative_chord hm θ v σ ξ hdom hσ hξ hz horder i j

theorem domain_configuration_injective {m : ℕ} (hm : 8 ≤ m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ)
    (hdom : InDomain (by omega) θ v) (hσ : ∀ j, |σ j| ≤ 1)
    (hξ : ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2)
    (hz : closure (phase (by omega) θ) (fun j => 2 * Real.cos (halfAngle (by omega) θ j)) σ (coordinates (by omega) v) ξ = 0)
    (horder : 10 * (logOrder (2 * m) : ℝ) + 1024 ≤ 2 * m)
    (hsmall : 300 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) < 1) :
    Function.Injective (configuration (by omega) θ v σ ξ) := by
  have he : GeometricRelativeRemainder.configuration (root (2 * m))
      (perturbation (by omega) θ v σ ξ) = configuration (by omega) θ v σ ξ := by
    funext j
    simp only [GeometricRelativeRemainder.configuration, perturbation, add_sub_cancel]
  rw [← he]
  apply GeometricRelativeRemainder.configuration_injective
    (root (2 * m)) (perturbation (by omega) θ v σ ξ)
    (HessianAngularReference.root_injective (by omega))
  intro p
  exact (domain_relative_chord hm θ v σ ξ hdom hσ hξ hz horder p.1 p.2).trans_lt hsmall

end
end StructuralNote.CommonFiberHessianGeometryDomain
