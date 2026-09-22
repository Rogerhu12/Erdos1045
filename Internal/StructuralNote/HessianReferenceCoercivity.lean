import StructuralNote.HessianAngularReference
import StructuralNote.HessianAcceleration

/-! Exact negative reference Hessian on the actual angular and free tangential
parameter directions. Half-periodic center accelerations contribute zero. -/

namespace StructuralNote.HessianReferenceCoercivity

open Erdos1045 Erdos1045.EventualExact Complex SchurSpectrum
open LogDiscriminantSecondDerivative LogDiscriminantHessian HessianReferencePotential
open HessianAngularReference HessianAcceleration CommonTangentialParameters CommonFiberGeometry
open scoped BigOperators
noncomputable section

theorem accelerationPairing_add {n : ℕ} (z a b : Fin n → ℂ) :
    accelerationPairing z (a + b) = accelerationPairing z a + accelerationPairing z b := by
  simp only [accelerationPairing, Pi.add_apply, inner_add_right, Finset.sum_add_distrib]

theorem reference_negative {m : ℕ} (hm : 2 ≤ m) (η : Fin (2 * m) → ℝ)
    (h a : Fin (2 * m) → ℂ) (hη : HalfPeriodic (by omega) (fun j => (η j : ℂ)))
    (hh : ParameterSpace (by omega) h) (ha : HalfPeriodic (by omega) a) :
    second (root (2 * m)) (fun j => I * root (2 * m) j * (η j : ℂ) + h j)
      (fun j => -root (2 * m) j * (η j : ℂ) ^ 2 + a j) ≤
        -pairEnergy (by omega) h / 32 - 2 * pairEnergy (by omega) (fun j => (η j : ℂ)) := by
  have hw : diameterVector (fun _ : Fin (2 * m) => (0 : ℝ)) = root (2 * m) := by
    funext j
    simp only [diameterVector, LensClosure.unit, ofReal_zero, zero_mul, Complex.exp_zero,
      mul_one, FourierMultiplier.character, root]
  have hzero : HalfPeriodic (by omega : 0 < m) (fun _ : Fin (2 * m) => ((0 : ℝ) : ℂ)) := by
    intro j
    rfl
  have hadd := HessianAntipodal.angular_center_mixed_zero (by omega) (fun _ => 0) η h hzero hη hh.1
  rw [hw] at hadd
  have hang := angular_quadratic_acceleration (by omega : 4 ≤ 2 * m) η
  have hneg := kernel_negative hm h hh
  rw [second_eq_quadratic_add_acceleration, hadd]
  change _ + accelerationPairing (root (2 * m))
    ((fun j => -root (2 * m) j * (η j : ℂ) ^ 2) + a) ≤ _
  rw [accelerationPairing_add, regular_pairing_zero (by omega) a ha]
  linarith

end
end StructuralNote.HessianReferenceCoercivity
