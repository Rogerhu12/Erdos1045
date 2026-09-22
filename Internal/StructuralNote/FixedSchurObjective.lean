import StructuralNote.FixedSchurEdgeGeometry
import StructuralNote.GeometricRelativeRemainder

/-! Exact objective splitting in the fixed-Schur coordinates.

`F` is the actual logarithm of the finite Vandermonde discriminant.  The
remainder below subtracts the regular-background pair potential, whereas the
older `GeometricRelativeRemainder.objectiveRemainder` subtracts its quadratic
form in the reference configuration.  Both quantities are related explicitly
below.
-/

namespace StructuralNote.FixedSchurObjective

open scoped BigOperators

open Erdos1045
open Erdos1045.Configuration
open Erdos1045.EventualExact
open Erdos1045.EventualExact.FiniteBox
open Erdos1045.EventualExact.FourierMultiplier
open Erdos1045.EventualExact.SchurLift
open Erdos1045.EventualExact.SchurSpectrum
open StructuralNote.CommonFiberGeometry
open StructuralNote.FixedSchurEdgeGeometry
open StructuralNote.FixedSchurLinear
open StructuralNote.EdgeCoordinates
open StructuralNote.GeometricRelativeRemainder

noncomputable section

def F {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  Real.log (Configuration.discriminant z)

def displacedVertices {n : ℕ} (θ : Fin n → ℝ) (C : Fin n → ℂ) : Fin n → ℂ :=
  fun j => diameterVector θ j + C j

def newRemainder {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) (C : Fin n → ℂ) : ℝ :=
  F (displacedVertices θ C) - F (diameterVector θ) - pairPotential hn C

theorem newRemainder_eq_gain_sub_pairPotential {n : ℕ} (hn : 0 < n)
    (θ : Fin n → ℝ) (C : Fin n → ℂ) :
    newRemainder hn θ C =
      GeometricRelativeRemainder.gain (diameterVector θ) C - pairPotential hn C := by
  unfold newRemainder F displacedVertices
  unfold GeometricRelativeRemainder.gain GeometricRelativeRemainder.configuration
  rfl

theorem newRemainder_eq_old_add_correction {n : ℕ} (hn : 0 < n)
    (θ : Fin n → ℝ) (C : Fin n → ℂ) :
    newRemainder hn θ C =
      GeometricRelativeRemainder.objectiveRemainder (diameterVector θ) C +
        GeometricRelativeRemainder.quadratic (diameterVector θ) C -
        pairPotential hn C := by
  rw [newRemainder_eq_gain_sub_pairPotential]
  unfold GeometricRelativeRemainder.objectiveRemainder
  ring

theorem newRemainder_sub_old_eq_quadratic_sub_pairPotential {n : ℕ}
    (hn : 0 < n) (θ : Fin n → ℝ) (C : Fin n → ℂ) :
    newRemainder hn θ C -
        GeometricRelativeRemainder.objectiveRemainder (diameterVector θ) C =
      GeometricRelativeRemainder.quadratic (diameterVector θ) C -
        pairPotential hn C := by
  rw [newRemainder_eq_old_add_correction]
  ring

theorem exact_split {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (q : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (hq : FiniteBox.Antiperiodic (by omega) q)
    (hv : HalfPeriodic (by omega) v)
    (hvq : constraint (by omega) v = 0) :
    F (fun j => vertex θ (center q v) j) - F (diameterVector θ) =
      normalizedBoxEnergy (operator (2 * m)) q + pairPotential (by omega) v +
        newRemainder (by omega) θ (center q v) := by
  change F (displacedVertices θ (center q v)) - F (diameterVector θ) =
    normalizedBoxEnergy (operator (2 * m)) q + pairPotential (by omega) v +
      (F (displacedVertices θ (center q v)) - F (diameterVector θ) -
        pairPotential (by omega) (center q v))
  rw [center_pairPotential hm q v hq hv hvq]
  ring

end
end StructuralNote.FixedSchurObjective
