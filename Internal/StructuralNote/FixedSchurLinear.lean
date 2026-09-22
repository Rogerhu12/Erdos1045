import StructuralNote.EdgeCoordinates

/-! Exact linear coordinates around the canonical Schur lift.

The center is the sum of the canonical lift of an antiperiodic real
constraint and a half-periodic residual.  This file records only the exact
linear identities; no estimates or nonlinear coordinate changes are used.
-/

namespace StructuralNote.FixedSchurLinear

open scoped BigOperators

open Complex
open Erdos1045.EventualExact
open Erdos1045.EventualExact.FiniteBox
open Erdos1045.EventualExact.FourierMultiplier
open Erdos1045.EventualExact.FiniteFourierLift
open Erdos1045.EventualExact.SchurLift
open Erdos1045.EventualExact.SchurSpectrum
open StructuralNote.EdgeCoordinates

noncomputable section

def center {m : ℕ} (q : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) :
    Fin (2 * m) → ℂ :=
  canonicalLift q + v

def projection {m : ℕ} (hm : 2 ≤ m) (C : Fin (2 * m) → ℂ) :
    Fin (2 * m) → ℂ :=
  C - canonicalLift (constraint (by omega) C)

theorem normal_eq_constraint {m : ℕ} (hm : 2 ≤ m) (C : Fin (2 * m) → ℂ) :
    EdgeCoordinates.normal (by omega) C = constraint (by omega) C := by
  funext j
  simpa only [EdgeCoordinates.normal] using
    (constraint_eq_edgeImaginary (show 2 ≤ 2 * m by omega) C j).symm

theorem center_constraint {m : ℕ} (hm : 2 ≤ m) (q : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (hvq : constraint (by omega) v = 0) :
    constraint (by omega) (center q v) = q := by
  change constraint (by omega) (canonicalLift q + v) = q
  rw [constraint_add (show 2 ≤ 2 * m by omega),
    constraint_canonicalLift (show 3 ≤ 2 * m by omega), hvq, add_zero]

theorem projection_constraint {m : ℕ} (hm : 2 ≤ m) (C : Fin (2 * m) → ℂ) :
    constraint (by omega) (projection hm C) = 0 := by
  unfold projection
  rw [constraint_sub (show 2 ≤ 2 * m by omega),
    constraint_canonicalLift (show 3 ≤ 2 * m by omega), sub_self]

theorem projection_center {m : ℕ} (hm : 2 ≤ m) (q : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (hvq : constraint (by omega) v = 0) :
    projection hm (center q v) = v := by
  unfold projection
  rw [center_constraint hm q v hvq]
  change canonicalLift q + v - canonicalLift q = v
  abel

theorem center_mean_zero {m : ℕ} (hm : 2 ≤ m) (q : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (hvm : ∑ j, v j = 0) :
    (∑ j, center q v j) = 0 := by
  simp only [center, Pi.add_apply, Finset.sum_add_distrib,
    canonicalLift_mean_zero (show 0 < 2 * m by omega) q, hvm, add_zero]

theorem center_halfPeriodic {m : ℕ} (hm : 2 ≤ m) (q : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ)
    (hq : FiniteBox.Antiperiodic (by omega) q)
    (hv : HalfPeriodic (by omega) v) :
    HalfPeriodic (by omega) (center q v) := by
  intro j
  change canonicalLift q (halfTurn (by omega) j) + v (halfTurn (by omega) j) =
    canonicalLift q j + v j
  rw [canonicalLift_halfTurn hm q hq, hv j]

theorem center_pairPotential {m : ℕ} (hm : 2 ≤ m) (q : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ)
    (hq : FiniteBox.Antiperiodic (by omega) q)
    (hv : HalfPeriodic (by omega) v)
    (hvq : constraint (by omega) v = 0) :
    pairPotential (by omega) (center q v) =
      normalizedBoxEnergy (operator (2 * m)) q + pairPotential (by omega) v := by
  simpa only [center] using
    (geometric_orthogonal_decomposition hm q hq v hv hvq)

theorem tangent_add {m : ℕ} (hm : 2 ≤ m) (u w : Fin (2 * m) → ℂ) :
    EdgeCoordinates.tangent (by omega) (u + w) =
      EdgeCoordinates.tangent (by omega) u + EdgeCoordinates.tangent (by omega) w := by
  funext j
  simp only [EdgeCoordinates.tangent, edgeRatio_add, Pi.add_apply, Complex.add_re]
  ring

theorem canonicalLift_tangent {m : ℕ} (hm : 2 ≤ m) (q : Fin (2 * m) → ℝ) :
    EdgeCoordinates.tangent (by omega) (canonicalLift q) = J q := by
  have hclose : firstCoefficient (J q) = -I * firstCoefficient q :=
    firstCoefficient_J (show 3 ≤ 2 * m by omega) q
  have hdiffLift :
      difference (by omega) (lift q (J q)) = edgeIncrement q (J q) :=
    lift_difference (show 2 ≤ 2 * m by omega) q (J q) hclose
  have hedge : edgeIncrement q (J q) = SchurLift.increment q := by
    funext j
    simp only [EdgeCoordinates.edgeIncrement, SchurLift.increment, J]
    push_cast
    ring
  have hdiff : difference (by omega) (lift q (J q)) = SchurLift.increment q := by
    rw [hdiffLift, hedge]
  have huniq : lift q (J q) = canonicalLift q :=
    canonicalLift_unique (show 3 ≤ 2 * m by omega) q (lift q (J q))
      (lift_mean_zero (show 0 < 2 * m by omega) q (J q)) hdiff
  have hcoord := lift_coordinates (show 2 ≤ 2 * m by omega) q (J q) hclose
  rw [huniq] at hcoord
  exact hcoord.2

theorem center_normal {m : ℕ} (hm : 2 ≤ m) (q : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (hvq : constraint (by omega) v = 0) :
    EdgeCoordinates.normal (by omega) (center q v) = q := by
  calc
    EdgeCoordinates.normal (by omega) (center q v) =
        constraint (by omega) (center q v) := normal_eq_constraint hm _
    _ = q := center_constraint hm q v hvq

theorem center_tangent {m : ℕ} (hm : 2 ≤ m) (q : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) :
    EdgeCoordinates.tangent (by omega) (center q v) =
      J q + EdgeCoordinates.tangent (by omega) v := by
  change EdgeCoordinates.tangent (by omega) (canonicalLift q + v) = _
  rw [tangent_add hm, canonicalLift_tangent hm q]

theorem center_difference {m : ℕ} (hm : 2 ≤ m) (q : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (hvq : constraint (by omega) v = 0) :
    difference (by omega) (center q v) =
      edgeIncrement q (J q + EdgeCoordinates.tangent (by omega) v) := by
  have h := actual_increment (show 2 ≤ 2 * m by omega) (center q v)
  rw [center_normal hm q v hvq, center_tangent hm q v] at h
  exact h

end
end StructuralNote.FixedSchurLinear
