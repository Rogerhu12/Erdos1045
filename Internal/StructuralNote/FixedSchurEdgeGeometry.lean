import StructuralNote.FixedSchurLinear
import StructuralNote.FixedSchurData

/-! Exact edge identities for the fixed-Schur coordinates.

The first two lemmas identify the antipodal diameter and the two orientations
of an adjacent crossing.  The last lemmas transfer the selected-crossing
quadratic identity to the actual complex edge.  No assertion about other
nonlocal edges is made here.
-/

namespace StructuralNote.FixedSchurEdgeGeometry

open scoped BigOperators

open Complex
open Erdos1045.EventualExact
open Erdos1045.EventualExact.FiniteBox
open Erdos1045.EventualExact.FourierMultiplier
open Erdos1045.EventualExact.FiniteFourierLift
open Erdos1045.EventualExact.SchurLift
open Erdos1045.EventualExact.SchurSpectrum
open StructuralNote.CommonFiberGeometry
open StructuralNote.FixedSchurData
open StructuralNote.FixedSchurLinear
open StructuralNote.EdgeCoordinates

noncomputable section

def vertex {m : ℕ} (θ : Fin (2 * m) → ℝ) (C : Fin (2 * m) → ℂ)
    (j : Fin (2 * m)) : ℂ :=
  diameterVector θ j + C j

def crossingVector {m : ℕ} (hm : 2 ≤ m) (θ : Fin (2 * m) → ℝ) (C : Fin (2 * m) → ℂ)
    (σ : Fin (2 * m) → ℝ) (j : Fin (2 * m)) : ℂ :=
  diameterVector θ j + diameterVector θ (successor (by omega) j) +
    (σ j : ℂ) * (C (successor (by omega) j) - C j)

theorem vertex_antipodal_difference {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (q : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (hθ : HalfPeriodic (by omega) (fun j => (θ j : ℂ)))
    (hq : FiniteBox.Antiperiodic (by omega) q)
    (hv : HalfPeriodic (by omega) v) (j : Fin (2 * m)) :
    vertex θ (center q v) j - vertex θ (center q v) (halfTurn (by omega) j) =
      2 * diameterVector θ j := by
  have hC : HalfPeriodic (by omega) (center q v) :=
    center_halfPeriodic hm q v hq hv
  simp only [vertex, diameterVector_halfTurn (by omega) θ hθ, hC j]
  ring

theorem vertex_antipodal_norm {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (q : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (hθ : HalfPeriodic (by omega) (fun j => (θ j : ℂ)))
    (hq : FiniteBox.Antiperiodic (by omega) q)
    (hv : HalfPeriodic (by omega) v) (j : Fin (2 * m)) :
    ‖vertex θ (center q v) j - vertex θ (center q v) (halfTurn (by omega) j)‖ = 2 := by
  rw [vertex_antipodal_difference hm θ q v hθ hq hv j]
  rw [norm_mul, diameterVector_norm]
  norm_num

theorem crossingVector_eq_vertex_sub_plus {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (C : Fin (2 * m) → ℂ)
    (σ : Fin (2 * m) → ℝ) (hθ : HalfPeriodic (by omega) (fun j => (θ j : ℂ)))
    (hC : HalfPeriodic (by omega) C) (j : Fin (2 * m)) (hσ : σ j = 1) :
    crossingVector hm θ C σ j =
      vertex θ C (successor (by omega) j) - vertex θ C (halfTurn (by omega) j) := by
  simp only [crossingVector, vertex, diameterVector_halfTurn (by omega) θ hθ,
    hC j, hσ, Complex.ofReal_one]
  ring

theorem crossingVector_eq_vertex_sub_minus {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (C : Fin (2 * m) → ℂ)
    (σ : Fin (2 * m) → ℝ) (hθ : HalfPeriodic (by omega) (fun j => (θ j : ℂ)))
    (hC : HalfPeriodic (by omega) C) (j : Fin (2 * m)) (hσ : σ j = -1) :
    crossingVector hm θ C σ j =
      vertex θ C j - vertex θ C (halfTurn (by omega) (successor (by omega) j)) := by
  simp only [crossingVector, vertex,
    diameterVector_halfTurn (by omega) θ hθ (successor (by omega) j),
    hC (successor (by omega) j), hσ]
  norm_num
  ring

theorem selected_crossing_edge_norm_eq_two {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (q : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (σ : Fin (2 * m) → ℝ)
    (hvq : constraint (by omega) v = 0) (j : Fin (2 * m))
    (hsq :
      (X (by omega) θ j + σ j * epsilon (2 * m) * q j) ^ 2 +
          (Y (by omega) θ j + σ j * epsilon (2 * m) *
            (J q + tangent (by omega) v) j) ^ 2 = 4) :
    ‖crossingVector hm θ (center q v) σ j‖ = 2 := by
  have hsel := selected_crossing_norm_sq (by omega) θ q
    (J q + tangent (by omega) v) σ j
  have hdiff := center_difference hm q v hvq
  have hvec : crossingVector hm θ (center q v) σ j =
      diameterVector θ j + diameterVector θ (successor (by omega) j) +
        (σ j : ℂ) * (edgeIncrement q (J q + tangent (by omega) v) j) := by
    unfold crossingVector
    rw [show center q v (successor (by omega) j) - center q v j =
        difference (by omega) (center q v) j by rfl,
      hdiff]
  rw [← hvec] at hsel
  rw [hsq] at hsel
  nlinarith [norm_nonneg (crossingVector hm θ (center q v) σ j)]

theorem selected_crossing_plus_length {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (q : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (σ : Fin (2 * m) → ℝ)
    (hθ : HalfPeriodic (by omega) (fun j => (θ j : ℂ)))
    (hq : FiniteBox.Antiperiodic (by omega) q)
    (hv : HalfPeriodic (by omega) v)
    (hvq : constraint (by omega) v = 0) (j : Fin (2 * m))
    (hσ : σ j = 1)
    (hsq :
      (X (by omega) θ j + σ j * epsilon (2 * m) * q j) ^ 2 +
          (Y (by omega) θ j + σ j * epsilon (2 * m) *
            (J q + tangent (by omega) v) j) ^ 2 = 4) :
    ‖vertex θ (center q v) (successor (by omega) j) -
        vertex θ (center q v) (halfTurn (by omega) j)‖ = 2 := by
  have hC : HalfPeriodic (by omega) (center q v) :=
    center_halfPeriodic hm q v hq hv
  have hcross := selected_crossing_edge_norm_eq_two hm θ q v σ hvq j hsq
  rw [← crossingVector_eq_vertex_sub_plus hm θ (center q v) σ hθ hC j hσ]
  exact hcross

theorem selected_crossing_minus_length {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (q : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (σ : Fin (2 * m) → ℝ)
    (hθ : HalfPeriodic (by omega) (fun j => (θ j : ℂ)))
    (hq : FiniteBox.Antiperiodic (by omega) q)
    (hv : HalfPeriodic (by omega) v)
    (hvq : constraint (by omega) v = 0) (j : Fin (2 * m))
    (hσ : σ j = -1)
    (hsq :
      (X (by omega) θ j + σ j * epsilon (2 * m) * q j) ^ 2 +
          (Y (by omega) θ j + σ j * epsilon (2 * m) *
            (J q + tangent (by omega) v) j) ^ 2 = 4) :
    ‖vertex θ (center q v) j -
        vertex θ (center q v) (halfTurn (by omega) (successor (by omega) j))‖ = 2 := by
  have hC : HalfPeriodic (by omega) (center q v) :=
    center_halfPeriodic hm q v hq hv
  have hcross := selected_crossing_edge_norm_eq_two hm θ q v σ hvq j hsq
  rw [← crossingVector_eq_vertex_sub_minus hm θ (center q v) σ hθ hC j hσ]
  exact hcross

end
end StructuralNote.FixedSchurEdgeGeometry
