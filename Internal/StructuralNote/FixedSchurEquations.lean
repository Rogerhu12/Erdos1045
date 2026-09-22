import StructuralNote.FixedSchurContraction
import StructuralNote.FixedSchurEdgeGeometry
import StructuralNote.CommonTangentialReconstruction

/-! The normalized crossing map with the actual angle and free-center data.
Its fixed points give the positive branch and the prescribed diameter edges. -/

namespace StructuralNote.FixedSchurEquations

open Erdos1045.EventualExact Complex
open FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open EdgeCoordinates FixedSchurData FixedSchurLinear FixedSchurScalarRoot
open FixedSchurContraction FixedSchurEdgeGeometry CommonTangentialParameters

noncomputable section

def equationMap {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ q : Fin (2 * m) → ℝ) : Fin (2 * m) → ℝ :=
  crossingMap (epsilon (2 * m)) (X (by omega) θ) (Y (by omega) θ)
    (tangent (by omega) v) σ q

theorem tangent_antiperiodic {m : ℕ} (hm : 0 < m) (v : Fin (2 * m) → ℂ)
    (hv : HalfPeriodic hm v) : FiniteBox.Antiperiodic hm (tangent (by omega) v) := by
  intro j
  have he : edgeRatio (by omega) v (halfTurn hm j) = -edgeRatio (by omega) v j := by
    rw [edgeRatio_eq_difference, edgeRatio_eq_difference,
      difference_halfPeriodic hm v hv j, reference_difference, reference_difference,
      frame_halfTurn]
    simp only [mul_neg, div_neg]
  simp only [tangent, he, Complex.neg_re, mul_neg]

theorem equationMap_antiperiodic {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) (σ q : Fin (2 * m) → ℝ)
    (hθ : HalfPeriodic hm (fun j => (θ j : ℂ))) (hv : HalfPeriodic hm v)
    (hσ : FiniteBox.Antiperiodic hm σ) :
    FiniteBox.Antiperiodic hm (equationMap hm θ v σ q) :=
  crossingMap_antiperiodic hm _ _ _ _ _ _ (X_halfTurn hm θ hθ)
    (Y_halfTurn hm θ hθ) (tangent_antiperiodic hm v hv) hσ

theorem solution_antiperiodic {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) (σ q : Fin (2 * m) → ℝ)
    (hθ : HalfPeriodic hm (fun j => (θ j : ℂ))) (hv : HalfPeriodic hm v)
    (hσ : FiniteBox.Antiperiodic hm σ) (hfix : equationMap hm θ v σ q = q) :
    FiniteBox.Antiperiodic hm q := by
  rw [← hfix]
  exact equationMap_antiperiodic hm θ v σ q hθ hv hσ

theorem solution_positive_branch {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) (σ q : Fin (2 * m) → ℝ)
    (hσ : ∀ j, σ j = 1 ∨ σ j = -1) (hfix : equationMap hm θ v σ q = q)
    (hsmall : ∀ j, |Y (by omega) θ j + σ j * epsilon (2 * m) *
      (tangent (by omega) v j + J q j)| < 2) (j : Fin (2 * m)) :
    0 < X (by omega) θ j + σ j * epsilon (2 * m) * q j ∧
      (X (by omega) θ j + σ j * epsilon (2 * m) * q j) ^ 2 +
      (Y (by omega) θ j + σ j * epsilon (2 * m) *
        (J q + tangent (by omega) v) j) ^ 2 = 4 := by
  have he := congrFun hfix j
  change rootValue (σ j) (epsilon (2 * m)) (X (by omega) θ j)
    (Y (by omega) θ j) (tangent (by omega) v j + J q j) = q j at he
  have hs := rootValue_spec (X := X (by omega) θ j) (hσ j)
    (epsilon_pos (show 2 ≤ 2 * m by omega)) (hsmall j)
  rw [he] at hs
  simpa only [Pi.add_apply, add_comm (J q j)] using hs

theorem positive_branch_solution {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) (σ q : Fin (2 * m) → ℝ)
    (hσ : ∀ j, σ j = 1 ∨ σ j = -1)
    (hsmall : ∀ j, |Y (by omega) θ j + σ j * epsilon (2 * m) *
      (tangent (by omega) v j + J q j)| < 2)
    (hpos : ∀ j, 0 < X (by omega) θ j + σ j * epsilon (2 * m) * q j)
    (hsq : ∀ j, (X (by omega) θ j + σ j * epsilon (2 * m) * q j) ^ 2 +
      (Y (by omega) θ j + σ j * epsilon (2 * m) *
        (J q + tangent (by omega) v) j) ^ 2 = 4) : equationMap hm θ v σ q = q := by
  funext j
  apply (rootValue_unique (hσ j) (epsilon_pos (show 2 ≤ 2 * m by omega))
    (hsmall j) (hpos j) _).symm
  simpa only [Pi.add_apply, add_comm (J q j)] using hsq j

theorem solution_selected_edge {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) (σ q : Fin (2 * m) → ℝ)
    (hvq : constraint (by omega) v = 0) (hσ : ∀ j, σ j = 1 ∨ σ j = -1)
    (hfix : equationMap (by omega) θ v σ q = q)
    (hsmall : ∀ j, |Y (by omega) θ j + σ j * epsilon (2 * m) *
      (tangent (by omega) v j + J q j)| < 2) (j : Fin (2 * m)) :
    ‖crossingVector hm θ (center q v) σ j‖ = 2 :=
  selected_crossing_edge_norm_eq_two hm θ q v σ hvq j
    (solution_positive_branch (by omega) θ v σ q hσ hfix hsmall j).2

end
end StructuralNote.FixedSchurEquations
