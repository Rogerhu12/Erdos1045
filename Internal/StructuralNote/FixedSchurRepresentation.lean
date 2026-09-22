import StructuralNote.FixedSchurProjectionDomain
import StructuralNote.FixedSchurChart

/-! Identification of an actual center with the selected fixed-Schur chart.
The selected crossing equalities and the positive branch are explicit inputs;
no actual-maximizer saturation statement is asserted here. -/

namespace StructuralNote.FixedSchurRepresentation

open Filter
open Erdos1045 Erdos1045.EventualExact
open FourierMultiplier FiniteFourierLift SchurSpectrum SchurLift
open CommonFiberGeometry EdgeCoordinates
open CommonDomainClosure FixedSchurData FixedSchurLinear FixedSchurEdgeGeometry
open FixedSchurDomainSmallness FixedSchurEquations FixedSchurChart
open FixedSchurExistence FixedSchurProjectionDomain
open scoped BigOperators

noncomputable section

theorem close_norm_le_five {m : ℕ} (hm : 2 ≤ m) (σ q : Fin (2 * m) → ℝ)
    (hσ : ∀ j, σ j = 1 ∨ σ j = -1)
    (hR : radius (2 * m) ≤ 1)
    (hclose : ‖q - baseWord σ‖ ≤ radius (2 * m)) :
    ‖q‖ ≤ 5 := by
  have hb := baseWord_norm_le_four (show 2 ≤ 2 * m by omega) hσ
  have hd := norm_sub_norm_le q (baseWord σ)
  linarith

theorem representation_of_selected_crossing {m : ℕ} (hm : 2 ≤ m)
    (s : FiniteBox.SignPattern (by omega)) (θ : Fin (2 * m) → ℝ)
    (C : Fin (2 * m) → ℂ)
    (_hθ : HalfPeriodic (by omega) (fun j => (θ j : ℂ)))
    (_hθmean : (∑ j, (θ j : ℂ)) = 0)
    (hC : HalfPeriodic (by omega) C) (hCmean : (∑ j, C j) = 0)
    (_hdom : InDomain (by omega) θ (projection hm C))
    (hclose : ‖constraint (by omega) C -
        baseWord (FiniteBox.patternSign s)‖ ≤ radius (2 * m))
    (hsmall : ∀ j, |Y (by omega) θ j + FiniteBox.patternSign s j *
      epsilon (2 * m) *
        (tangent (by omega) (projection hm C) j +
          J (constraint (by omega) C) j)| < 2)
    (hpos : ∀ j, 0 < X (by omega) θ j + FiniteBox.patternSign s j *
      epsilon (2 * m) * constraint (by omega) C j)
    (hcross : ∀ j, ‖crossingVector hm θ C (FiniteBox.patternSign s) j‖ = 2)
    (hunique : ∀ r : Fin (2 * m) → ℝ,
      ‖r - baseWord (FiniteBox.patternSign s)‖ ≤ radius (2 * m) →
      equationMap (by omega) θ (projection hm C) (FiniteBox.patternSign s) r = r →
      r = coordinate (by omega) s θ (projection hm C)) :
    constraint (by omega) C = coordinate (by omega) s θ (projection hm C) ∧
      C = center (coordinate (by omega) s θ (projection hm C))
        (projection hm C) ∧
      vertex θ C = FixedSchurChart.configuration (by omega) s θ
        (projection hm C) := by
  have hv := projection_parameterSpace hm hC hCmean
  have hvq := hv.2.2
  have hcenter : center (constraint (by omega) C) (projection hm C) = C :=
    center_projection hm C
  have hsq (j : Fin (2 * m)) :
      (X (by omega) θ j + FiniteBox.patternSign s j * epsilon (2 * m) *
          constraint (by omega) C j) ^ 2 +
        (Y (by omega) θ j + FiniteBox.patternSign s j * epsilon (2 * m) *
          (J (constraint (by omega) C) +
            tangent (by omega) (projection hm C)) j) ^ 2 = 4 := by
    have hsel := selected_crossing_norm_sq (by omega) θ
      (constraint (by omega) C) (J (constraint (by omega) C) +
        tangent (by omega) (projection hm C)) (FiniteBox.patternSign s) j
    have hdiff : C (successor (by omega) j) - C j =
        edgeIncrement (constraint (by omega) C)
          (J (constraint (by omega) C) +
            tangent (by omega) (projection hm C)) j := by
      calc
        C (successor (by omega) j) - C j =
            center (constraint (by omega) C) (projection hm C)
              (successor (by omega) j) -
              center (constraint (by omega) C) (projection hm C) j := by
                rw [hcenter]
        _ = difference (by omega)
            (center (constraint (by omega) C) (projection hm C)) j := rfl
        _ = edgeIncrement (constraint (by omega) C)
            (J (constraint (by omega) C) +
              tangent (by omega) (projection hm C)) j :=
          congrFun (center_difference hm (constraint (by omega) C)
            (projection hm C) hvq) j
    have hvec : crossingVector hm θ C (FiniteBox.patternSign s) j =
        diameterVector θ j + diameterVector θ (successor (by omega) j) +
          (FiniteBox.patternSign s j : ℂ) *
            (edgeIncrement (constraint (by omega) C)
              (J (constraint (by omega) C) +
                tangent (by omega) (projection hm C)) j) := by
      unfold crossingVector
      rw [hdiff]
    rw [← hvec] at hsel
    rw [hcross j] at hsel
    nlinarith
  have hfix : equationMap (by omega) θ (projection hm C)
      (FiniteBox.patternSign s) (constraint (by omega) C) =
        constraint (by omega) C :=
    positive_branch_solution (by omega) θ (projection hm C)
      (FiniteBox.patternSign s) (constraint (by omega) C)
      (FiniteBox.patternSign_is_sign s) hsmall hpos hsq
  have hcoord := hunique (constraint (by omega) C) hclose hfix
  have hcenter' : center (coordinate (by omega) s θ (projection hm C))
      (projection hm C) = C := by
    rw [← hcoord]
    exact hcenter
  refine ⟨hcoord, hcenter'.symm, ?_⟩
  funext j
  simp only [FixedSchurChart.configuration]
  rw [hcenter']

theorem eventually_representation_of_selected_crossing :
    ∀ᶠ m : ℕ in atTop,
      ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
        (θ : Fin (2 * m) → ℝ) (C : Fin (2 * m) → ℂ),
        HalfPeriodic (by omega) (fun j => (θ j : ℂ)) →
        (∑ j, (θ j : ℂ)) = 0 →
        HalfPeriodic (by omega) C →
        (∑ j, C j) = 0 →
        InDomain (by omega) θ (projection hm C) →
        ‖constraint (by omega) C -
            baseWord (FiniteBox.patternSign s)‖ ≤ radius (2 * m) →
        (∀ j, 0 < X (by omega) θ j + FiniteBox.patternSign s j *
          epsilon (2 * m) * constraint (by omega) C j) →
        (∀ j, ‖crossingVector hm θ C (FiniteBox.patternSign s) j‖ = 2) →
        constraint (by omega) C = coordinate (by omega) s θ (projection hm C) ∧
          C = center (coordinate (by omega) s θ (projection hm C))
            (projection hm C) ∧
          vertex θ C = FixedSchurChart.configuration (by omega) s θ
            (projection hm C) := by
  filter_upwards [eventual_coordinate_unique, eventual_ball_positive_input] with
    m huniq hinput
  intro hm s θ C hθ hθmean hC hCmean hdom hclose hpos hcross
  have hsmall := hinput (by omega) θ (projection hm C)
    (FiniteBox.patternSign s) hdom (FiniteBox.patternSign_is_sign s)
    (constraint (by omega) C) hclose
  exact representation_of_selected_crossing hm s θ C hθ hθmean hC hCmean hdom
    hclose hsmall hpos hcross (huniq (by omega) s θ (projection hm C) hdom)

end
end StructuralNote.FixedSchurRepresentation
