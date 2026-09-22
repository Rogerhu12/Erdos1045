import StructuralNote.FixedSchurEdgeGeometry

/-! Algebra for selected and unselected adjacent crossings. -/

namespace StructuralNote.FixedSchurAdjacentAlgebra

open Complex
open Erdos1045.EventualExact
open Erdos1045.EventualExact.FiniteBox
open Erdos1045.EventualExact.FourierMultiplier
open Erdos1045.EventualExact.FiniteFourierLift
open Erdos1045.EventualExact.SchurLift
open Erdos1045.EventualExact.SchurSpectrum
open StructuralNote.CommonFiberGeometry
open StructuralNote.FixedSchurData
open StructuralNote.FixedSchurEdgeGeometry
open StructuralNote.FixedSchurLinear
open StructuralNote.EdgeCoordinates

noncomputable section

theorem flip_square_identity (X Y ε σ q p : ℝ) :
    (X - σ * ε * q) ^ 2 + (Y - σ * ε * p) ^ 2 =
      (X + σ * ε * q) ^ 2 + (Y + σ * ε * p) ^ 2 -
        4 * σ * ε * (X * q + Y * p) := by
  ring

theorem unselected_square_le {X Y ε σ q p : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hε : 0 < ε) (hX : 1 ≤ X)
    (hq : 1 / 2 ≤ σ * q) (hYp : |Y * p| ≤ 1 / 4)
    (hselected : (X + σ * ε * q) ^ 2 + (Y + σ * ε * p) ^ 2 = 4) :
    (X - σ * ε * q) ^ 2 + (Y - σ * ε * p) ^ 2 ≤ 4 - ε := by
  rcases hσ with rfl | rfl
  · have hq0 : 0 ≤ q := by linarith
    have hXq : 1 / 2 ≤ X * q := by
      have hmul := mul_le_mul_of_nonneg_right hX hq0
      nlinarith
    have hYp_lower : -(1 / 4 : ℝ) ≤ Y * p := (abs_le.mp hYp).1
    have hcross : 1 / 4 ≤ X * q + Y * p := by
      linarith
    have hscaled := mul_le_mul_of_nonneg_left hcross (le_of_lt hε)
    have hflip := flip_square_identity X Y ε 1 q p
    nlinarith
  · have hq0 : 0 ≤ -q := by linarith
    have hXq : 1 / 2 ≤ X * (-q) := by
      have hmul := mul_le_mul_of_nonneg_right hX hq0
      nlinarith
    have hYp_upper : Y * p ≤ 1 / 4 := (abs_le.mp hYp).2
    have hcross : 1 / 4 ≤ (-1 : ℝ) * (X * q + Y * p) := by
      nlinarith
    have hscaled := mul_le_mul_of_nonneg_left hcross (le_of_lt hε)
    have hflip := flip_square_identity X Y ε (-1) q p
    nlinarith

theorem unselected_square_lt {X Y ε σ q p : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hε : 0 < ε) (hX : 1 ≤ X)
    (hq : 1 / 2 ≤ σ * q) (hYp : |Y * p| ≤ 1 / 4)
    (hselected : (X + σ * ε * q) ^ 2 + (Y + σ * ε * p) ^ 2 = 4) :
    (X - σ * ε * q) ^ 2 + (Y - σ * ε * p) ^ 2 < 4 := by
  have hle := unselected_square_le hσ hε hX hq hYp hselected
  linarith

theorem unselected_crossing_norm_lt_two {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (q : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (σ : Fin (2 * m) → ℝ)
    (_hθ : HalfPeriodic (by omega) (fun j => (θ j : ℂ)))
    (_hq : FiniteBox.Antiperiodic (by omega) q)
    (_hv : HalfPeriodic (by omega) v)
    (hvq : constraint (by omega) v = 0) (j : Fin (2 * m))
    (hσ : σ j = 1 ∨ σ j = -1)
    (hXj : 1 ≤ X (by omega) θ j)
    (hqj : 1 / 2 ≤ σ j * q j)
    (hYpj :
      |Y (by omega) θ j * (J q + tangent (by omega) v) j| ≤ 1 / 4)
    (hselected :
      (X (by omega) θ j + σ j * epsilon (2 * m) * q j) ^ 2 +
          (Y (by omega) θ j + σ j * epsilon (2 * m) *
            (J q + tangent (by omega) v) j) ^ 2 = 4) :
    ‖crossingVector hm θ (center q v) (fun k => -σ k) j‖ < 2 := by
  let p : Fin (2 * m) → ℝ := J q + tangent (by omega) v
  have heps : 0 < epsilon (2 * m) := epsilon_pos (show 2 ≤ 2 * m by omega)
  have hun := unselected_square_le hσ heps
    hXj hqj hYpj hselected
  have hselNorm := selected_crossing_norm_sq (by omega) θ q p
    (fun k => -σ k) j
  have hdiff := center_difference hm q v hvq
  have hvec : crossingVector hm θ (center q v) (fun k => -σ k) j =
      diameterVector θ j + diameterVector θ (successor (by omega) j) +
        ((-σ j : ℝ) : ℂ) * edgeIncrement q p j := by
    unfold crossingVector
    rw [show center q v (successor (by omega) j) - center q v j =
        difference (by omega) (center q v) j by rfl,
      hdiff]
  have hnormsq :
      ‖crossingVector hm θ (center q v) (fun k => -σ k) j‖ ^ 2 ≤
        4 - epsilon (2 * m) := by
    rw [hvec]
    rw [hselNorm]
    simpa [p, sub_eq_add_neg, Nat.mul_comm] using hun
  nlinarith [norm_nonneg (crossingVector hm θ (center q v) (fun k => -σ k) j)]

end
end StructuralNote.FixedSchurAdjacentAlgebra
