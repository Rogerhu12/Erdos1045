import StructuralNote.MatchingActivityRadialModelEnergy

/-! Chord control for the actual unsaturated antipodal diameters. -/

namespace StructuralNote.MatchingActivityRadialDiameterError

open Erdos1045 Erdos1045.EventualExact Complex
open FiniteFourierLift FourierMultiplier SchurSpectrum SchurLift LensClosure
open StrongPointwiseCoordinates StrongPointwiseSteps StrongBudgetConsequences
open ExtremalPolarCenter NormalizedPolarRepresentation SignedPressureRemainder StrongObjectiveEstimate SinglePressureEstimate
open GeometricRelativeRemainder SignedPressureAngular CommonFiberGeometry
open CommonFiberHessianGeometryChord MatchingActivityRadialModelEnergy
open MatchingActivityRadialActual MatchingActivityRadialGeometry
noncomputable section

def modelDiameter (m : ℕ) (β : ℂ) (u : ℕ → ℂ) : Fin (2 * m) → ℂ :=
  fun j => (PolarRepresentation.radius m ‖β‖ u j : ℂ) * diameterVector (normalizedAngle m u) j

def diameterStepConstant : ℝ := 1 + angleConstant + 2 * budgetConstant

theorem diameterStepConstant_nonneg : 0 ≤ diameterStepConstant := by
  unfold diameterStepConstant angleConstant
  have := budgetConstant_nonneg
  positivity

theorem modelDiameter_antipodal {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) (j : Fin (2 * m)) :
    modelDiameter m β u (halfTurn hm j) = -modelDiameter m β u j := by
  have hθ : HalfPeriodic hm (fun j => (normalizedAngle m u j : ℂ)) :=
    fun k => congrArg Complex.ofReal (normalizedAngle_halfPeriodic hm u hu k)
  simp only [modelDiameter, ← radiusFull_model hm β u hu, radiusFull_halfTurn,
    diameterVector_halfTurn hm _ hθ, mul_neg]

theorem modelDiameter_step {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ)
    (hb : PointwiseBounds hm β u)
    (hθ : ∀ j, |normalizedAngle m u j| ≤ 1 / (1000 * (2 * m : ℝ))) (j : Fin (2 * m)) :
    ‖difference (by omega) (modelDiameter m β u - root (2 * m)) j‖ ≤
      diameterStepConstant / (2 * m : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < 2 * m := by positivity
  have hn1 : (1 : ℝ) ≤ 2 * m := by exact_mod_cast (show 1 ≤ 2 * m by omega)
  let θ := normalizedAngle m u
  let b := radialDeficit m β u
  have hid : modelDiameter m β u - root (2 * m) = angularError θ - fun k => (b k : ℂ) * diameterVector θ k := by
    funext k
    simp only [modelDiameter, angularError, b, radialDeficit, ofReal_sub, ofReal_one, Pi.sub_apply, θ]
    ring
  have hpoint (k : Fin (2 * m)) : ‖(b k : ℂ) * diameterVector θ k‖ ≤ budgetConstant / (2 * m : ℝ) ^ 3 := by
    rw [norm_mul, diameterVector_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb.2.2.1 k).1]
    exact (hb.2.2.1 k).2
  have hs := angularError_step (show 0 < 2 * m by omega) θ j
  have hθprod := mul_le_mul_of_nonneg_left (hθ (successor (by omega) j)) (show 0 ≤ 8 / (2 * m : ℝ) by positivity)
  have hangle := hb.2.2.2.1 j
  change |CommonClosureEnergy.angleDifference (by omega) θ j| ≤ angleConstant / (2 * m : ℝ) ^ 2 at hangle
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hs
  have hdiff : ‖difference (by omega) (modelDiameter m β u - root (2 * m)) j‖ ≤
      8 / (2 * m : ℝ) * (1 / (1000 * (2 * m : ℝ))) + angleConstant / (2 * m : ℝ) ^ 2 +
        2 * budgetConstant / (2 * m : ℝ) ^ 3 := by
    rw [hid]
    have he : difference (show 0 < 2 * m by omega) (angularError θ - fun k => (b k : ℂ) * diameterVector θ k) j =
        difference (by omega) (angularError θ) j -
          ((b (successor (by omega) j) : ℂ) * diameterVector θ (successor (by omega) j) -
            (b j : ℂ) * diameterVector θ j) := by simp only [difference, Pi.sub_apply]; ring
    rw [he]
    have hn := (norm_sub_le (difference (show 0 < 2 * m by omega) (angularError θ) j) ((b (successor (by omega) j) : ℂ) * diameterVector θ (successor (by omega) j) - (b j : ℂ) * diameterVector θ j)).trans (add_le_add le_rfl (norm_sub_le _ _))
    have hA := hs.trans (add_le_add hθprod hangle)
    exact (hn.trans (add_le_add hA (add_le_add (hpoint (successor (by omega) j)) (hpoint j)))).trans_eq (by ring)
  have hbdiv : budgetConstant / (2 * m : ℝ) ^ 3 ≤ budgetConstant / (2 * m : ℝ) ^ 2 := by
    apply div_le_div_of_nonneg_left budgetConstant_nonneg (by positivity)
    nlinarith [sq_nonneg (2 * m : ℝ), mul_nonneg (sq_nonneg (2 * m : ℝ)) (show 0 ≤ (2 * m : ℝ) - 1 by linarith)]
  have hnum : 8 / (2 * m : ℝ) * (1 / (1000 * (2 * m : ℝ))) ≤ 1 / (2 * m : ℝ) ^ 2 := by
    field_simp
    norm_num
  have hbdiv' : 2 * budgetConstant / (2 * m : ℝ) ^ 3 ≤ 2 * budgetConstant / (2 * m : ℝ) ^ 2 := by
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hbdiv (by norm_num : (0 : ℝ) ≤ 2)
  unfold diameterStepConstant
  rw [add_div, add_div]
  linarith only [hdiff, hnum, hbdiv']

theorem modelDiameter_quotient {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ)
    (hb : PointwiseBounds hm β u)
    (hθ : ∀ j, |normalizedAngle m u j| ≤ 1 / (1000 * (2 * m : ℝ))) (p : Fin (2 * m) × Fin (2 * m)) :
    ‖quotient (modelDiameter m β u - root (2 * m)) (root (2 * m)) p‖ ≤
      diameterStepConstant / (2 * m : ℝ) := by
  have hn0 : (0 : ℝ) < 2 * m := by positivity
  have he := quotient_of_step (show 0 < 2 * m by omega) (modelDiameter m β u - root (2 * m))
    (div_nonneg diameterStepConstant_nonneg (sq_nonneg _)) (modelDiameter_step hm β u hb hθ) p.1 p.2
  simp only [Nat.cast_mul, Nat.cast_ofNat] at he
  have heq : (2 * m : ℝ) / 4 * (diameterStepConstant / (2 * m : ℝ) ^ 2) = (diameterStepConstant / (2 * m : ℝ)) / 4 := by field_simp
  rw [heq] at he
  have hnon := div_nonneg diameterStepConstant_nonneg hn0.le
  linarith

end
end StructuralNote.MatchingActivityRadialDiameterError
