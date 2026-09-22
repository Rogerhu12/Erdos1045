import StructuralNote.MatchingActivityRadialDiameterError

/-! The actual center first-variation error has an inverse-order coefficient.
Together with the cubic radial-velocity energy bound, it is O(sqrt n). -/

namespace StructuralNote.MatchingActivityRadialModelCenterError

open Erdos1045 Erdos1045.EventualExact Complex
open FiniteFourierLift FourierMultiplier SchurSpectrum SchurLift LensClosure
open StrongPointwiseCoordinates StrongPointwiseSteps StrongBudgetConsequences
open ExtremalPolarCenter NormalizedPolarRepresentation SignedPressureRemainder StrongObjectiveEstimate SinglePressureEstimate
open GeometricRelativeRemainder SignedPressureAngular CommonFiberGeometry
open CommonFiberHessianGeometryChord MatchingActivityRadialModelEnergy
open MatchingActivityRadialDiameterError MatchingActivityRadialStepEnergy MatchingActivityRadialCenterError
open MatchingActivityNonlocalPairs
noncomputable section

def centerErrorConstant : ℝ := 64 * physicalStepConstant ^ 3 + 20 * diameterStepConstant * physicalStepConstant +
  2 * derotationConstant + 2 * Real.sqrt budgetConstant

theorem centerErrorConstant_nonneg : 0 ≤ centerErrorConstant := by
  unfold centerErrorConstant
  obtain ⟨hP, hK⟩ := constants_nonneg
  have := diameterStepConstant_nonneg
  positivity

theorem model_center_quotient {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ)
    (hb : PointwiseBounds hm β u) (p : Fin (2 * m) × Fin (2 * m)) :
    ‖quotient (actualCenter m β u) (root (2 * m)) p‖ ≤ physicalStepConstant / (2 * m : ℝ) := by
  have hn0 : (0 : ℝ) < 2 * m := by positivity
  have he := quotient_of_step (show 0 < 2 * m by omega) (actualCenter m β u)
    (div_nonneg constants_nonneg.1 (sq_nonneg _)) hb.2.2.2.2.2.2 p.1 p.2
  simp only [Nat.cast_mul, Nat.cast_ofNat] at he
  have heq : (2 * m : ℝ) / 4 * (physicalStepConstant / (2 * m : ℝ) ^ 2) = (physicalStepConstant / (2 * m : ℝ)) / 4 := by field_simp
  rw [heq] at he
  have hnon := div_nonneg constants_nonneg.1 hn0.le
  linarith

theorem coefficient_bound {n P K D B : ℝ} (hn : 1 ≤ n) (hP : 0 ≤ P) (_hK : 0 ≤ K)
    (_hD : 0 ≤ D) (_hB : 0 ≤ B) :
    (16 * (2 * P / n) ^ 2 + 20 * (D / n)) * P + 2 * (K / n) + 2 * (Real.sqrt B / n) ≤
      (64 * P ^ 3 + 20 * D * P + 2 * K + 2 * Real.sqrt B) / n := by
  have hn0 : 0 < n := by linarith
  have hn2 : n ≤ n ^ 2 := by nlinarith
  have hh : 64 * P ^ 3 / n ^ 2 ≤ 64 * P ^ 3 / n :=
    div_le_div_of_nonneg_left (by positivity) hn0 hn2
  have he : (16 * (2 * P / n) ^ 2 + 20 * (D / n)) * P + 2 * (K / n) + 2 * (Real.sqrt B / n) =
      64 * P ^ 3 / n ^ 2 + (20 * D * P + 2 * K + 2 * Real.sqrt B) / n := by ring
  calc
    _ = 64 * P ^ 3 / n ^ 2 + (20 * D * P + 2 * K + 2 * Real.sqrt B) / n := he
    _ ≤ 64 * P ^ 3 / n + (20 * D * P + 2 * K + 2 * Real.sqrt B) / n := add_le_add hh le_rfl
    _ = _ := by ring

theorem model_centerFirst_error {m : ℕ} (hm : 2 ≤ m) (β : ℂ) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) (hb : PointwiseBounds (m := m) (by omega) β u)
    (hθ : ∀ j, |normalizedAngle m u j| ≤ 1 / (1000 * (2 * m : ℝ)))
    (hbudget : radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
      DiscreteEnergy.realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / (2 * m : ℝ) ^ 2)
    (hsmallD : diameterStepConstant / (2 * m : ℝ) ≤ 1 / 2)
    (hsmallC : 2 * physicalStepConstant / (2 * m : ℝ) ≤ 1 / 2)
    (U : Fin (2 * m) → ℂ) (hU : HalfPeriodic (by omega) U) :
    |MatchingActivityRadialCenterFirst.centerFirst (modelDiameter m β u) (actualCenter m β u) U -
      finitePairing (operator (2 * m) (polarConstraint (by omega) β u)) (constraint (by omega) U) / (2 * m : ℝ)| ≤
        centerErrorConstant / (2 * m : ℝ) * Real.sqrt (pairEnergy (by omega) U) := by
  have hn0 : (0 : ℝ) < 2 * m := by positivity
  have hn1 : (1 : ℝ) ≤ 2 * m := by exact_mod_cast (show 1 ≤ 2 * m by omega)
  have hden := modelDiameter_quotient (show 0 < m by omega) β u hb hθ
  have hden' (p : Fin (2 * m) × Fin (2 * m)) : ‖quotient (modelDiameter m β u - root (2 * m)) (root (2 * m)) p‖ ≤ 1 / 2 := (hden p).trans hsmallD
  have hD : Function.Injective (modelDiameter m β u) := by
    have he := configuration_injective (root (2 * m)) (modelDiameter m β u - root (2 * m))
      (HessianAngularReference.root_injective (show 4 ≤ 2 * m by omega)) (fun p => (hden' p).trans_lt (by norm_num))
    have hid : GeometricRelativeRemainder.configuration (root (2 * m)) (modelDiameter m β u - root (2 * m)) = modelDiameter m β u := by
      funext j
      simp only [GeometricRelativeRemainder.configuration, Pi.sub_apply, add_sub_cancel]
    rwa [hid] at he
  have hc := PolarCenterNormalization.correctedCenter_halfPeriodic (show 0 < m by omega) (angles m u)
    (ExtremalPolarCenter.physicalCenter m β u) (angles_halfPeriodic (by omega) u hu)
    (physicalCenter_halfPeriodic (by omega) β u hu)
  change HalfPeriodic (by omega) (polarCenter m β u) at hc
  have hCq (p : Fin (2 * m) × Fin (2 * m)) : ‖quotient (actualCenter m β u) (modelDiameter m β u) p‖ ≤
      2 * physicalStepConstant / (2 * m : ℝ) := by
    have he := (quotient_true_le_twice (show 4 ≤ 2 * m by omega) (modelDiameter m β u) (actualCenter m β u) hden' p).trans
      (mul_le_mul_of_nonneg_left (model_center_quotient (by omega) β u hb p) (by norm_num : (0 : ℝ) ≤ 2))
    exact he.trans_eq (by ring)
  have hmain := centerFirst_schur_error hm (modelDiameter m β u) (actualCenter m β u) (polarCenter m β u) U
    hD (modelDiameter_antipodal (by omega) β u hu) (actualCenter_halfPeriodic (by omega) β u hu) hc hU
    (div_nonneg (mul_nonneg (by norm_num) constants_nonneg.1) hn0.le) hsmallC hCq
    (div_nonneg diameterStepConstant_nonneg hn0.le) hsmallD hden
  have hτ : 0 ≤ radialMass m β u := by
    unfold radialMass
    exact mul_nonneg hn0.le (Finset.sum_nonneg (fun j _ => (hb.2.2.1 j).1))
  have hE : 0 ≤ DiscreteEnergy.realEnergy (by omega) (normalizedAngle m u) := pairEnergy_nonneg (by omega) _
  have hres : residualEnergy (by omega) (polarCenter m β u) ≤ budgetConstant / (2 * m : ℝ) ^ 2 := by linarith only [hbudget, hτ, hE]
  have hressqrt : Real.sqrt (residualEnergy (by omega) (polarCenter m β u)) ≤ Real.sqrt budgetConstant / (2 * m : ℝ) := by
    have he := Real.sqrt_le_sqrt hres
    rwa [Real.sqrt_div budgetConstant_nonneg, Real.sqrt_sq hn0.le] at he
  have hcenter := model_center_sqrt_energy (show 0 < m by omega) β u hb
  have hderot := model_derotation_sqrt_energy (show 0 < m by omega) β u hb hθ
  have hcoef := coefficient_bound hn1 constants_nonneg.1 constants_nonneg.2 diameterStepConstant_nonneg budgetConstant_nonneg
  have hbound : ((16 * (2 * physicalStepConstant / (2 * m : ℝ)) ^ 2 + 20 * (diameterStepConstant / (2 * m : ℝ))) *
      Real.sqrt (pairEnergy (by omega) (actualCenter m β u)) + 2 * Real.sqrt (pairEnergy (by omega) (actualCenter m β u - polarCenter m β u)) +
        2 * Real.sqrt (residualEnergy (by omega) (polarCenter m β u))) ≤ centerErrorConstant / (2 * m : ℝ) := by
    apply le_trans _ hcoef
    apply add_le_add (add_le_add ?_ (mul_le_mul_of_nonneg_left hderot (by norm_num)))
      (mul_le_mul_of_nonneg_left hressqrt (by norm_num))
    exact mul_le_mul_of_nonneg_left hcenter (by have := diameterStepConstant_nonneg; positivity)
  exact hmain.trans (mul_le_mul_of_nonneg_right hbound (Real.sqrt_nonneg _))

end
end StructuralNote.MatchingActivityRadialModelCenterError
