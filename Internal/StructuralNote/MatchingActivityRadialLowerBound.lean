import StructuralNote.MatchingActivityRadialObjectiveFirst
import StructuralNote.MatchingActivityRadialGradient

/-! A fixed positive linear radial gain, with only logarithmic and square-root
errors. This avoids the stronger logarithmic center-velocity energy estimate. -/

namespace StructuralNote.MatchingActivityRadialLowerBound

open Erdos1045 Erdos1045.EventualExact Complex Configuration
open FiniteFourierLift FourierMultiplier SchurSpectrum SchurLift LensClosure
open ActualCrossingGeometry ExtremalPolarCenter NormalizedPolarRepresentation SignedPressureRemainder StrongObjectiveEstimate SinglePressureEstimate
open StrongPointwiseCoordinates StrongPointwiseSteps StrongBudgetConsequences
open CommonFiberGeometry CommonClosureEnergy MatchingActivityRadialGeometry MatchingActivityRadialActual
open MatchingActivityRadialIntegration MatchingActivityRadialFeasible MatchingActivityRadialClosure
open MatchingActivityRadialPair MatchingActivityRadialBounds MatchingActivityRadialVelocity
open MatchingActivityRadialSmallness MatchingActivityRadialPressure MatchingActivityRadialEnergy
open MatchingActivityRadialModelEnergy MatchingActivityRadialModelCenterError MatchingActivityRadialDiameterError
open MatchingActivityRadialObjectiveFirst MatchingActivityRadialGradient MatchingActivityRadialCenterFirst
open LocalGradient
open scoped BigOperators
noncomputable section

def lowerBound (n : ℕ) : ℝ := (n : ℝ) / 4 - 53 - 4 * configurationStepConstant * (1 + Real.log n) -
  12 * centerErrorConstant * Real.sqrt n

theorem sqrt_cubic_energy {n A : ℝ} (hn : 0 ≤ n) (hA : A ≤ 130 * n ^ 3) :
    Real.sqrt A ≤ 12 * n * Real.sqrt n := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hs := Real.sq_sqrt hn
  have hid : (12 * n * Real.sqrt n) ^ 2 = 144 * n ^ 3 := by rw [mul_pow, mul_pow, hs]; ring
  rw [hid]
  nlinarith [pow_nonneg hn 3]

theorem model_radial_derivative_lower {m : ℕ} (hm : 8 ≤ m) (β : ℂ) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) (hb : PointwiseBounds (m := m) (by omega) β u)
    (hθ : ∀ j, |normalizedAngle m u j| ≤ 1 / (1000 * (2 * m : ℝ)))
    (hstep : ∀ j, ‖difference (by omega) (actualCenter m β u) j‖ ≤ 1 / (1000 * (2 * m : ℝ)))
    (hbudget : radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
      DiscreteEnergy.realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / (2 * m : ℝ) ^ 2)
    (hpressure : ‖operator (2 * m) (polarConstraint (by omega) β u)‖ ≤ 31 * Real.pi / 64)
    (hsmallD : diameterStepConstant / (2 * m : ℝ) ≤ 1 / 2)
    (hsmallC : 2 * physicalStepConstant / (2 * m : ℝ) ≤ 1 / 2)
    (hsmallG : configurationStepConstant / (2 * m : ℝ) ≤ 1 / 2)
    (σ ν : Fin m → ℝ) (g : (Fin m → ℝ) → ℂ)
    (hchart : IsFeasibleRadialChart (by omega) (normalizedAngle m u) σ ν (modelRadii m β u)
      (average (actualCenter m β u)) g)
    (hbase : radialConfiguration (by omega) (normalizedAngle m u) σ ν (modelRadii m β u) 0
      (average (actualCenter m β u)) = normalizedPoint m β u)
    (hν : ∀ j, |ν j| ≤ 1 / (1000 * (2 * m : ℝ)))
    (hr : ∀ j, 3 / 4 ≤ modelRadii m β u j ∧ modelRadii m β u j ≤ 1) (i : Fin m) :
    lowerBound (2 * m) ≤
      (∑ j, inner ℝ (realGradient (normalizedPoint m β u) j) (directVelocity (by omega) (normalizedAngle m u) i j)) +
        centerFirst (modelDiameter m β u) (actualCenter m β u)
          (centerVelocity (by omega) (normalizedAngle m u) σ ν (modelRadii m β u) g i) := by
  let θ := normalizedAngle m u
  let r := modelRadii m β u
  let a := average (actualCenter m β u)
  let U := centerVelocity (show 0 < m by omega) θ σ ν r g i
  have hn0 : (0 : ℝ) < 2 * m := by positivity
  have hn16 : (16 : ℝ) ≤ 2 * m := by exact_mod_cast (show 16 ≤ 2 * m by omega)
  have hφ (j : Fin m) : |halfAngle (by omega) θ j| ≤ 1 / 4 := (small_half_angle hm θ hθ j).2.1
  have hp (j : Fin m) : 1 ≤ (pair (halfAngle (by omega) θ j) (r j) (r (nextIndex (by omega) j))).re :=
    pair_re_ge_one (hφ j) (hr j).1 (hr _).1
  have hphase := phaseHeight_scale hm θ r ν hr hθ hν
  have hphase' (j : Fin m) : |radialPhase (by omega) θ r j - LensClosure.midpoint m j| + |ν j| ≤ 1 / 4 := by
    have hnum : 4 / (2 * m : ℝ) ≤ 1 / 4 := (div_le_iff₀ hn0).2 (by linarith)
    exact (hphase j).trans hnum
  have hν' (j : Fin m) : |ν j| ≤ 1 / 4 := by linarith [hphase' j, abs_nonneg (radialPhase (by omega) θ r j - LensClosure.midpoint m j)]
  have ht (j : Fin m) : ν j ^ 2 < 4 := by nlinarith [(abs_le.mp (hν' j)).1, (abs_le.mp (hν' j)).2]
  have hbody := chart_body_small hm θ σ ν r a g (actualCenter m β u) hchart
    (hbase.trans (model_vertices (by omega) β u hu).symm) hstep
  have hrabs (j : Fin m) : |r j| ≤ 1 := abs_le.mpr ⟨by linarith [(hr j).1], (hr j).2⟩
  have hU := centerVelocity_halfPeriodic (show 0 < m by omega) θ σ ν r a g i hchart
    (fun j => lt_of_lt_of_le (by norm_num) (hp j)) ht
  have henergy := centerVelocity_energy_bound (show 2 ≤ m by omega) θ σ ν r a g i hchart hp hrabs hφ hphase'
    (fun j => (hbody j).trans (by norm_num))
  have hUsqrt : Real.sqrt (pairEnergy (by omega) U) ≤ 12 * (2 * m : ℝ) * Real.sqrt (2 * m : ℝ) :=
    sqrt_cubic_energy hn0.le henergy
  have herr := model_centerFirst_error (show 2 ≤ m by omega) β u hu hb hθ hbudget hsmallD hsmallC U hU
  have herr' : |centerFirst (modelDiameter m β u) (actualCenter m β u) U -
      finitePairing (operator (2 * m) (polarConstraint (by omega) β u)) (constraint (by omega) U) / (2 * m : ℝ)| ≤
        12 * centerErrorConstant * Real.sqrt (2 * m : ℝ) := by
    apply (herr.trans (mul_le_mul_of_nonneg_left hUsqrt (div_nonneg centerErrorConstant_nonneg hn0.le))).trans_eq
    field_simp
  have hgpoint (j : Fin (2 * m)) : |operator (2 * m) (polarConstraint (by omega) β u) j| ≤ 31 * Real.pi / 64 := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (operator (2 * m) (polarConstraint (by omega) β u)) j).trans hpressure
  have hwork := pressure_work_coefficient hm θ σ ν r a g i hchart hp hrabs hφ hphase hbody _ hgpoint
  change |finitePairing (operator (2 * m) (polarConstraint (by omega) β u)) (constraint (by omega) U) / (2 * m : ℝ)| ≤ _ at hwork
  have hwork' : |finitePairing (operator (2 * m) (polarConstraint (by omega) β u)) (constraint (by omega) U) / (2 * m : ℝ)| ≤
      7 / 4 * (2 * m : ℝ) + 50 := by
    have hc : 9 * (31 * Real.pi / 64) / 8 ≤ 7 / 4 := by linarith [Real.pi_lt_d2]
    have hd : 32 * (31 * Real.pi / 64) ≤ 50 := by linarith [Real.pi_lt_d2]
    exact hwork.trans (add_le_add (mul_le_mul_of_nonneg_right hc hn0.le) hd)
  have hgrad := model_gradient_deviation (show 2 ≤ m by omega) β u hb hθ hsmallG
  have hdirect := directDerivative_lower (show 0 < m by omega) θ (normalizedPoint m β u) i hgrad (by positivity) hθ
  have hmain : (2 * (2 * m : ℝ) - 2 - 4 * configurationStepConstant * (1 + Real.log (2 * m : ℝ)) - 1 / 500) ≤
      ∑ j, inner ℝ (realGradient (normalizedPoint m β u) j) (directVelocity (by omega) θ i j) := by
    convert hdirect using 1
    field_simp
    ring
  dsimp only [lowerBound]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  change _ ≤ (∑ j, inner ℝ (realGradient (normalizedPoint m β u) j) (directVelocity (by omega) θ i j)) +
    centerFirst (modelDiameter m β u) (actualCenter m β u) U
  linarith [(abs_le.mp herr').1, (abs_le.mp hwork').1]

end
end StructuralNote.MatchingActivityRadialLowerBound
