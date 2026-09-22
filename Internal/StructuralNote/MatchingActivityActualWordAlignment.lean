import StructuralNote.MatchingActivityActualWordPressure
import StructuralNote.MatchingActivityActualWordDeficit

/-! Full-period pressure alignment and the resulting finite deficit for the
actual physical crossing word. -/

namespace StructuralNote.MatchingActivityActualWordAlignment

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization Filter
open LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum FiniteBox
open CommonClosureEnergy CommonTangentialParameters MatchingActivityRadialBounds
open MatchingActivityRadialGeometry
open MatchingActivityRadialActual MatchingActivityCrossingExclusivity
open MatchingActivityActualChartSelection MatchingActivityActualWordPressure
open MatchingActivityActualWordDeficit
open StrongPointwiseCoordinates StrongPointwiseSteps
open ActualCrossingGeometry NormalizedPolarRepresentation ExtremalPolarCenter
open SignedPressureRemainder SinglePressureEstimate StrongBudgetConsequences
open StrongObjectiveEstimate SolScalarGap
open FixedDualClassificationFinite
open scoped BigOperators Topology
noncomputable section

theorem sign_mul_eq_abs_of_mul_pos {σ x : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hpos : 0 < σ * x) : σ * x = |x| := by
  rcases hσ with hσ | hσ
  · have hx : 0 < x := by simpa only [hσ, one_mul] using hpos
    simpa only [hσ, one_mul] using (abs_of_pos hx).symm
  · rw [hσ] at hpos ⊢
    have hx : x < 0 := by nlinarith
    rw [abs_of_neg hx]
    ring

/-- The physical active word is aligned, at every full-period site, with the
pressure of the corrected polar constraint. -/
theorem model_activePattern_pressureAligned {m : ℕ} (hm : 8 ≤ m)
    {z : Points (2 * m)} {π : Equiv.Perm (Fin (2 * m))} {α β : ℂ}
    {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z π α β u η)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (hbounds : PointwiseBounds (m := m) (by omega) β u)
    (hθ : ∀ j, |normalizedAngle m u j| ≤ 1 / (1000 * (2 * m : ℝ)))
    (hbudget : radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
      DiscreteEnergy.realEnergy (by omega) (normalizedAngle m u) ≤
        budgetConstant / (2 * m : ℝ) ^ 2)
    (hgap : G (m := m) (by omega) (polarConstraint (by omega) β u) ≤
      budgetConstant / (2 * m : ℝ) ^ 2)
    (hpressure : ‖operator (2 * m) (polarConstraint (by omega) β u)‖ ≤
      31 * Real.pi / 64)
    (hsmallB : 4 * budgetConstant / (2 * m : ℝ) ≤ 1 / 1000000)
    (hsmallC : physicalStepConstant / (2 * m : ℝ) ≤ 1 / 1000)
    (hsmallR : StrongPointwiseRadial.radialErrorConstant / (2 * m : ℝ) ≤
      10 - Real.pi ^ 2)
    (hsmallb : 2 * budgetConstant / (2 * m : ℝ) ≤ 1 / 10)
    (hsmallD : MatchingActivityRadialDiameterError.diameterStepConstant /
      (2 * m : ℝ) ≤ 1 / 2)
    (hsat : ∀ j : Fin m, modelRadii m β u j = 1)
    (hmargin :
      8 * (31 * Real.pi / 64) +
          (9 / 2 : ℝ) * MatchingActivityRadialModelCenterError.centerErrorConstant *
            Real.sqrt (1 + Real.log (2 * m : ℕ)) <
        ((Real.log ((((2 * m) / 4 : ℕ) : ℝ) + 1) - 1) / 16 -
          budgetConstant / 2) / 8)
    (hactive : ∀ i : Fin m,
      (‖plusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ = 2 ∧
        ‖minusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ < 2) ∨
      (‖plusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ < 2 ∧
        ‖minusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ = 2)) :
    PressureAligned (by omega) (polarConstraint (by omega) β u)
      (activePattern (by omega) (normalizedAngle m u) (modelRadii m β u)
        (actualCenter m β u)) := by
  let q : Fin (2 * m) → ℝ := polarConstraint (by omega) β u
  let g : Fin (2 * m) → ℝ := operator (2 * m) q
  let s := activePattern (by omega) (normalizedAngle m u) (modelRadii m β u)
    (actualCenter m β u)
  have hfirst (i : Fin m) : patternSign s (halfIndex i) * g (halfIndex i) =
      |g (halfIndex i)| := by
    have hp := model_activeHalfSign_pressure_pos hm h hz hbounds hθ hbudget hgap hpressure
      hsmallB hsmallC hsmallR hsmallb hsmallD hsat hmargin i (hactive i)
    have hsigma : activeHalfSign (by omega) (normalizedAngle m u) (modelRadii m β u)
        (actualCenter m β u) i = 1 ∨
      activeHalfSign (by omega) (normalizedAngle m u) (modelRadii m β u)
        (actualCenter m β u) i = -1 := by
      unfold activeHalfSign
      split <;> simp
    dsimp [s, g, q]
    rw [patternSign_activePattern, activeRaw_halfIndex]
    exact sign_mul_eq_abs_of_mul_pos hsigma hp
  intro j
  obtain ⟨i, hj | hj⟩ := half_decomposition (by omega : 0 < m) j
  · rw [hj]
    exact hfirst i
  · rw [hj, patternSign_antiperiodic, operator_antiperiodic]
    simp only [neg_mul, mul_neg, neg_neg, abs_neg]
    exact hfirst i

/-- The actual physical crossing word has the manuscript-scale finite deficit,
without identifying the physical center with the corrected polar center. -/
theorem model_activePattern_deficit_le_gap {m : ℕ} (hm : 8 ≤ m)
    {z : Points (2 * m)} {π : Equiv.Perm (Fin (2 * m))} {α β : ℂ}
    {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z π α β u η)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (hbounds : PointwiseBounds (m := m) (by omega) β u)
    (hθ : ∀ j, |normalizedAngle m u j| ≤ 1 / (1000 * (2 * m : ℝ)))
    (hbudget : radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
      DiscreteEnergy.realEnergy (by omega) (normalizedAngle m u) ≤
        budgetConstant / (2 * m : ℝ) ^ 2)
    (hgap : G (m := m) (by omega) (polarConstraint (by omega) β u) ≤
      budgetConstant / (2 * m : ℝ) ^ 2)
    (hpressure : ‖operator (2 * m) (polarConstraint (by omega) β u)‖ ≤
      31 * Real.pi / 64)
    (hsmallB : 4 * budgetConstant / (2 * m : ℝ) ≤ 1 / 1000000)
    (hsmallC : physicalStepConstant / (2 * m : ℝ) ≤ 1 / 1000)
    (hsmallR : StrongPointwiseRadial.radialErrorConstant / (2 * m : ℝ) ≤
      10 - Real.pi ^ 2)
    (hsmallb : 2 * budgetConstant / (2 * m : ℝ) ≤ 1 / 10)
    (hsmallD : MatchingActivityRadialDiameterError.diameterStepConstant /
      (2 * m : ℝ) ≤ 1 / 2)
    (hsat : ∀ j : Fin m, modelRadii m β u j = 1)
    (hmargin :
      8 * (31 * Real.pi / 64) +
          (9 / 2 : ℝ) * MatchingActivityRadialModelCenterError.centerErrorConstant *
            Real.sqrt (1 + Real.log (2 * m : ℕ)) <
        ((Real.log ((((2 * m) / 4 : ℕ) : ℝ) + 1) - 1) / 16 -
          budgetConstant / 2) / 8)
    (hactive : ∀ i : Fin m,
      (‖plusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ = 2 ∧
        ‖minusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ < 2) ∨
      (‖plusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ < 2 ∧
        ‖minusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ = 2)) :
    deficit (by omega) (activePattern (by omega) (normalizedAngle m u)
        (modelRadii m β u) (actualCenter m β u)) ≤
      budgetConstant / (2 * m : ℝ) ^ 2 := by
  exact (deficit_le_gap_of_aligned (by omega) _ _
    (model_activePattern_pressureAligned hm h hz hbounds hθ hbudget hgap hpressure
      hsmallB hsmallC hsmallR hsmallb hsmallD hsat hmargin hactive)).trans hgap

end
end StructuralNote.MatchingActivityActualWordAlignment
