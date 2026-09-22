import StructuralNote.ExplicitStrongCoordinates
import StructuralNote.ExplicitMatchingThreshold
import StructuralNote.MatchingActivityActualWordAlignment

/-! Matching and crossing saturation for genuine maximizers at a closed order threshold. -/

namespace StructuralNote.ExplicitMatchingCoordinates

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization
open NormalizedPolarRepresentation ExtremalPolarCenter SchurLiftBounds SchurSpectrum
open SinglePressureEstimate StrongObjectiveEstimate SignedPressureRemainder DiscreteEnergy
open FourierMultiplier SolScalarGap StrongPointwiseCoordinates StrongPointwiseSmallness
open FiniteBox CommonClosureEnergy
open MatchingActivityRadialActual MatchingActivityCrossingExclusivity
open MatchingActivityActualChartSelection MatchingActivityCrossingVariationSaturation
noncomputable section

def matchingThreshold : ℕ :=
  max ExplicitStrongCoordinates.orderThreshold
    (max ExplicitMatchingThreshold.pointwiseThreshold ExplicitMatchingThreshold.saturationThreshold)

def crossingThreshold : ℕ := max matchingThreshold ExplicitPressureThreshold.activeWordThreshold

theorem combined_budget_parts {m : ℕ} (hm : 0 < m)
    {z : Points (2 * m)} {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hz : DiameterAtMost 2 z)
    (hcombined : G hm (polarConstraint hm β u) + radialMass m β u +
      residualEnergy (by omega) (polarCenter m β u) +
      realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / (2 * m : ℝ) ^ 2) :
    (radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
      realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / (2 * m : ℝ) ^ 2) ∧
    G hm (polarConstraint hm β u) ≤ budgetConstant / (2 * m : ℝ) ^ 2 := by
  have hG0 := gap_nonneg hm (polarConstraint hm β u)
  have hτ : 0 ≤ radialMass m β u := by
    unfold radialMass
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun j _ => sub_nonneg.mpr
      (PolarRepresentation.model_radius_le_one hm h hz j)
  have hD := pairEnergy_nonneg (show 0 < 2 * m by omega)
    (polarCenter m β u - SchurLift.canonicalLift (polarConstraint hm β u))
  have hE := pairEnergy_nonneg (show 0 < 2 * m by omega)
    (fun j => (normalizedAngle m u j : ℂ))
  change 0 ≤ residualEnergy (by omega) (polarCenter m β u) at hD
  change 0 ≤ realEnergy (by omega) (normalizedAngle m u) at hE
  constructor <;> linarith only [hcombined, hG0, hτ, hD, hE]

def HasSaturatedCoordinates (m : ℕ) (z : Points (2 * m)) : Prop :=
  ∃ (hm : 0 < m) (σ : Equiv.Perm (Fin (2 * m))) (α β : ℂ) (u : ℕ → ℂ) (η : ℝ),
    NormalizedRelativeEdgeModel z σ α β u η ∧ CenterBounds hm β u ∧
    η ≤ 1 / 1024 ∧ meanSquare (polarConstraint hm β u) ≤ 65 * Real.pi ^ 2 ∧
    ‖operator (2 * m) (polarConstraint hm β u)‖ ≤ 31 * Real.pi / 64 ∧
    G hm (polarConstraint hm β u) + radialMass m β u +
      residualEnergy (by omega) (polarCenter m β u) +
      realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / (2 * m : ℝ) ^ 2 ∧
    PointwiseBounds hm β u ∧ (∀ i : Fin m, modelRadii m β u i = 1)

theorem diameter_matching_saturated {m : ℕ} {z : Points (2 * m)}
    (hz : ExtremalNormalization.DiameterExtremal z) (hn : matchingThreshold ≤ 2 * m) :
    HasSaturatedCoordinates m z := by
  have hsc := (le_max_left _ _).trans hn
  have hpw := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hsatN := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hm : 8 ≤ m := by
    have := (ExplicitMatchingThreshold.pointwise_scales hpw).1
    omega
  obtain ⟨hmp, σ, α, β, u, η, hmodel, hc, hη, hq, hpressure, hcombined⟩ :=
    ExplicitStrongCoordinates.diameter_scalar_gap_coordinates hz hsc
  have hbudget := (combined_budget_parts hmp hmodel hz.1 hcombined).1
  have hbounds := ExplicitMatchingThreshold.model_pointwise hm hpw hmodel hz.1 hc hq hbudget
  have hsat := ExplicitMatchingThreshold.model_saturated hm hsatN hmodel hz hpressure hbudget hbounds
  exact ⟨hmp, σ, α, β, u, η, hmodel, hc, hη, hq, hpressure, hcombined, hbounds, hsat⟩

theorem model_crossings_active {m : ℕ} (hm : 8 ≤ m)
    (hn : ExplicitPressureThreshold.activeWordThreshold ≤ 2 * m)
    {z : Points (2 * m)} {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hz : ExtremalNormalization.DiameterExtremal z)
    (hb : PointwiseBounds (m := m) (by omega) β u)
    (hcombined : G (m := m) (by omega) (polarConstraint (by omega) β u) + radialMass m β u +
      residualEnergy (by omega) (polarCenter m β u) +
      realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / (2 * m : ℝ) ^ 2)
    (hpressure : ‖operator (2 * m) (polarConstraint (by omega) β u)‖ ≤ 31 * Real.pi / 64)
    (hsat : ∀ i : Fin m, modelRadii m β u i = 1) (i : Fin m) :
    ((‖plusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
        (actualCenter m β u) i‖ = 2 ∧
      ‖minusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
        (actualCenter m β u) i‖ < 2) ∨
    (‖plusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
        (actualCenter m β u) i‖ < 2 ∧
      ‖minusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
        (actualCenter m β u) i‖ = 2)) ∧
    0 < activeHalfSign (by omega) (normalizedAngle m u) (modelRadii m β u)
      (actualCenter m β u) i * operator (2 * m) (polarConstraint (by omega) β u) (halfIndex i) := by
  have hs := ExplicitPressureThreshold.coefficients_small ((le_max_left _ _).trans hn)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hs
  obtain ⟨hbudget, hgap⟩ := combined_budget_parts (by omega) h hz.1 hcombined
  have hθ := (model_nonlocal_smallness hm h hz.1 hb hbudget hs.2.1 hs.2.2.1 hs.2.2.2.1).1
  have hactive := model_exactly_one_crossing_active hm h hz hb hθ hbudget hgap hpressure
    hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2 hsat
    (ExplicitPressureThreshold.pressure_margin ((le_max_right _ _).trans hn)) i
  exact ⟨hactive, ExplicitPressureThreshold.model_activeHalfSign_pressure_pos hm hn h hz hb
    hbudget hgap hpressure hsat i hactive⟩

theorem diameter_crossings_active {m : ℕ} {z : Points (2 * m)}
    (hz : ExtremalNormalization.DiameterExtremal z) (hn : crossingThreshold ≤ 2 * m) :
    ∃ (hm : 0 < m) (σ : Equiv.Perm (Fin (2 * m))) (α β : ℂ) (u : ℕ → ℂ) (η : ℝ),
      NormalizedRelativeEdgeModel z σ α β u η ∧ CenterBounds hm β u ∧
      η ≤ 1 / 1024 ∧ meanSquare (polarConstraint hm β u) ≤ 65 * Real.pi ^ 2 ∧
      ‖operator (2 * m) (polarConstraint hm β u)‖ ≤ 31 * Real.pi / 64 ∧
      G hm (polarConstraint hm β u) + radialMass m β u +
        residualEnergy (by omega) (polarCenter m β u) +
        realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / (2 * m : ℝ) ^ 2 ∧
      PointwiseBounds hm β u ∧ (∀ i : Fin m, modelRadii m β u i = 1) ∧
      (∀ i : Fin m,
        (‖plusCrossingVector hm (normalizedAngle m u) (modelRadii m β u)
            (actualCenter m β u) i‖ = 2 ∧
          ‖minusCrossingVector hm (normalizedAngle m u) (modelRadii m β u)
            (actualCenter m β u) i‖ < 2) ∨
        (‖plusCrossingVector hm (normalizedAngle m u) (modelRadii m β u)
            (actualCenter m β u) i‖ < 2 ∧
          ‖minusCrossingVector hm (normalizedAngle m u) (modelRadii m β u)
            (actualCenter m β u) i‖ = 2)) ∧
      FixedDualClassificationFinite.deficit hm
        (activePattern hm (normalizedAngle m u) (modelRadii m β u) (actualCenter m β u)) ≤
          budgetConstant / (2 * m : ℝ) ^ 2 := by
  have hmatching := (le_max_left _ _).trans hn
  have hword := (le_max_right _ _).trans hn
  obtain ⟨hmp, σ, α, β, u, η, hmodel, hc, hη, hq, hpressure, hcombined, hb, hsat⟩ :=
    diameter_matching_saturated hz hmatching
  have hs := ExplicitPressureThreshold.coefficients_small ((le_max_left _ _).trans hword)
  have hm : 8 ≤ m := by omega
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hs
  obtain ⟨hbudget, hgap⟩ := combined_budget_parts hmp hmodel hz.1 hcombined
  have hactive := fun i => (model_crossings_active hm hword hmodel hz hb hcombined hpressure hsat i).1
  have hθ := (model_nonlocal_smallness hm hmodel hz.1 hb hbudget hs.2.1 hs.2.2.1 hs.2.2.2.1).1
  have hdef := MatchingActivityActualWordAlignment.model_activePattern_deficit_le_gap hm hmodel hz
    hb hθ hbudget hgap hpressure hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2
    hsat (ExplicitPressureThreshold.pressure_margin ((le_max_right _ _).trans hword)) hactive
  exact ⟨hmp, σ, α, β, u, η, hmodel, hc, hη, hq, hpressure, hcombined, hb, hsat,
    hactive, hdef⟩

end
end StructuralNote.ExplicitMatchingCoordinates
