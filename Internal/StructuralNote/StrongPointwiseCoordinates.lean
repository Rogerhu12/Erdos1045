import StructuralNote.StrongPointwiseSteps

/-! All pointwise scales in (6.21) for actual even-order global maximizers. -/

noncomputable section
open scoped BigOperators Topology

namespace StructuralNote.StrongPointwiseCoordinates

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization Filter GapRigidity
open SchurSpectrum SchurLift SchurLiftBounds DiscreteEnergy FiniteFourierLift FourierMultiplier
open ExtremalPolarCenter NormalizedPolarRepresentation SignedPressureRemainder StrongObjectiveEstimate
open SinglePressureEstimate StrongBudgetConsequences StrongPointwiseNormal StrongPointwiseSteps ActualCrossingGeometry

/-- Physical centers after the same translation and rotation as `normalizedPoint`. -/
def actualCenter (m : ℕ) (β : ℂ) (u : ℕ → ℂ) : Points (2 * m) :=
  fun j => circle (normalizedAngle m u j) * polarCenter m β u j

theorem actualCenter_eq_evenPart {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) :
    actualCenter m β u = AntipodalDecomposition.evenPart (halfTurn hm) (normalizedPoint m β u) := by
  funext j
  exact (actual_antipodal_parts hm β u hu j).2.symm

theorem actualCenter_norm (m : ℕ) (β : ℂ) (u : ℕ → ℂ) :
    ‖actualCenter m β u‖ = ‖polarCenter m β u‖ := by
  apply le_antisymm
  · apply pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.2
    intro j
    simpa only [actualCenter, norm_mul, circle_norm, one_mul] using norm_le_pi_norm (polarCenter m β u) j
  · apply pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.2
    intro j
    simpa only [actualCenter, norm_mul, circle_norm, one_mul] using norm_le_pi_norm (actualCenter m β u) j

def PointwiseBounds {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ) : Prop :=
  ‖polarCenter m β u‖ ≤ centerConstant / (2 * m) ∧
  ‖actualCenter m β u‖ ≤ centerConstant / (2 * m) ∧
  (∀ j, 0 ≤ radialDeficit m β u j ∧ radialDeficit m β u j ≤ budgetConstant / (2 * m : ℝ) ^ 3) ∧
  (∀ j, |normalizedAngle m u (successor (by omega) j) - normalizedAngle m u j| ≤
    angleConstant / (2 * m : ℝ) ^ 2) ∧
  (∀ j, |polarConstraint hm β u j| ≤ FiniteBox.amplitude (2 * m) + normalConstant / (2 * m)) ∧
  (∀ j, ‖difference (by omega) (polarCenter m β u) j‖ ≤ centerStepConstant / (2 * m : ℝ) ^ 2) ∧
  (∀ j, ‖difference (by omega) (actualCenter m β u) j‖ ≤ physicalStepConstant / (2 * m : ℝ) ^ 2)

theorem model_pointwise_coordinates {m : ℕ} (hm : 2 ≤ m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hz : DiameterAtMost 2 z)
    (hc : CenterBounds (m := m) (by omega) β u)
    (hq : meanSquare (polarConstraint (m := m) (by omega) β u) ≤ 65 * Real.pi ^ 2)
    (hbudget : radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
      realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / (2 * m : ℝ) ^ 2)
    (hsmall : normalConstant / (2 * m : ℝ) ≤ 1)
    (hnormal : ∀ j, |polarConstraint (m := m) (by omega) β u j| ≤
      FiniteBox.amplitude (2 * m) + normalConstant / (2 * m)) :
    PointwiseBounds (m := m) (by omega) β u := by
  obtain ⟨hcenter, hb, hangle⟩ := model_pointwise_bounds hm h hz hc hq hbudget
  have hτ : 0 ≤ radialMass m β u := by
    unfold radialMass
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => (hb j).1)
  have hE : 0 ≤ realEnergy (by omega) (normalizedAngle m u) := pairEnergy_nonneg (by omega) _
  have hD : pairEnergy (by omega) (polarCenter m β u - canonicalLift (polarConstraint (by omega) β u)) ≤
      budgetConstant / (2 * m : ℝ) ^ 2 := by
    change residualEnergy (by omega) (polarCenter m β u) ≤ _
    linarith only [hbudget, hτ, hE]
  have hfive (j : Fin (2 * m)) : |polarConstraint (m := m) (by omega) β u j| ≤ 5 := by
    have hh := WholeBoxObjective.amplitude_le_four (show 2 ≤ 2 * m by omega)
    linarith only [hnormal j, hh, hsmall]
  have hstep (j : Fin (2 * m)) : ‖difference (by omega) (polarCenter m β u) j‖ ≤
      centerStepConstant / (2 * m : ℝ) ^ 2 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using center_difference_bound (show 3 ≤ 2 * m by omega)
      (polarCenter m β u) (polarConstraint (by omega) β u) hfive
      (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hD) j
  refine ⟨hcenter, by rwa [actualCenter_norm], hb, hangle, hnormal, hstep, ?_⟩
  intro j
  change ‖difference (by omega) (fun j => circle (normalizedAngle m u j) * polarCenter m β u j) j‖ ≤
    physicalStepConstant / (2 * m : ℝ) ^ 2
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using derotation_difference_bound
    (show 0 < 2 * m by omega) (polarCenter m β u) (normalizedAngle m u)
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcenter)
    (fun k => by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hstep k)
    (fun k => by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hangle k) j

/-- Every genuine global maximizer has all the pointwise estimates in (6.21).
No crossing estimate, localization inequality, or energy bound is an input. -/
theorem eventual_diameter_pointwise_coordinates :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z : Points (2 * m), ExtremalNormalization.DiameterExtremal z →
      ∃ (hm : 0 < m) (σ : Equiv.Perm (Fin (2 * m))) (α β : ℂ) (u : ℕ → ℂ) (η : ℝ),
        NormalizedRelativeEdgeModel z σ α β u η ∧ CenterBounds hm β u ∧
        meanSquare (polarConstraint hm β u) ≤ 65 * Real.pi ^ 2 ∧
        radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
          realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / (2 * m : ℝ) ^ 2 ∧
        PointwiseBounds hm β u := by
  obtain ⟨m₀, h₀⟩ := eventual_diameter_normal_bound
  have hN : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 2 * m) tendsto_id
  have hs : ∀ᶠ m : ℕ in atTop, normalConstant / (2 * m : ℝ) ≤ 1 := by
    have hh := ((tendsto_const_div_atTop_nhds_zero_nat normalConstant).comp hN).eventually_le_const
      (by norm_num : (0 : ℝ) < 1)
    simpa only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat] using hh
  obtain ⟨m₁, h₁⟩ := eventually_atTop.1 hs
  refine ⟨max (max m₀ m₁) 2, ?_⟩
  intro m hm z hz
  obtain ⟨hmp, σ, α, β, u, η, h, hc, hq, hbudget, hn⟩ := h₀ m (by omega) z hz
  exact ⟨hmp, σ, α, β, u, η, h, hc, hq, hbudget,
    model_pointwise_coordinates (by omega) h hz.1 hc hq hbudget (h₁ m (by omega)) hn⟩

end StructuralNote.StrongPointwiseCoordinates
