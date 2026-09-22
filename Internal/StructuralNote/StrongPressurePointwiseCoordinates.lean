import StructuralNote.StrongPointwiseCoordinates

/-! The pressure gap and all pointwise scales for one common choice of
coordinates of each genuine even-order global maximizer. -/

noncomputable section
open scoped BigOperators Topology

namespace StructuralNote.StrongPressurePointwiseCoordinates

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization Filter
open SchurSpectrum SchurLift DiscreteEnergy FiniteFourierLift FourierMultiplier
open ExtremalPolarCenter NormalizedPolarRepresentation SignedPressureRemainder StrongObjectiveEstimate
open SinglePressureEstimate StrongBudgetConsequences StrongPointwiseNormal StrongPointwiseCoordinates

/-- The witnesses are selected once by the single-pressure theorem; both
pointwise refinements are then proved for those exact witnesses. -/
theorem eventual_diameter_pressure_pointwise_coordinates :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z : Points (2 * m), ExtremalNormalization.DiameterExtremal z →
      ∃ (hm : 0 < m) (σ : Equiv.Perm (Fin (2 * m))) (α β : ℂ) (u : ℕ → ℂ) (η : ℝ),
        NormalizedRelativeEdgeModel z σ α β u η ∧
        ‖operator (2 * m) (polarConstraint hm β u)‖ ≤ 31 * Real.pi / 64 ∧
        radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
          realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / (2 * m : ℝ) ^ 2 ∧
        PointwiseBounds hm β u := by
  obtain ⟨m₀, h₀⟩ := eventual_diameter_single_pressure
  have hN : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 2 * m) tendsto_id
  have hs : ∀ᶠ m : ℕ in atTop, normalConstant / (2 * m : ℝ) ≤ 1 := by
    have hh := ((tendsto_const_div_atTop_nhds_zero_nat normalConstant).comp hN).eventually_le_const
      (by norm_num : (0 : ℝ) < 1)
    simpa only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat] using hh
  obtain ⟨m₁, h₁⟩ := eventually_atTop.1 (strong_scale_small.and hs)
  refine ⟨max (max m₀ m₁) 8, ?_⟩
  intro m hm z hz
  obtain ⟨hmp, σ, α, β, u, η, h, hc, _, hq, hpressure, _, hbudget⟩ :=
    h₀ m (by omega) z hz
  have hsmall := h₁ m (by omega)
  have hbudget' : radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
      realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / (2 * m : ℝ) ^ 2 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbudget
  have hnormal := model_normal_bound (show 8 ≤ m by omega) h hz.1 hc hq hbudget'
    hsmall.1.1 hsmall.1.2.1 hsmall.1.2.2
  exact ⟨hmp, σ, α, β, u, η, h, hpressure, hbudget',
    model_pointwise_coordinates (by omega) h hz.1 hc hq hbudget' hsmall.2 hnormal⟩

end StructuralNote.StrongPressurePointwiseCoordinates
