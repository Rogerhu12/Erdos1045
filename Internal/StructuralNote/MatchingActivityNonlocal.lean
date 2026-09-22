import StructuralNote.MatchingActivityNonlocalPairs

/-! Distant offsets are inactive for every sufficiently large even maximizer,
without assuming matching saturation. -/

namespace StructuralNote.MatchingActivityNonlocal

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization Filter
open FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open StrongPointwiseCoordinates StrongPointwiseSmallness MatchingActivityNonlocalPairs
open ActualCrossingGeometry NormalizedPolarRepresentation ExtremalPolarCenter SignedPressureRemainder
open SinglePressureEstimate StrongBudgetConsequences StrongObjectiveEstimate
open scoped Topology
noncomputable section

theorem model_normalized_distance {m : ℕ} {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (i j : Fin (2 * m)) :
    ‖z (σ i) - z (σ j)‖ = ‖normalizedPoint m β u i - normalizedPoint m β u j‖ := by
  have he (j : Fin (2 * m)) : z (σ j) =
      (α + (β / (‖β‖ : ℂ)) * physicalTranslation m ‖β‖ u) +
      ((β / (‖β‖ : ℂ)) * PolarCenterEnergy.phase (-meanAngle m u)) * normalizedPoint m β u j := by
    have hh := model_normalized_coordinates h j
    rw [← ActualPressureGap.polarCenter_eq_normalizedCenter m β u] at hh
    simpa only [normalizedPoint, PolarCenterEnergy.phase, neg_neg, SignedPressureAngular.root,
      PolarRepresentation.reference, mul_assoc] using hh
  rw [he i, he j, show
    (α + (β / (‖β‖ : ℂ)) * physicalTranslation m ‖β‖ u) +
      ((β / (‖β‖ : ℂ)) * PolarCenterEnergy.phase (-meanAngle m u)) * normalizedPoint m β u i -
    ((α + (β / (‖β‖ : ℂ)) * physicalTranslation m ‖β‖ u) +
      ((β / (‖β‖ : ℂ)) * PolarCenterEnergy.phase (-meanAngle m u)) * normalizedPoint m β u j) =
      ((β / (‖β‖ : ℂ)) * PolarCenterEnergy.phase (-meanAngle m u)) *
        (normalizedPoint m β u i - normalizedPoint m β u j) by ring,
    norm_mul, normalizedRotation_norm h.scale_ne_zero, one_mul]

theorem model_nonlocal_offset_strict {m r : ℕ} (hm : 8 ≤ m) (hr : r < 2 * m)
    (hne : r ≠ m - 1 ∧ r ≠ m ∧ r ≠ m + 1)
    {z : Points (2 * m)} {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hz : DiameterAtMost 2 z)
    (hbounds : PointwiseBounds (m := m) (by omega) β u)
    (hbudget : radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
      DiscreteEnergy.realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / (2 * m : ℝ) ^ 2)
    (hsmallB : 4 * budgetConstant / (2 * m : ℝ) ≤ 1 / 1000000)
    (hsmallC : StrongPointwiseSteps.physicalStepConstant / (2 * m : ℝ) ≤ 1 / 1000)
    (hsmallR : StrongPointwiseRadial.radialErrorConstant / (2 * m : ℝ) ≤ 10 - Real.pi ^ 2)
    (hsmallb : 2 * budgetConstant / (2 * m : ℝ) ≤ 1 / 10) (j : Fin (2 * m)) :
    ‖z (σ (cyclicAdvance j r)) - z (σ j)‖ < 2 := by
  rw [model_normalized_distance h]
  by_cases hrm : r ≤ m
  · have hh := model_forward_strict hm (show 2 ≤ m - r by omega) (show m - r ≤ m by omega)
      h hz hbounds hbudget hsmallB hsmallC hsmallR hsmallb (cyclicAdvance j (m - (m - r)))
    rw [NonlocalFeasibility.advance_back_forward (show m - r ≤ m by omega),
      Nat.sub_sub_self hrm, norm_sub_rev] at hh
    exact hh
  · have hh := model_forward_strict hm (show 2 ≤ r - m by omega) (show r - m ≤ m by omega)
      h hz hbounds hbudget hsmallB hsmallC hsmallR hsmallb j
    rwa [Nat.add_sub_of_le (show m ≤ r by omega)] at hh

/-- At a genuine global maximizer, the only possible diameter offsets are
matching and the two adjacent crossings. This is proved before saturation. -/
theorem eventual_diameter_nonlocal_inactive :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z : Points (2 * m), ExtremalNormalization.DiameterExtremal z →
      ∃ (hm : 0 < m) (σ : Equiv.Perm (Fin (2 * m))) (α β : ℂ) (u : ℕ → ℂ) (η : ℝ),
        NormalizedRelativeEdgeModel z σ α β u η ∧ PointwiseBounds hm β u ∧
        ∀ (j : Fin (2 * m)) (r : ℕ), r < 2 * m → r ≠ m - 1 → r ≠ m → r ≠ m + 1 →
          ‖z (σ (cyclicAdvance j r)) - z (σ j)‖ < 2 := by
  obtain ⟨m₀, h₀⟩ := eventual_diameter_pointwise_coordinates
  obtain ⟨n₁, h₁⟩ := eventually_atTop.1 eventual_coefficients_small
  refine ⟨max (max m₀ n₁) 8, ?_⟩
  intro m hm z hz
  obtain ⟨hmp, σ, α, β, u, η, h, _, _, hbudget, hbounds⟩ := h₀ m (by omega) z hz
  have hs := h₁ (2 * m) (by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hs
  refine ⟨hmp, σ, α, β, u, η, h, hbounds, ?_⟩
  intro j r hr hminus hmatch hpos
  exact model_nonlocal_offset_strict (by omega) hr ⟨hminus, hmatch, hpos⟩ h hz.1 hbounds hbudget
    hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2 j

end
end StructuralNote.MatchingActivityNonlocal
