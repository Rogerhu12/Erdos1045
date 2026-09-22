import StructuralNote.MatchingActivityRadialNeighborhood

/-! A genuinely feasible smooth chart with independent unsaturated matching
radii at every sufficiently large actual maximizer. -/

namespace StructuralNote.MatchingActivityRadialFeasible

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization Filter
open LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open CommonClosureEnergy CommonFiberGeometry MatchingActivityRadialPair MatchingActivityRadialBounds
open MatchingActivityRadialClosure MatchingActivityRadialGeometry MatchingActivityRadialBase
open MatchingActivityRadialActual MatchingActivityRadialIntegration MatchingActivityRadialNeighborhood
open StrongPointwiseCoordinates StrongPointwiseSmallness MatchingActivityNonlocalPairs MatchingActivityNonlocal
open ActualCrossingGeometry NormalizedPolarRepresentation ExtremalPolarCenter SignedPressureRemainder
open SinglePressureEstimate StrongBudgetConsequences StrongObjectiveEstimate
open scoped Topology ContDiff
noncomputable section

def IsFeasibleRadialChart {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (a : ℂ) (g : (Fin m → ℝ) → ℂ) : Prop :=
  (∀ j, |σ j| ≤ 1) ∧ g r = 0 ∧ ContDiffAt ℝ ∞ g r ∧
  (∀ᶠ r' in 𝓝 r, closureFamily (parameters hm θ σ ν r') (g r') = 0) ∧
  ContDiffAt ℝ ∞ (fun r' => radialConfiguration hm θ σ ν r' (g r') a) r ∧
  (∀ᶠ r' in 𝓝 r, (∀ j, |r' j| ≤ 1) → DiameterAtMost 2 (radialConfiguration hm θ σ ν r' (g r') a))

theorem model_feasible_radial_chart {m : ℕ} (hm : 8 ≤ m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hz : DiameterAtMost 2 z)
    (hbounds : PointwiseBounds (m := m) (by omega) β u)
    (hbudget : radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
      DiscreteEnergy.realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / (2 * m : ℝ) ^ 2)
    (hsmallB : 4 * budgetConstant / (2 * m : ℝ) ≤ 1 / 1000000)
    (hsmallC : StrongPointwiseSteps.physicalStepConstant / (2 * m : ℝ) ≤ 1 / 1000)
    (hsmallR : StrongPointwiseRadial.radialErrorConstant / (2 * m : ℝ) ≤ 10 - Real.pi ^ 2)
    (hsmallb : 2 * budgetConstant / (2 * m : ℝ) ≤ 1 / 10) :
    ∃ (s ν : Fin m → ℝ) (g : (Fin m → ℝ) → ℂ),
      IsFeasibleRadialChart (by omega) (normalizedAngle m u) s ν (modelRadii m β u) (average (actualCenter m β u)) g ∧
      radialConfiguration (by omega) (normalizedAngle m u) s ν (modelRadii m β u) 0 (average (actualCenter m β u)) = normalizedPoint m β u ∧
      (∀ j, |ν j| ≤ 1 / (1000 * (2 * m : ℝ))) := by
  obtain ⟨s, ν, g, hs, hν, hi, hw, hg0, hg, hge⟩ := model_has_radial_chart hm h hz hbounds hbudget hsmallB hsmallC hsmallR
  obtain ⟨hθ, _, _⟩ := model_nonlocal_smallness hm h hz hbounds hbudget hsmallB hsmallC hsmallR
  have hhalf : HalfPeriodic (by omega) (fun j => (normalizedAngle m u j : ℂ)) := by
    intro j
    exact congrArg Complex.ofReal (normalizedAngle_halfPeriodic (by omega) u h.periodic j)
  have hr := model_radii_bounds hm h hz hbounds hsmallB
  have hp (j : Fin m) : 0 < (pair (halfAngle (by omega) (normalizedAngle m u) j)
      (modelRadii m β u j) (modelRadii m β u (nextIndex (by omega) j))).re := by
    have ha := small_half_angle hm (normalizedAngle m u) hθ j
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (pair_re_ge_one ha.2.1 (hr j).1 (hr _).1)
  have ht (j : Fin m) : |ν j| < 2 := by
    have hn : (16 : ℝ) ≤ 2 * m := by exact_mod_cast (show 16 ≤ 2 * m by omega)
    have hs' : 1 / (1000 * (2 * m : ℝ)) < 2 := by
      apply (div_lt_iff₀ (by positivity : 0 < 1000 * (2 * m : ℝ))).2
      nlinarith
    exact (hν j).trans_lt hs'
  have he : radialConfiguration (by omega) (normalizedAngle m u) s ν (modelRadii m β u) 0 (average (actualCenter m β u)) =
      normalizedPoint m β u := by
    rw [radialConfiguration_base (by omega) _ _ _ _ _ (actualCenter_halfPeriodic (by omega) β u h.periodic) hi,
      model_vertices (by omega) β u h.periodic]
  have hfar (j k : Fin (2 * m)) (hk₁ : k.val ≠ m - 1) (hk₂ : k.val ≠ m) (hk₃ : k.val ≠ m + 1) :
      ‖radialConfiguration (by omega) (normalizedAngle m u) s ν (modelRadii m β u) 0 (average (actualCenter m β u))
          (cyclicAdvance j k.val) -
        radialConfiguration (by omega) (normalizedAngle m u) s ν (modelRadii m β u) 0 (average (actualCenter m β u)) j‖ < 2 := by
    rw [he, ← model_normalized_distance h]
    exact model_nonlocal_offset_strict hm k.isLt ⟨hk₁, hk₂, hk₃⟩ h hz hbounds hbudget hsmallB hsmallC hsmallR hsmallb j
  obtain ⟨hf, hfe⟩ := eventually_diameter (by omega) (normalizedAngle m u) s ν (modelRadii m β u)
    (average (actualCenter m β u)) g hhalf hs hg0 hg hge hp ht hw hfar
  exact ⟨s, ν, g, ⟨hs, hg0, hg, hge, hf, hfe⟩, he, hν⟩

/-- Every sufficiently large actual maximizer has a feasible smooth radial
chart; matching saturation is not a hypothesis of this statement. -/
theorem eventual_diameter_feasible_radial_chart :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z : Points (2 * m), ExtremalNormalization.DiameterExtremal z →
      ∃ (hm : 0 < m) (σ : Equiv.Perm (Fin (2 * m))) (α β : ℂ) (u : ℕ → ℂ) (η : ℝ)
        (s ν : Fin m → ℝ) (g : (Fin m → ℝ) → ℂ),
        NormalizedRelativeEdgeModel z σ α β u η ∧
        IsFeasibleRadialChart hm (normalizedAngle m u) s ν (modelRadii m β u) (average (actualCenter m β u)) g ∧
        radialConfiguration hm (normalizedAngle m u) s ν (modelRadii m β u) 0 (average (actualCenter m β u)) = normalizedPoint m β u ∧
        (∀ j, 3 / 4 ≤ modelRadii m β u j ∧ modelRadii m β u j ≤ 1) := by
  obtain ⟨m₀, h₀⟩ := eventual_diameter_pointwise_coordinates
  obtain ⟨n₁, h₁⟩ := eventually_atTop.1 eventual_coefficients_small
  refine ⟨max (max m₀ n₁) 8, ?_⟩
  intro m hm z hz
  obtain ⟨hmp, σ, α, β, u, η, h, _, _, hbudget, hbounds⟩ := h₀ m (by omega) z hz
  have hs := h₁ (2 * m) (by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hs
  obtain ⟨s, ν, g, hf, he, _⟩ := model_feasible_radial_chart (by omega) h hz.1 hbounds hbudget
    hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2
  exact ⟨hmp, σ, α, β, u, η, s, ν, g, h, hf, he, model_radii_bounds (by omega) h hz.1 hbounds hs.2.1⟩

end
end StructuralNote.MatchingActivityRadialFeasible
