import StructuralNote.MatchingActivityRadialBase

/-! The unsaturated radial closure chart at the actual localized maximizer. -/

namespace StructuralNote.MatchingActivityRadialActual

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization Filter
open LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open CommonClosureEnergy MatchingActivityRadialPair MatchingActivityRadialBounds
open MatchingActivityRadialClosure MatchingActivityRadialGeometry MatchingActivityRadialBase
open StrongPointwiseCoordinates StrongPointwiseSmallness MatchingActivityNonlocalPairs
open ActualCrossingGeometry NormalizedPolarRepresentation ExtremalPolarCenter SignedPressureRemainder
open SinglePressureEstimate StrongBudgetConsequences StrongObjectiveEstimate
open scoped Topology ContDiff
noncomputable section

def modelRadii (m : ℕ) (β : ℂ) (u : ℕ → ℂ) (j : Fin m) : ℝ :=
  PolarRepresentation.radius m ‖β‖ u j.val

theorem radiusFull_model {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) (j : Fin (2 * m)) :
    radiusFull hm (modelRadii m β u) j = PolarRepresentation.radius m ‖β‖ u j := by
  exact (CyclicAngles.periodic_mod _ (PolarRepresentation.radius_periodic hm ‖β‖ u hu) j.val).symm

theorem model_vertices {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) :
    vertices hm (normalizedAngle m u) (modelRadii m β u) (actualCenter m β u) =
      normalizedPoint m β u := by
  funext j
  rw [normalizedPoint_decomposition]
  simp only [vertices, radiusFull_model hm β u hu]

theorem model_radii_bounds {m : ℕ} (hm : 8 ≤ m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hz : DiameterAtMost 2 z)
    (hbounds : PointwiseBounds (m := m) (by omega) β u)
    (hsmall : 4 * budgetConstant / (2 * m : ℝ) ≤ 1 / 1000000) (j : Fin m) :
    3 / 4 ≤ modelRadii m β u j ∧ modelRadii m β u j ≤ 1 := by
  have hn : (16 : ℝ) ≤ 2 * m := by exact_mod_cast (show 16 ≤ 2 * m by omega)
  have hn0 : (0 : ℝ) < 2 * m := by positivity
  have hb := (hbounds.2.2.1 (CommonClosureEnergy.halfIndex j)).2
  have hpow : (2 * m : ℝ) ≤ (2 * m : ℝ) ^ 3 := by
    calc
      _ = (2 * m : ℝ) * 1 := by ring
      _ ≤ (2 * m : ℝ) * (2 * m : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (by nlinarith : (1 : ℝ) ≤ (2 * m : ℝ) ^ 2) hn0.le
      _ = _ := by ring
  have hdiv : budgetConstant / (2 * m : ℝ) ^ 3 ≤ budgetConstant / (2 * m : ℝ) :=
    div_le_div_of_nonneg_left budgetConstant_nonneg hn0 hpow
  have hquarter : budgetConstant / (2 * m : ℝ) ≤ 1 / 4 := by
    have he : 4 * budgetConstant / (2 * m : ℝ) = 4 * (budgetConstant / (2 * m : ℝ)) := by ring
    rw [he] at hsmall
    linarith
  constructor
  · change 1 - modelRadii m β u j ≤ _ at hb
    linarith
  · exact PolarRepresentation.model_radius_le_one (by omega) h hz (CommonClosureEnergy.halfIndex j)

/-- The chart retains the actual tangential heights, with zero initial closure
correction; no matching radius is required to equal one. -/
def HasRadialChart {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ) : Prop :=
  ∃ (σ ν : Fin m → ℝ) (g : (Fin m → ℝ) → ℂ),
    (∀ j, |σ j| ≤ 1) ∧
    (∀ j, |ν j| ≤ 1 / (1000 * (2 * m : ℝ))) ∧
    (∀ j, difference (by omega) (actualCenter m β u) (CommonClosureEnergy.halfIndex j) =
      radialIncrement hm (normalizedAngle m u) σ ν (modelRadii m β u) 0 j) ∧
    (∀ j, 0 < Lens.width (radialLength hm (normalizedAngle m u) (modelRadii m β u) j) (ν j)) ∧
    g (modelRadii m β u) = 0 ∧ ContDiffAt ℝ ∞ g (modelRadii m β u) ∧
    (∀ᶠ r' in 𝓝 (modelRadii m β u),
      closureFamily (parameters hm (normalizedAngle m u) σ ν r') (g r') = 0)

theorem model_has_radial_chart {m : ℕ} (hm : 8 ≤ m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hz : DiameterAtMost 2 z)
    (hbounds : PointwiseBounds (m := m) (by omega) β u)
    (hbudget : radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
      DiscreteEnergy.realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / (2 * m : ℝ) ^ 2)
    (hsmallB : 4 * budgetConstant / (2 * m : ℝ) ≤ 1 / 1000000)
    (hsmallC : StrongPointwiseSteps.physicalStepConstant / (2 * m : ℝ) ≤ 1 / 1000)
    (hsmallR : StrongPointwiseRadial.radialErrorConstant / (2 * m : ℝ) ≤ 10 - Real.pi ^ 2) :
    HasRadialChart (by omega : 0 < m) β u := by
  obtain ⟨hθ, hstep, _⟩ := model_nonlocal_smallness hm h hz hbounds hbudget hsmallB hsmallC hsmallR
  have hhalf : HalfPeriodic (by omega) (fun j => (normalizedAngle m u j : ℂ)) := by
    intro j
    exact congrArg Complex.ofReal (normalizedAngle_halfPeriodic (by omega) u h.periodic j)
  have hr := model_radii_bounds hm h hz hbounds hsmallB
  have hd : DiameterAtMost 2 (vertices (by omega) (normalizedAngle m u) (modelRadii m β u) (actualCenter m β u)) := by
    rw [model_vertices (by omega) β u h.periodic]
    exact model_diameter h hz
  obtain ⟨s, ν, hs, hν, hi, hw, hsmall, hz0⟩ := exists_base_coordinates hm
    (normalizedAngle m u) (modelRadii m β u) (actualCenter m β u) hhalf
    (actualCenter_halfPeriodic (by omega) β u h.periodic) hd hr hθ hstep
  have hp (j : Fin m) : 0 < (pair (halfAngle (by omega) (normalizedAngle m u) j)
      (modelRadii m β u j) (modelRadii m β u (nextIndex (by omega) j))).re := by
    have ha := small_half_angle hm (normalizedAngle m u) hθ j
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (pair_re_ge_one ha.2.1 (hr j).1 (hr _).1)
  obtain ⟨g, hg, hgd, hge⟩ := exists_smooth_radial_root (by omega : 2 ≤ m)
    (normalizedAngle m u) s ν (modelRadii m β u) hs hp hsmall hz0
  exact ⟨s, ν, g, hs, hν, hi, hw, hg, hgd, hge⟩

theorem eventual_diameter_radial_chart :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z : Points (2 * m), ExtremalNormalization.DiameterExtremal z →
      ∃ (hm : 0 < m) (σ : Equiv.Perm (Fin (2 * m))) (α β : ℂ) (u : ℕ → ℂ) (η : ℝ),
        NormalizedRelativeEdgeModel z σ α β u η ∧ HasRadialChart hm β u := by
  obtain ⟨m₀, h₀⟩ := eventual_diameter_pointwise_coordinates
  obtain ⟨n₁, h₁⟩ := eventually_atTop.1 eventual_coefficients_small
  refine ⟨max (max m₀ n₁) 8, ?_⟩
  intro m hm z hz
  obtain ⟨hmp, σ, α, β, u, η, h, _, _, hbudget, hbounds⟩ := h₀ m (by omega) z hz
  have hs := h₁ (2 * m) (by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hs
  exact ⟨hmp, σ, α, β, u, η, h,
    model_has_radial_chart (by omega) h hz.1 hbounds hbudget hs.2.1 hs.2.2.1 hs.2.2.2.1⟩

end
end StructuralNote.MatchingActivityRadialActual
