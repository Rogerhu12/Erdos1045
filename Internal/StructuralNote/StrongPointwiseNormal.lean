import StructuralNote.StrongPointwiseConstraint

/-! The genuine normal variables lie within O(1/n) of the finite box. -/

noncomputable section
open scoped BigOperators Topology

namespace StructuralNote.StrongPointwiseNormal

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization Filter
open SchurSpectrum SchurLiftBounds DiscreteEnergy FiniteFourierLift FourierMultiplier
open ExtremalPolarCenter NormalizedPolarRepresentation SignedPressureRemainder StrongObjectiveEstimate
open SinglePressureEstimate StrongBudgetConsequences StrongPointwiseConstraint
open SignedCrossingPressure ActualCrossingGeometry

def normalConstant : ℝ := errorConstant budgetConstant angleConstant centerConstant / 4

theorem normalConstant_nonneg : 0 ≤ normalConstant := by
  unfold normalConstant errorConstant angleConstant centerConstant
  have := budgetConstant_nonneg
  positivity

theorem model_normal_bound {m : ℕ} (hm : 8 ≤ m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hz : DiameterAtMost 2 z)
    (hc : CenterBounds (m := m) (by omega) β u)
    (hq : meanSquare (polarConstraint (m := m) (by omega) β u) ≤ 65 * Real.pi ^ 2)
    (hbudget : radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
      realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / (2 * m : ℝ) ^ 2)
    (hsmallB : 2 * budgetConstant / (2 * m : ℝ) ^ 3 ≤ 1 / 2)
    (hsmallT : angleConstant / (2 * m : ℝ) ^ 2 ≤ 1 / 2)
    (hsmallC : centerConstant / (2 * m : ℝ) ≤ 1) (j : Fin (2 * m)) :
    |polarConstraint (m := m) (by omega) β u j| ≤
      FiniteBox.amplitude (2 * m) + normalConstant / (2 * m) := by
  obtain ⟨hcenter, hb, hangle⟩ := model_pointwise_bounds (show 2 ≤ m by omega) h hz hc hq hbudget
  have hrot (k : Fin (2 * m)) : ‖rotatedCenter m β u j k‖ ≤ centerConstant / (2 * m) := by
    rw [rotatedCenter_norm]
    exact (norm_le_pi_norm (polarCenter m β u) k).trans hcenter
  have hbpair : radialDeficit m β u j + radialDeficit m β u (successor (by omega) j) ≤
      2 * budgetConstant / (2 * m : ℝ) ^ 3 := by
    calc
      _ ≤ budgetConstant / (2 * m : ℝ) ^ 3 + budgetConstant / (2 * m : ℝ) ^ 3 :=
        add_le_add (hb j).2 (hb (successor (by omega) j)).2
      _ = _ := by ring
  have hcross := actual_rotated_crossing (show 0 < m by omega) h hz j
  have hh := normal_bound (show 16 ≤ 2 * m by omega) (B := budgetConstant) (T := angleConstant)
    (C := centerConstant) budgetConstant_nonneg
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hsmallB)
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hsmallT)
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hsmallC)
    (hb j).1 (hb (successor (by omega) j)).1
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbpair)
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hangle j)
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hrot j)
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hrot (successor (by omega) j))
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcross.1)
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcross.2)
  have he : normalComponent (2 * m) (Real.pi / (2 * m : ℕ))
      (rotatedCenter m β u j j) (rotatedCenter m β u j (successor (by omega) j)) =
        polarConstraint (m := m) (by omega) β u j := by
    rw [rotatedCenter, rotatedCenter, normalComponent_eq_normal (by omega)]
    exact congrFun (ActualPressureGap.polarConstraint_eq_normal (by omega) β u).symm j
  rw [he] at hh
  convert hh using 1
  simp only [Nat.cast_mul, Nat.cast_ofNat, normalConstant]
  ring

theorem strong_scale_small : ∀ᶠ m : ℕ in atTop,
    2 * budgetConstant / (2 * m : ℝ) ^ 3 ≤ 1 / 2 ∧
    angleConstant / (2 * m : ℝ) ^ 2 ≤ 1 / 2 ∧
    centerConstant / (2 * m : ℝ) ≤ 1 := by
  have hN : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 2 * m) tendsto_id
  have hi : Tendsto (fun m : ℕ => (2 * m : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat] using
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hN)
  have hb : Tendsto (fun m : ℕ => 2 * budgetConstant / (2 * m : ℝ) ^ 3) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : 3 ≠ 0), inv_pow, div_eq_mul_inv, mul_zero] using
      (hi.pow 3).const_mul (2 * budgetConstant)
  have ht : Tendsto (fun m : ℕ => angleConstant / (2 * m : ℝ) ^ 2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : 2 ≠ 0), inv_pow, div_eq_mul_inv, mul_zero] using
      (hi.pow 2).const_mul angleConstant
  have hc : Tendsto (fun m : ℕ => centerConstant / (2 * m : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hi.const_mul centerConstant
  filter_upwards [hb.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2),
    ht.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2),
    hc.eventually_le_const (by norm_num : (0 : ℝ) < 1)] with m hb ht hc
  exact ⟨hb, ht, hc⟩

/-- The pointwise normal estimate of (6.21), retaining the strong budget and all
coordinates of the actual maximizer in the same existential witness. -/
theorem eventual_diameter_normal_bound :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z : Points (2 * m), ExtremalNormalization.DiameterExtremal z →
      ∃ (hm : 0 < m) (σ : Equiv.Perm (Fin (2 * m))) (α β : ℂ) (u : ℕ → ℂ) (η : ℝ),
        NormalizedRelativeEdgeModel z σ α β u η ∧ CenterBounds hm β u ∧
        meanSquare (polarConstraint hm β u) ≤ 65 * Real.pi ^ 2 ∧
        radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
          realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / (2 * m : ℝ) ^ 2 ∧
        ∀ j, |polarConstraint hm β u j| ≤ FiniteBox.amplitude (2 * m) + normalConstant / (2 * m) := by
  obtain ⟨m₀, h₀⟩ := eventual_diameter_single_pressure
  obtain ⟨m₁, h₁⟩ := eventually_atTop.1 strong_scale_small
  refine ⟨max (max m₀ m₁) 8, ?_⟩
  intro m hm z hz
  obtain ⟨hmp, σ, α, β, u, η, h, hc, _, hq, _, _, hbudget⟩ := h₀ m (by omega) z hz
  have hs := h₁ m (by omega)
  have hbudget' : radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
      realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / (2 * m : ℝ) ^ 2 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbudget
  exact ⟨hmp, σ, α, β, u, η, h, hc, hq, hbudget',
    model_normal_bound (by omega) h hz.1 hc hq hbudget' hs.1 hs.2.1 hs.2.2⟩

end StructuralNote.StrongPointwiseNormal
