import StructuralNote.SinglePressureEstimate

/-! Pointwise consequences of the genuine strong energy budget. -/

noncomputable section
open scoped BigOperators Topology

namespace StructuralNote.StrongBudgetConsequences

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization
open SchurSpectrum SchurLiftBounds DiscreteEnergy FiniteFourierLift FourierMultiplier
open ExtremalPolarCenter NormalizedPolarRepresentation SignedPressureRemainder StrongObjectiveEstimate
open SinglePressureEstimate CanonicalNonlinearError

theorem budgetConstant_nonneg : 0 ≤ budgetConstant := by
  unfold budgetConstant comparisonConstant objectiveConstant ActualPressureAbsorption.pressureConstant
    PressureAngularAbsorption.angularConstant
  positivity

def centerConstant : ℝ := Real.sqrt (64 * Real.pi ^ 2 * (65 * Real.pi ^ 2) + 24 * budgetConstant)

def angleConstant : ℝ := Real.sqrt (8 * Real.pi ^ 2 * budgetConstant)

theorem center_bound_of_budget {n : ℕ} (hn : 3 ≤ n) (c : Points n) (q : Fin n → ℝ)
    (hmean : ∑ j, c j = 0) (hq : meanSquare q ≤ 65 * Real.pi ^ 2)
    (hD : pairEnergy (by omega) (c - SchurLift.canonicalLift q) ≤ budgetConstant / (n : ℝ) ^ 2) :
    ‖c‖ ≤ centerConstant / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : Real.log n ≤ (n : ℝ) ^ 2 := by
    have hh := Real.log_le_sub_one_of_pos hn0
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hcoeff : 24 * Real.log n / (n : ℝ) ^ 2 ≤ 24 := by
    apply (div_le_iff₀ (sq_pos_of_pos hn0)).2
    linarith only [hlog]
  have hm := mul_le_mul_of_nonneg_right hcoeff
    (pairEnergy_nonneg (show 0 < n by omega) (c - SchurLift.canonicalLift q))
  have hD' := mul_le_mul_of_nonneg_left hD (by norm_num : (0 : ℝ) ≤ 24)
  have hs := center_sup_sq_le hn c q hmean hq
  have hbound : ‖c‖ ^ 2 ≤
      (64 * Real.pi ^ 2 * (65 * Real.pi ^ 2) + 24 * budgetConstant) / (n : ℝ) ^ 2 := by
    calc
      _ ≤ 64 * Real.pi ^ 2 / (n : ℝ) ^ 2 * (65 * Real.pi ^ 2) +
          24 * (budgetConstant / (n : ℝ) ^ 2) := by linarith only [hs, hm, hD']
      _ = _ := by ring
  have hC : centerConstant ^ 2 = 64 * Real.pi ^ 2 * (65 * Real.pi ^ 2) + 24 * budgetConstant := by
    exact Real.sq_sqrt (by have := budgetConstant_nonneg; positivity)
  apply (sq_le_sq₀ (norm_nonneg _) (div_nonneg (Real.sqrt_nonneg _) hn0.le)).1
  change ‖c‖ ^ 2 ≤ (centerConstant / n) ^ 2
  rw [div_pow, hC]
  exact hbound

theorem angular_difference_of_budget {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ)
    (hE : realEnergy hn θ ≤ budgetConstant / (n : ℝ) ^ 2) (j : Fin n) :
    |θ (successor hn j) - θ j| ≤ angleConstant / (n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have he := difference_energy_le hn (fun j => (θ j : ℂ))
  simp only [difference, ← ofReal_sub, normSq_ofReal, ← pow_two] at he
  change (n : ℝ) ^ 2 * (∑ j, (θ (successor hn j) - θ j) ^ 2) ≤
    8 * Real.pi ^ 2 * realEnergy hn θ at he
  have hs := Finset.single_le_sum (s := Finset.univ)
    (f := fun j => (θ (successor hn j) - θ j) ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  have hs' := mul_le_mul_of_nonneg_left hs (sq_nonneg (n : ℝ))
  have hδ : (θ (successor hn j) - θ j) ^ 2 ≤ 8 * Real.pi ^ 2 * realEnergy hn θ / (n : ℝ) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hn0)).2
    nlinarith only [he, hs']
  have hC : angleConstant ^ 2 = 8 * Real.pi ^ 2 * budgetConstant := by
    exact Real.sq_sqrt (by have := budgetConstant_nonneg; positivity)
  have hδ' : (θ (successor hn j) - θ j) ^ 2 ≤ (angleConstant / (n : ℝ) ^ 2) ^ 2 := by
    calc
      _ ≤ 8 * Real.pi ^ 2 * realEnergy hn θ / (n : ℝ) ^ 2 := hδ
      _ ≤ 8 * Real.pi ^ 2 * (budgetConstant / (n : ℝ) ^ 2) / (n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by positivity)) (sq_nonneg _)
      _ = _ := by rw [div_pow, hC]; ring
  exact (sq_le_sq₀ (abs_nonneg _) (by unfold angleConstant; positivity)).1 (by rwa [sq_abs])

theorem radial_deficit_of_budget {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ)
    (hb : ∀ j, 0 ≤ radialDeficit m β u j)
    (hτ : radialMass m β u ≤ budgetConstant / (2 * m : ℝ) ^ 2) (j : Fin (2 * m)) :
    radialDeficit m β u j ≤ budgetConstant / (2 * m : ℝ) ^ 3 := by
  have hn : (0 : ℝ) < 2 * m := by positivity
  have hs := Finset.single_le_sum (s := Finset.univ) (f := radialDeficit m β u)
    (fun k _ => hb k) (Finset.mem_univ j)
  calc
    _ ≤ radialMass m β u / (2 * m) := by
      simpa only [radialMass, mul_div_cancel_left₀ _ hn.ne'] using hs
    _ ≤ (budgetConstant / (2 * m : ℝ) ^ 2) / (2 * m) := div_le_div_of_nonneg_right hτ hn.le
    _ = _ := by ring

theorem model_pointwise_bounds {m : ℕ} (hm : 2 ≤ m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hz : DiameterAtMost 2 z)
    (hc : CenterBounds (m := m) (by omega) β u)
    (hq : meanSquare (polarConstraint (m := m) (by omega) β u) ≤ 65 * Real.pi ^ 2)
    (hbudget : radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
      realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / (2 * m : ℝ) ^ 2) :
    ‖polarCenter m β u‖ ≤ centerConstant / (2 * m) ∧
      (∀ j, 0 ≤ radialDeficit m β u j ∧ radialDeficit m β u j ≤ budgetConstant / (2 * m : ℝ) ^ 3) ∧
      (∀ j, |normalizedAngle m u (successor (by omega) j) - normalizedAngle m u j| ≤
        angleConstant / (2 * m : ℝ) ^ 2) := by
  have hb (j : Fin (2 * m)) : 0 ≤ radialDeficit m β u j := sub_nonneg.mpr
    (PolarRepresentation.model_radius_le_one (by omega) h hz j)
  have hτ : 0 ≤ radialMass m β u := by
    unfold radialMass
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => hb j)
  have hD : 0 ≤ residualEnergy (by omega) (polarCenter m β u) := pairEnergy_nonneg (by omega) _
  have hE : 0 ≤ realEnergy (by omega) (normalizedAngle m u) := pairEnergy_nonneg (by omega) _
  have hDb : residualEnergy (by omega) (polarCenter m β u) ≤ budgetConstant / (2 * m : ℝ) ^ 2 := by linarith
  have hEb : realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / (2 * m : ℝ) ^ 2 := by linarith
  refine ⟨?_, fun j => ⟨hb j, radial_deficit_of_budget (by omega) β u hb (by linarith) j⟩, ?_⟩
  · simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      center_bound_of_budget (show 3 ≤ 2 * m by omega) (polarCenter m β u) (polarConstraint (by omega) β u)
        hc.mean_zero hq (by simpa only [residualEnergy, polarConstraint, Nat.cast_mul, Nat.cast_ofNat] using hDb)
  · intro j
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using angular_difference_of_budget
      (show 0 < 2 * m by omega) (normalizedAngle m u) (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hEb) j

/-- The pointwise center, radius, and angular-step scales of (6.21), for every
actual maximizer of sufficiently large even order. -/
theorem eventual_diameter_pointwise :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z : Points (2 * m), ExtremalNormalization.DiameterExtremal z →
      ∃ (hm : 0 < m) (σ : Equiv.Perm (Fin (2 * m))) (α β : ℂ) (u : ℕ → ℂ) (η : ℝ),
        NormalizedRelativeEdgeModel z σ α β u η ∧
        ‖polarCenter m β u‖ ≤ centerConstant / (2 * m) ∧
        (∀ j, 0 ≤ radialDeficit m β u j ∧ radialDeficit m β u j ≤ budgetConstant / (2 * m : ℝ) ^ 3) ∧
        (∀ j, |normalizedAngle m u (successor (by omega) j) - normalizedAngle m u j| ≤
          angleConstant / (2 * m : ℝ) ^ 2) := by
  obtain ⟨m₀, h₀⟩ := eventual_diameter_single_pressure
  refine ⟨max m₀ 2, ?_⟩
  intro m hm z hz
  obtain ⟨hmp, σ, α, β, u, η, h, hc, _, hq, _, _, hbudget⟩ := h₀ m (by omega) z hz
  have hp := model_pointwise_bounds (show 2 ≤ m by omega) h hz.1 hc hq
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbudget)
  exact ⟨hmp, σ, α, β, u, η, h, hp⟩

end StructuralNote.StrongBudgetConsequences
