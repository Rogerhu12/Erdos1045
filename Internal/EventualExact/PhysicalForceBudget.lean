import EventualExact.AngularHarmonicBound
import EventualExact.GapRigidityLimit

/-! Arithmetic consequences of physical polar stationarity and separation. -/

namespace Erdos1045.EventualExact.PhysicalForceBudget

open scoped BigOperators Topology
open Filter Asymptotics CyclicAngles CyclicForceBudget FiniteCircleRigidity AngularHarmonicBound

noncomputable section

def radialConstant (γ : ℝ) : ℝ := 2 * Real.pi ^ 2 / γ
def angularConstant (γ : ℝ) : ℝ := 2 * Real.pi ^ 4 / γ
def forceConstant (γ : ℝ) : ℝ := 1 + radialConstant γ + angularConstant γ

theorem forceConstant_nonneg {γ : ℝ} (hγ : 0 < γ) : 0 ≤ forceConstant γ := by
  unfold forceConstant radialConstant angularConstant
  positivity

theorem polarForce_eq_circleForce {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ : ι → ℝ) (i : ι) : polarForce θ i = circleForce θ i := by
  have hs := Finset.sum_erase_add (Finset.univ : Finset ι)
    (fun j => Real.cot ((θ i - θ j) / 2)) (Finset.mem_univ i)
  simp only [sub_self, zero_div, Real.cot_eq_cos_div_sin, Real.cos_zero, Real.sin_zero, div_zero, add_zero] at hs
  unfold polarForce circleForce circleInteraction circleCot
  simp only [Real.cot_eq_cos_div_sin]
  rw [hs]

/-- The explicit reciprocal-angle sum has been eliminated using actual separation. -/
theorem physical_force_residual_bound {n : ℕ} (a : Angles n) (i : Fin n)
    {height : Fin n → ℝ} {γ ε s : ℝ} (hγ : 0 < γ) (hε : 0 ≤ ε)
    (hsmall : ε * Real.pi ≤ 1)
    (hsep : ∀ z : ℤ, γ / n ≤ a.angle (z + 1) - a.angle z)
    (hh : ∀ j, j ≠ i → |height i - height j| ≤ ε * |shortAngle a i j|)
    (hstat : polarForceExpression height (angleVector a) i s = 0) :
    |circleForce (angleVector a) i + (1 - 1 / (n : ℝ)) * s| ≤
      (radialConstant γ * ε * |s| + angularConstant γ * ε ^ 2) * (1 + Real.log n) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  have hb := polar_force_stationarity_bound (height := height) (θ := angleVector a)
    (x := shortAngle a i) i hε hsmall (fun j _ => shortAngle_abs_le_pi a i j)
    (fun j hj => shortAngle_ne_zero a (Ne.symm hj)) hh
    (fun j _ => shortAngle_cos a i j) (fun j _ => shortAngle_sin a i j) hstat
  rw [polarForce_eq_circleForce, Fintype.card_fin] at hb
  have hH := inverseDistanceSum_le_scaled a i hγ hsep
  calc
    _ ≤ (Real.pi ^ 2 * ε * |s| + Real.pi ^ 4 * ε ^ 2) *
        polarInverseDistanceSum (shortAngle a i) i / n := hb
    _ ≤ (Real.pi ^ 2 * ε * |s| + Real.pi ^ 4 * ε ^ 2) *
        ((2 / γ) * n * (1 + Real.log n)) / n := by gcongr
    _ = _ := by unfold radialConstant angularConstant; field_simp

theorem physical_force_norm_bound {n : ℕ} (a : Angles n) (hn : 0 < n)
    {height slope : Fin n → ℝ} {γ ε : ℝ} (hγ : 0 < γ) (hε : 0 ≤ ε)
    (hsmall : ε * Real.pi ≤ 1) (hlogsmall : ε * (1 + Real.log n) ≤ 1)
    (hsep : ∀ z : ℤ, γ / n ≤ a.angle (z + 1) - a.angle z)
    (hh : ∀ i j, j ≠ i → |height i - height j| ≤ ε * |shortAngle a i j|)
    (hs : ∀ i, |slope i| ≤ ε)
    (hstat : ∀ i, polarForceExpression height (angleVector a) i (slope i) = 0) :
    ‖circleForce (angleVector a)‖ ≤ forceConstant γ * ε := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hΛ : 0 ≤ 1 + Real.log n := by have := Real.log_nonneg hn1; linarith
  have hA : 0 ≤ radialConstant γ := by unfold radialConstant; positivity
  have hB : 0 ≤ angularConstant γ := by unfold angularConstant; positivity
  have hc : |1 - 1 / (n : ℝ)| ≤ 1 := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hinv : 1 / (n : ℝ) ≤ 1 := (div_le_one hn0).2 hn1
    have hinv0 : 0 ≤ 1 / (n : ℝ) := by positivity
    rw [abs_le]
    constructor <;> linarith
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (forceConstant_nonneg hγ) hε)).2
  intro i
  rw [Real.norm_eq_abs]
  have he := physical_force_residual_bound a i hγ hε hsmall hsep (hh i) (hstat i)
  have hres : |circleForce (angleVector a) i + (1 - 1 / (n : ℝ)) * slope i| ≤
      (radialConstant γ + angularConstant γ) * ε := by
    calc
      _ ≤ (radialConstant γ * ε * |slope i| + angularConstant γ * ε ^ 2) * (1 + Real.log n) := he
      _ ≤ (radialConstant γ * ε * ε + angularConstant γ * ε ^ 2) * (1 + Real.log n) := by gcongr; exact hs i
      _ = ((radialConstant γ + angularConstant γ) * ε) * (ε * (1 + Real.log n)) := by ring
      _ ≤ ((radialConstant γ + angularConstant γ) * ε) * 1 := by gcongr
      _ = _ := mul_one _
  have htri : |circleForce (angleVector a) i| ≤
      |circleForce (angleVector a) i + (1 - 1 / (n : ℝ)) * slope i| +
        |(1 - 1 / (n : ℝ)) * slope i| := by
    simpa using abs_sub_le (circleForce (angleVector a) i + (1 - 1 / (n : ℝ)) * slope i)
      0 ((1 - 1 / (n : ℝ)) * slope i)
  have hterm : |(1 - 1 / (n : ℝ)) * slope i| ≤ ε := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right hc (abs_nonneg _)).trans (by simpa using hs i)
  unfold forceConstant
  nlinarith

theorem forceSquareSum_le_card_mul_norm_sq {n : ℕ} (a : Angles n) :
    forceSquareSum a ≤ n * ‖circleForce (angleVector a)‖ ^ 2 := by
  unfold forceSquareSum
  calc
    _ ≤ ∑ _i : Fin n, ‖circleForce (angleVector a)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hh := norm_le_pi_norm (circleForce (angleVector a)) i
      rw [Real.norm_eq_abs] at hh
      have hsq := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 hh
      simpa only [sq_abs] using hsq
    _ = _ := by simp

/-- In the improved capacity scale, a bound on `n epsilon²` already suffices. -/
theorem physical_force_square_bound {n : ℕ} (a : Angles n) (hn : 0 < n)
    {height slope : Fin n → ℝ} {γ ε E : ℝ} (hγ : 0 < γ) (hε : 0 ≤ ε)
    (hsmall : ε * Real.pi ≤ 1) (hlogsmall : ε * (1 + Real.log n) ≤ 1)
    (hsep : ∀ z : ℤ, γ / n ≤ a.angle (z + 1) - a.angle z)
    (hh : ∀ i j, j ≠ i → |height i - height j| ≤ ε * |shortAngle a i j|)
    (hs : ∀ i, |slope i| ≤ ε)
    (hstat : ∀ i, polarForceExpression height (angleVector a) i (slope i) = 0)
    (hE : (n : ℝ) * ε ^ 2 ≤ E) : forceSquareSum a ≤ forceConstant γ ^ 2 * E := by
  have hf := physical_force_norm_bound a hn hγ hε hsmall hlogsmall hsep hh hs hstat
  calc
    _ ≤ n * ‖circleForce (angleVector a)‖ ^ 2 := forceSquareSum_le_card_mul_norm_sq a
    _ ≤ n * (forceConstant γ * ε) ^ 2 := by gcongr
    _ = forceConstant γ ^ 2 * ((n : ℝ) * ε ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hE (sq_nonneg _)

/-- This records the power cancellation used by the stronger geometric input. -/
theorem card_mul_epsilon_sq_of_half_power {n : ℕ} (hn : 0 < n) {ε C : ℝ}
    (hε : 0 ≤ ε) (hbound : ε ≤ C * (n : ℝ) ^ (-(1 / 2 : ℝ))) :
    (n : ℝ) * ε ^ 2 ≤ C ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : ((n : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (n : ℝ)⁻¹ := by
    rw [← Real.rpow_natCast ((n : ℝ) ^ (-(1 / 2 : ℝ))) 2, ← Real.rpow_mul hn0.le]
    norm_num [Real.rpow_neg_one]
  calc
    _ ≤ (n : ℝ) * (C * (n : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 := by gcongr
    _ = C ^ 2 := by rw [mul_pow, hp]; field_simp

theorem logarithmic_half_power_tendsto :
    Tendsto (fun x : ℝ => (1 + Real.log x) * x ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
  have hp := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2))
  have hl := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have he : (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) =ᶠ[atTop]
      fun x => Real.log x * x ^ (-(1 / 2 : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.rpow_neg hx.le, div_eq_mul_inv]
  have hl' := hl.congr' he
  simpa only [add_mul, one_mul, add_zero] using hp.add hl'

theorem eventually_half_power_small {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {ε : ℕ → ℝ} {C : ℝ}
    (hbound : ∀ᶠ j in atTop, ε j ≤ C * (N j : ℝ) ^ (-(1 / 2 : ℝ))) :
    ∀ᶠ j in atTop, ε j * Real.pi ≤ 1 ∧ ε j * (1 + Real.log (N j)) ≤ 1 := by
  have hNr : Tendsto (fun j => (N j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  have hp := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hNr).const_mul (C * Real.pi)
  have hl := (logarithmic_half_power_tendsto.comp hNr).const_mul C
  have hpe : ∀ᶠ j in atTop, (C * Real.pi) * (N j : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
    hp.eventually (gt_mem_nhds (by norm_num))
  have hle : ∀ᶠ j in atTop,
      C * ((1 + Real.log (N j)) * (N j : ℝ) ^ (-(1 / 2 : ℝ))) < 1 :=
    hl.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hbound, hpe, hle, hN.eventually (eventually_ge_atTop 1)] with j hb hpp hll hn
  have hn1 : (1 : ℝ) ≤ N j := by exact_mod_cast hn
  have hΛ : 0 ≤ 1 + Real.log (N j) := by have := Real.log_nonneg hn1; linarith
  constructor
  · have := mul_le_mul_of_nonneg_right hb Real.pi_pos.le
    nlinarith
  · have := mul_le_mul_of_nonneg_right hb hΛ
    nlinarith

def rigidityBudgetConstant (γ C : ℝ) : ℝ :=
  1 + forceConstant γ * C + forceConstant γ ^ 2 * C ^ 2

theorem rigidityBudgetConstant_nonneg {γ C : ℝ} (hγ : 0 < γ) (hC : 0 ≤ C) :
    0 ≤ rigidityBudgetConstant γ C := by
  have := forceConstant_nonneg hγ
  unfold rigidityBudgetConstant
  positivity

/-- The stronger half-power input supplies both hypotheses of `GapRigidityLimit`. -/
theorem force_bounds_of_half_power {n : ℕ} (a : Angles n) (hn : 0 < n)
    {height slope : Fin n → ℝ} {γ ε C : ℝ} (hγ : 0 < γ) (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hsmall : ε * Real.pi ≤ 1) (hlogsmall : ε * (1 + Real.log n) ≤ 1)
    (hsep : ∀ z : ℤ, γ / n ≤ a.angle (z + 1) - a.angle z)
    (hh : ∀ i j, j ≠ i → |height i - height j| ≤ ε * |shortAngle a i j|)
    (hs : ∀ i, |slope i| ≤ ε)
    (hstat : ∀ i, polarForceExpression height (angleVector a) i (slope i) = 0)
    (hbound : ε ≤ C * (n : ℝ) ^ (-(1 / 2 : ℝ))) :
    forceSquareSum a ≤ rigidityBudgetConstant γ C * (1 + Real.log n) ^ 2 ∧
    ‖circleForce (angleVector a)‖ ≤ rigidityBudgetConstant γ C * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
  have hK := forceConstant_nonneg hγ
  have hD := rigidityBudgetConstant_nonneg hγ hC
  have hD₁ : forceConstant γ * C ≤ rigidityBudgetConstant γ C := by
    unfold rigidityBudgetConstant
    nlinarith [sq_nonneg (forceConstant γ * C)]
  have hD₂ : forceConstant γ ^ 2 * C ^ 2 ≤ rigidityBudgetConstant γ C := by
    unfold rigidityBudgetConstant
    have := mul_nonneg hK hC
    linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hΛ : 1 ≤ (1 + Real.log n) ^ 2 := by
    have := Real.log_nonneg hn1
    nlinarith [sq_nonneg (Real.log n)]
  constructor
  · have ht := physical_force_square_bound a hn hγ hε hsmall hlogsmall hsep hh hs hstat
      (card_mul_epsilon_sq_of_half_power hn hε hbound)
    exact ht.trans (hD₂.trans (by nlinarith [mul_le_mul_of_nonneg_left hΛ hD]))
  · have hf := physical_force_norm_bound a hn hγ hε hsmall hlogsmall hsep hh hs hstat
    have hp : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (n : ℝ) ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
    calc
      _ ≤ forceConstant γ * ε := hf
      _ ≤ forceConstant γ * (C * (n : ℝ) ^ (-(1 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hbound hK
      _ = (forceConstant γ * C) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by ring
      _ ≤ (forceConstant γ * C) * (n : ℝ) ^ (-(1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hp (mul_nonneg hK hC)
      _ ≤ _ := mul_le_mul_of_nonneg_right hD₁ (Real.rpow_nonneg (by positivity) _)

/-- Actual separated polar stationary configurations become gap-rigid under a
half-power radial and normal-slope bound. No slope integral budget is needed. -/
theorem gapDeviation_tendsto_of_half_power {N : ℕ → ℕ} (a : ∀ j, Angles (N j))
    (hN : Tendsto N atTop atTop) (height slope : ∀ j, Fin (N j) → ℝ) (ε : ℕ → ℝ)
    {γ C : ℝ} (hγ : 0 < γ) (hC : 0 ≤ C)
    (hε : ∀ᶠ j in atTop, 0 ≤ ε j)
    (hbound : ∀ᶠ j in atTop, ε j ≤ C * (N j : ℝ) ^ (-(1 / 2 : ℝ)))
    (hsep : ∀ᶠ j in atTop, ∀ z : ℤ, γ / N j ≤ (a j).angle (z + 1) - (a j).angle z)
    (hh : ∀ᶠ j in atTop, ∀ i k, k ≠ i →
      |height j i - height j k| ≤ ε j * |shortAngle (a j) i k|)
    (hs : ∀ᶠ j in atTop, ∀ i, |slope j i| ≤ ε j)
    (hstat : ∀ᶠ j in atTop, ∀ i,
      polarForceExpression (height j) (angleVector (a j)) i (slope j i) = 0) :
    Tendsto (fun j => ‖gapDeviation (a j)‖) atTop (𝓝 0) := by
  have hsmall := eventually_half_power_small hN hbound
  have hbud : ∀ᶠ j in atTop,
      forceSquareSum (a j) ≤ rigidityBudgetConstant γ C * (1 + Real.log (N j)) ^ 2 ∧
      ‖circleForce (angleVector (a j))‖ ≤ rigidityBudgetConstant γ C *
        (N j : ℝ) ^ (-(1 / 4 : ℝ)) := by
    filter_upwards [hε, hbound, hsep, hh, hs, hstat, hsmall,
      hN.eventually (eventually_ge_atTop 1)] with j he hb hsep hh hs hstat hsmall hn
    exact force_bounds_of_half_power (a j) hn hγ he hC hsmall.1 hsmall.2 hsep hh hs hstat hb
  exact GapRigidityLimit.gapDeviation_tendsto_zero a hN (rigidityBudgetConstant_nonneg hγ hC)
    (hbud.mono fun _ h => h.1) (hbud.mono fun _ h => h.2)

end
end Erdos1045.EventualExact.PhysicalForceBudget
