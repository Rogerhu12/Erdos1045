import EventualExact.FiniteCircleRigidity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The asymptotic consequence of finite circle rigidity. The two hypotheses
are ordinary estimates on the actual force and its square sum; this module
does not assert that a geometric extremizer satisfies those estimates. -/

namespace Erdos1045.EventualExact.GapRigidityLimit

open Filter Asymptotics
open scoped Topology
open CyclicAngles CyclicForceBudget FiniteCircleRigidity

noncomputable section

def rigidityConstant (C : ℝ) : ℝ :=
  54 * Real.pi ^ 3 * (2 + 3 * Real.pi ^ 2 * C) ^ 3 * C ^ 2

/-- The explicit eighth logarithmic power resulting from the finite cubic bound. -/
theorem gapDeviation_cube_le {n : ℕ} (a : Angles n) (hn : 3 ≤ n)
    {C : ℝ} (hC : 0 ≤ C)
    (hT : forceSquareSum a ≤ C * (1 + Real.log n) ^ 2)
    (hf : ‖circleForce (angleVector a)‖ ≤ C * (n : ℝ) ^ (-(1 / 4 : ℝ))) :
    ‖gapDeviation a‖ ^ 3 ≤
      rigidityConstant C * (1 + Real.log n) ^ 8 * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hΛ : 1 ≤ (1 + Real.log n) ^ 2 := by nlinarith [sq_nonneg (Real.log n)]
  have hT0 := forceSquareSum_nonneg a
  have hb : 2 + 3 * Real.pi ^ 2 * forceSquareSum a ≤
      (2 + 3 * Real.pi ^ 2 * C) * (1 + Real.log n) ^ 2 := by
    calc
      _ ≤ 2 + 3 * Real.pi ^ 2 * (C * (1 + Real.log n) ^ 2) := by gcongr
      _ ≤ 2 * (1 + Real.log n) ^ 2 +
          3 * Real.pi ^ 2 * (C * (1 + Real.log n) ^ 2) := by linarith
      _ = _ := by ring
  calc
    _ ≤ 54 * Real.pi ^ 3 * (2 + 3 * Real.pi ^ 2 * forceSquareSum a) ^ 3 *
        forceSquareSum a * ‖circleForce (angleVector a)‖ := finite_circle_rigidity a hn
    _ ≤ 54 * Real.pi ^ 3 * ((2 + 3 * Real.pi ^ 2 * C) * (1 + Real.log n) ^ 2) ^ 3 *
        (C * (1 + Real.log n) ^ 2) * (C * (n : ℝ) ^ (-(1 / 4 : ℝ))) := by
      gcongr
    _ = _ := by unfold rigidityConstant; ring

/-- A fixed logarithmic eighth power is dominated by the negative quarter power. -/
theorem log_eighth_mul_neg_quarter_tendsto :
    Tendsto (fun x : ℝ => (1 + Real.log x) ^ 8 * x ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) := by
  have h1 : (fun _x : ℝ => (1 : ℝ)) =o[atTop] fun x => x ^ (1 / 32 : ℝ) := by
    simpa only [Function.comp_def, id_eq] using
      (isLittleO_const_id_atTop (1 : ℝ)).comp_tendsto
        (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 32))
  have hl := isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 32)
  have hp := ((h1.add hl).pow (by norm_num : 0 < (8 : ℕ))).tendsto_div_nhds_zero
  apply hp.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [← Real.rpow_natCast (x ^ (1 / 32 : ℝ)) 8, ← Real.rpow_mul hx.le]
  norm_num
  rw [Real.rpow_neg hx.le, div_eq_mul_inv]

/-- Cube convergence implies convergence for a nonnegative real sequence. -/
theorem tendsto_zero_of_cube {u : ℕ → ℝ}
    (hu : ∀ j, 0 ≤ u j) (hlim : Tendsto (fun j => u j ^ 3) atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro x hx
    exact Eventually.of_forall fun j => hx.trans_le (hu j)
  · intro ε hε
    filter_upwards [hlim.eventually (gt_mem_nhds (pow_pos hε 3))] with j hj
    exact lt_of_pow_lt_pow_left₀ 3 hε.le hj

/-- Along arbitrary dimensions tending to infinity, the two force estimates
imply uniform relative-gap rigidity. Their geometric origin is left to callers. -/
theorem gapDeviation_tendsto_zero {N : ℕ → ℕ} (a : ∀ j, Angles (N j))
    (hN : Tendsto N atTop atTop) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ᶠ j in atTop, forceSquareSum (a j) ≤ C * (1 + Real.log (N j)) ^ 2)
    (hf : ∀ᶠ j in atTop,
      ‖circleForce (angleVector (a j))‖ ≤ C * (N j : ℝ) ^ (-(1 / 4 : ℝ))) :
    Tendsto (fun j => ‖gapDeviation (a j)‖) atTop (𝓝 0) := by
  have hNr : Tendsto (fun j => (N j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hmodel : Tendsto (fun j => rigidityConstant C *
      ((1 + Real.log (N j)) ^ 8 * (N j : ℝ) ^ (-(1 / 4 : ℝ)))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      (log_eighth_mul_neg_quarter_tendsto.comp hNr).const_mul (rigidityConstant C)
  apply tendsto_zero_of_cube (fun _ => norm_nonneg _)
  apply squeeze_zero' (Eventually.of_forall fun _ => by positivity) _ hmodel
  filter_upwards [hN.eventually (eventually_ge_atTop 3), hT, hf] with j hn hT hf
  simpa only [mul_assoc] using gapDeviation_cube_le (a j) hn hC hT hf

end
end Erdos1045.EventualExact.GapRigidityLimit
