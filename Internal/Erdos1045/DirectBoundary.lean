import Erdos1045.ExteriorClassical
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv

/-! # Boundary arc estimates from the analytic-model derivative bound

The estimate used for node separation follows by applying the ordinary mean
value inequality on circles of radius greater than one and passing to the
boundary. No boundary mean-value theorem is assumed.
-/

namespace Erdos1045.ExteriorClassical

open ExteriorBoundary Configuration Filter
open scoped Topology
noncomputable section

theorem ExteriorData.circle_arc_bound {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) {r : ℝ} (hr : 1 < r) (s t : ℝ) :
    ‖d.map ((r : ℂ) * unit s) - d.map ((r : ℂ) * unit t)‖ ≤
      4 * d.capacity * r * |s - t| := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hnorm (u : ℝ) : ‖(r : ℂ) * unit u‖ = r := by
    simp [Complex.norm_real, abs_of_pos hr0]
  have hder (u : ℝ) : HasDerivAt (fun v : ℝ => d.map ((r : ℂ) * unit v))
      (d.derivative ((r : ℂ) * unit u) * ((r : ℂ) * unit u * Complex.I)) u := by
    have hinner := ((Complex.hasDerivAt_exp ((u : ℂ) * Complex.I)).comp (u : ℂ)
      ((hasDerivAt_id (u : ℂ)).mul_const Complex.I)).const_mul (r : ℂ)
    have hout := (HF.map_derivative ((r : ℂ) * unit u) (by rw [hnorm]; exact hr)).comp
      (u : ℂ) hinner
    simpa [unit, mul_assoc] using hout.comp_ofReal
  have hbound (u : ℝ) :
      ‖d.derivative ((r : ℂ) * unit u) * ((r : ℂ) * unit u * Complex.I)‖ ≤
        4 * d.capacity * r := by
    simpa only [norm_mul, Complex.norm_I, mul_one, hnorm] using
      mul_le_mul_of_nonneg_right (d.derivative_le (by rw [hnorm]; exact hr)) hr0.le
  simpa only [Real.norm_eq_abs] using
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u _ => (hder u).hasDerivWithinAt) (fun u _ => hbound u)
      (Set.mem_univ t) (Set.mem_univ s)

theorem ExteriorData.boundary_arc_bound {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (s t : ℝ) :
    ‖d.map (unit s) - d.map (unit t)‖ ≤ 4 * d.capacity * |s - t| := by
  let r : ℕ → ℝ := fun k => 1 + (1 / 2 : ℝ) ^ k
  have hr (k : ℕ) : 1 < r k := by
    dsimp [r]
    linarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k]
  have hrlim : Tendsto r atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))
  have hlim (u : ℝ) : Tendsto (fun k => d.map ((r k : ℂ) * unit u)) atTop
      (𝓝 (d.map (unit u))) := by
    apply (HF.map_continuous (unit u)
      (by simp : unit u ∈ {w : ℂ | 1 ≤ ‖w‖})).tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (Complex.continuous_ofReal.tendsto 1 |>.comp hrlim).mul_const (unit u)
    · exact Filter.Eventually.of_forall fun k => by
        dsimp
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_unit, mul_one]
        rw [abs_of_pos (lt_trans zero_lt_one (hr k))]
        exact (hr k).le
  have hright : Tendsto (fun k => 4 * d.capacity * r k * |s - t|) atTop
      (𝓝 (4 * d.capacity * |s - t|)) := by
    simpa using (tendsto_const_nhds.mul hrlim).mul_const |s - t|
  exact le_of_tendsto_of_tendsto' ((hlim s).sub (hlim t)).norm hright
    (fun k => d.circle_arc_bound HF (hr k) s t)

private theorem unit_period (t : ℝ) : unit (t + 2 * Real.pi) = unit t := by
  unfold unit
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem ExteriorData.boundary_short_arc_bound {n : ℕ} {z : Points n}
    (d : ExteriorData z) (HF : FaberIdentities d) (s t : ℝ)
    (hst : |s - t| ≤ 2 * Real.pi) :
    ‖d.map (unit s) - d.map (unit t)‖ ≤
      4 * d.capacity * min |s - t| (2 * Real.pi - |s - t|) := by
  have hc : 0 ≤ 4 * d.capacity := mul_nonneg (by norm_num) d.capacity_pos.le
  rw [mul_min_of_nonneg _ _ hc]
  refine le_min (d.boundary_arc_bound HF s t) ?_
  by_cases hst' : s ≤ t
  · have h := d.boundary_arc_bound HF (s + 2 * Real.pi) t
    rw [unit_period] at h
    rw [abs_of_nonpos (sub_nonpos.mpr hst')] at hst ⊢
    rw [abs_of_nonneg (by linarith : 0 ≤ s + 2 * Real.pi - t)] at h
    nlinarith [h]
  · have h := d.boundary_arc_bound HF s (t + 2 * Real.pi)
    rw [unit_period] at h
    rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hst'))] at hst ⊢
    rw [abs_of_nonpos (by linarith : s - (t + 2 * Real.pi) ≤ 0)] at h
    nlinarith [h]

end
end Erdos1045.ExteriorClassical
