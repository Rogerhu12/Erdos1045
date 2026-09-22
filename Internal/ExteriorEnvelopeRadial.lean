import BoundaryPolygonLength
import PositiveExteriorModel
import RadialEnergy

namespace ExteriorReduction
open Complex Metric Set Filter MeasureTheory
open Erdos1045.ExteriorBoundary
open scoped Topology
noncomputable section

/-- Exterior circle length is the interior radial mean of the actual
normalized derivative, with the exact radius and `2π` factors. -/
theorem exteriorCircleLength_model {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) {c : ℝ} (hc : 0 < c)
    (hq0 : q 0 = (c : ℂ)) (A : ℂ) {r : ℝ} (hr : 1 < r) :
    exteriorCircleLength (exteriorFromModel q A) r =
      2 * Real.pi * r * c * radialMeanNorm (modelDerivative q) r⁻¹ := by
  have hqne : q 0 ≠ 0 := hq0 ▸ Complex.ofReal_ne_zero.mpr hc.ne'
  have havg : radialMeanNorm (modelDerivative q) r⁻¹ =
      (2 * Real.pi)⁻¹ * ∫ t in 0..2 * Real.pi,
        ‖modelDerivative q (((r : ℂ) * unit t)⁻¹)‖ := by
    unfold radialMeanNorm
    rw [Real.circleAverage_eq_circleAverage_zero_one,
      ← Real.circleAverage_zero_one_congr_inv]
    unfold Real.circleAverage
    simp only [smul_eq_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    simp [circleMap, unit, mul_comm]
  have hpoint (t : ℝ) :
      ‖deriv (exteriorFromModel q A) ((r : ℂ) * unit t)‖ * r =
        (c * r) * ‖modelDerivative q (((r : ℂ) * unit t)⁻¹)‖ := by
    rw [exteriorFromModel_normalized_deriv hq hqne A (exterior_circle_mem hr t),
      hq0, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    ring
  unfold exteriorCircleLength
  simp_rw [hpoint]
  rw [intervalIntegral.integral_const_mul, havg]
  field_simp

/-- Inversion carries radii approaching one from below to exterior radii
approaching one from above. -/
theorem tendsto_inverse_radius_one :
    Tendsto (fun ρ : ℝ => ρ⁻¹) (𝓝[<] 1) (𝓝[>] 1) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hh := (tendsto_id : Tendsto (fun ρ : ℝ => ρ) (𝓝 1) (𝓝 1)).inv₀ one_ne_zero
    simpa only [inv_one, id_eq] using hh.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with ρ hρ1 hρ0
    change 1 < ρ⁻¹
    exact (one_lt_inv₀ (show 0 < ρ from hρ0)).mpr hρ1

/-- A geometric upper limit of exterior-circle lengths gives precisely the
radial length premise used by the energy theorem. -/
theorem radialMeanNorm_upper_of_circleLength_upper {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) {c : ℝ} (hc : 0 < c)
    (hq0 : q 0 = (c : ℂ)) (A : ℂ) {P : ℝ}
    (hL : ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℝ in 𝓝[>] 1,
      exteriorCircleLength (exteriorFromModel q A) r ≤ P + ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ ρ : ℝ in 𝓝[<] 1,
      c * radialMeanNorm (modelDerivative q) ρ ≤ P / (2 * Real.pi) + ε := by
  intro ε hε
  filter_upwards [tendsto_inverse_radius_one.eventually (hL (2 * Real.pi * ε) (by positivity)),
    self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with ρ hLρ hρ1 hρ0
  have hr : 1 < ρ⁻¹ := (one_lt_inv₀ hρ0).mpr hρ1
  rw [exteriorCircleLength_model hq hc hq0 A hr, inv_inv] at hLρ
  have hM : 0 ≤ c * radialMeanNorm (modelDerivative q) ρ := by
    apply mul_nonneg hc.le
    exact Real.circleAverage_nonneg_of_nonneg (fun _ _ => norm_nonneg _)
  have hh := mul_le_mul_of_nonneg_right hr.le
    (mul_nonneg (show 0 ≤ 2 * Real.pi by positivity) hM)
  have hbound : 2 * Real.pi * (c * radialMeanNorm (modelDerivative q) ρ) ≤ P + 2 * Real.pi * ε := by
    nlinarith
  have hdiv : c * radialMeanNorm (modelDerivative q) ρ ≤
      (P + 2 * Real.pi * ε) / (2 * Real.pi) :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr (by nlinarith)
  convert hdiv using 1
  field_simp

/-- The normalized perimeter `2π` supplies `BoundaryData.radial_perimeter`. -/
theorem radialMeanNorm_normalized_upper_of_circleLength_upper {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) {c : ℝ} (hc : 0 < c)
    (hq0 : q 0 = (c : ℂ)) (A : ℂ)
    (hL : ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℝ in 𝓝[>] 1,
      exteriorCircleLength (exteriorFromModel q A) r ≤ 2 * Real.pi + ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ ρ : ℝ in 𝓝[<] 1,
      c * radialMeanNorm (modelDerivative q) ρ ≤ 1 + ε := by
  simpa only [div_self (show 2 * Real.pi ≠ 0 by positivity)] using
    radialMeanNorm_upper_of_circleLength_upper hq hc hq0 A hL

#print axioms exteriorCircleLength_model
#print axioms radialMeanNorm_normalized_upper_of_circleLength_upper
end
end ExteriorReduction


