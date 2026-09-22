import LaurentEnergyRadial
import LaurentEnergySummable
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The actual Laurent energy is the limit of finite-circle energies

The preliminary square summability comes from the analytic convexity criterion.
Only the geometric mean-length limit is needed for the capacity-defect estimate.
An eventual bound B on the normalized derivative retains the sharp factor B+1.
-/

namespace ExteriorReduction

open Complex Metric Set Filter
open FaberKernel
open scoped Topology
noncomputable section

theorem radial_weighted_tsum_tendsto {a : ℕ → ℝ}
    (ha : ∀ m, 0 ≤ a m) (hs : Summable a) :
    Tendsto (fun r : ℝ => ∑' m, a m * r ^ (2 * (m + 1)))
      (𝓝[<] 1) (𝓝 (∑' m, a m)) := by
  apply tendsto_tsum_of_dominated_convergence hs
  · intro m
    have hc : Continuous (fun r : ℝ => a m * r ^ (2 * (m + 1))) := by fun_prop
    simpa only [one_pow, mul_one] using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with r hr1 hr0 m
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (ha m) (pow_nonneg hr0.le _))]
    exact mul_le_of_le_one_right (ha m) (pow_le_one₀ hr0.le hr1.le)

theorem raw_laurent_energy_limit_of_summable {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) {c : ℝ} (hc : 0 < c) (hq0 : q 0 = (c : ℂ))
    (hs : Summable (fun m : ℕ => (m : ℝ) ^ 2 * ‖modelLaurentCoefficient q m‖ ^ 2)) :
    Tendsto (fun r => 2 * Real.pi * c ^ 2 * radialMeanEnergy (modelDerivative q) r)
      (𝓝[<] (1 : ℝ))
      (𝓝 (Erdos1045.ExteriorClassical.sobolevEnergySquared (modelLaurentCoefficient q))) := by
  have ht := (radial_weighted_tsum_tendsto (fun m => by positivity) hs).const_mul (2 * Real.pi)
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with r hr1 hr0
  exact (raw_laurent_radial_energy hq hc hq0 hr0.le hr1).symm

/-- The limit statement has no Sobolev or Parseval hypothesis. -/
theorem raw_laurent_energy_limit_of_criterion {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) {c : ℝ} (hc : 0 < c) (hq0 : q 0 = (c : ℂ))
    (hne : ∀ z ∈ ball (0 : ℂ) 1, modelDerivative q z ≠ 0)
    (hpos : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ (derivativeCriterion (modelDerivative q) z).re) :
    Tendsto (fun r => 2 * Real.pi * c ^ 2 * radialMeanEnergy (modelDerivative q) r)
      (𝓝[<] (1 : ℝ))
      (𝓝 (Erdos1045.ExteriorClassical.sobolevEnergySquared (modelLaurentCoefficient q))) := by
  have hqne : q 0 ≠ 0 := hq0 ▸ Complex.ofReal_ne_zero.mpr hc.ne'
  have hs := model_laurent_sobolev_of_criterion hq hqne hne hpos
  exact raw_laurent_energy_limit_of_summable hq hc hq0
    (Erdos1045.FaberFourier.coefficient_energies_summable hs.2).2

/-- The geometric input is precisely c times the circle mean of |D| tending
to one. An eventual upper bound B gives the sharp 4*pi*c*(B+1) coefficient. -/
theorem raw_laurent_energy_bound {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) {c B : ℝ} (hc : 0 < c) (hq0 : q 0 = (c : ℂ))
    (hne : ∀ z ∈ ball (0 : ℂ) 1, modelDerivative q z ≠ 0)
    (hpos : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ (derivativeCriterion (modelDerivative q) z).re)
    (hB : 1 ≤ B)
    (hbound : ∀ᶠ r : ℝ in 𝓝[<] 1, ∀ z ∈ sphere (0 : ℂ) r, ‖modelDerivative q z‖ ≤ B)
    (hL : Tendsto (fun r => c * radialMeanNorm (modelDerivative q) r)
      (𝓝[<] (1 : ℝ)) (𝓝 1)) :
    Erdos1045.ExteriorClassical.sobolevEnergySquared (modelLaurentCoefficient q) ≤
      4 * Real.pi * c * (B + 1) * (1 - c) := by
  have hqne : q 0 ≠ 0 := hq0 ▸ Complex.ofReal_ne_zero.mpr hc.ne'
  have hleft := raw_laurent_energy_limit_of_criterion hq hc hq0 hne hpos
  have hright := (hL.sub_const c).const_mul (4 * Real.pi * c * (B + 1))
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [hbound, self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with r hrB hr1 hr0
  exact analytic_disk_scaled_energy_bound (c := c) (modelDerivative_analytic hq hqne)
    hne (modelDerivative_zero hqne) hr0.le hr1 hB hrB

theorem raw_laurent_coarse_energy_bound {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) {c : ℝ} (hc : 0 < c) (hq0 : q 0 = (c : ℂ))
    (hne : ∀ z ∈ ball (0 : ℂ) 1, modelDerivative q z ≠ 0)
    (hpos : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ (derivativeCriterion (modelDerivative q) z).re)
    (hL : Tendsto (fun r => c * radialMeanNorm (modelDerivative q) r)
      (𝓝[<] (1 : ℝ)) (𝓝 1)) :
    Erdos1045.ExteriorClassical.sobolevEnergySquared (modelLaurentCoefficient q) ≤
      12 * Real.pi * c * (1 - c) := by
  have hqne : q 0 ≠ 0 := hq0 ▸ Complex.ofReal_ne_zero.mpr hc.ne'
  have hbound : ∀ᶠ r : ℝ in 𝓝[<] 1,
      ∀ z ∈ sphere (0 : ℂ) r, ‖modelDerivative q z‖ ≤ 2 := by
    filter_upwards [self_mem_nhdsWithin] with r hr1 z hz
    exact normalized_derivative_le_two (modelDerivative_analytic hq hqne) hne
      (modelDerivative_zero hqne) (modelDerivative_hasDerivAt_zero (hq 0 (by simp))).deriv hpos
      (sphere_subset_ball hr1 hz)
  have he := raw_laurent_energy_bound hq hc hq0 hne hpos (by norm_num : (1 : ℝ) ≤ 2) hbound hL
  convert he using 1
  ring

#print axioms raw_laurent_energy_limit_of_criterion
#print axioms raw_laurent_energy_bound
#print axioms raw_laurent_coarse_energy_bound

end
end ExteriorReduction
