import LaurentEnergyLimit

/-! A geometric upper limit for radial length already suffices. Existence of
a perimeter limit and equality of boundary length are unnecessary. -/

namespace ExteriorReduction

open Complex Metric Set Filter
open scoped Topology
noncomputable section

theorem raw_laurent_energy_bound_of_length_upper {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) {c B : ℝ} (hc : 0 < c) (hq0 : q 0 = (c : ℂ))
    (hne : ∀ z ∈ ball (0 : ℂ) 1, modelDerivative q z ≠ 0)
    (hpos : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ (derivativeCriterion (modelDerivative q) z).re)
    (hB : 1 ≤ B)
    (hbound : ∀ᶠ r : ℝ in 𝓝[<] 1, ∀ z ∈ sphere (0 : ℂ) r, ‖modelDerivative q z‖ ≤ B)
    (hL : ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℝ in 𝓝[<] 1,
      c * radialMeanNorm (modelDerivative q) r ≤ 1 + ε) :
    Erdos1045.ExteriorClassical.sobolevEnergySquared (modelLaurentCoefficient q) ≤
      4 * Real.pi * c * (B + 1) * (1 - c) := by
  have hqne : q 0 ≠ 0 := hq0 ▸ Complex.ofReal_ne_zero.mpr hc.ne'
  have hleft := raw_laurent_energy_limit_of_criterion hq hc hq0 hne hpos
  have hC : 0 ≤ 4 * Real.pi * c * (B + 1) := by positivity
  have hε (ε : ℝ) (hε : 0 < ε) :
      Erdos1045.ExteriorClassical.sobolevEnergySquared (modelLaurentCoefficient q) ≤
        4 * Real.pi * c * (B + 1) * (1 + ε - c) := by
    apply le_of_tendsto_of_tendsto hleft tendsto_const_nhds
    filter_upwards [hL ε hε, hbound, self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with r hrl hrB hr1 hr0
    exact (analytic_disk_scaled_energy_bound (c := c) (modelDerivative_analytic hq hqne)
      hne (modelDerivative_zero hqne) hr0.le hr1 hB hrB).trans
      (mul_le_mul_of_nonneg_left (sub_le_sub_right hrl c) hC)
  have ht : Tendsto (fun ε : ℝ => 4 * Real.pi * c * (B + 1) * (1 + ε - c))
      (𝓝[>] 0) (𝓝 (4 * Real.pi * c * (B + 1) * (1 - c))) := by
    have ht := (show Continuous (fun ε : ℝ => 4 * Real.pi * c * (B + 1) * (1 + ε - c))
      by fun_prop).tendsto 0
    simpa only [add_zero] using ht.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto tendsto_const_nhds ht
  filter_upwards [self_mem_nhdsWithin] with ε hεpos
  exact hε ε hεpos

theorem raw_laurent_coarse_energy_of_length_upper {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) {c : ℝ} (hc : 0 < c) (hq0 : q 0 = (c : ℂ))
    (hne : ∀ z ∈ ball (0 : ℂ) 1, modelDerivative q z ≠ 0)
    (hpos : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ (derivativeCriterion (modelDerivative q) z).re)
    (hL : ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℝ in 𝓝[<] 1,
      c * radialMeanNorm (modelDerivative q) r ≤ 1 + ε) :
    Erdos1045.ExteriorClassical.sobolevEnergySquared (modelLaurentCoefficient q) ≤
      12 * Real.pi * c * (1 - c) := by
  have hqne : q 0 ≠ 0 := hq0 ▸ Complex.ofReal_ne_zero.mpr hc.ne'
  have hb : ∀ᶠ r : ℝ in 𝓝[<] 1,
      ∀ z ∈ sphere (0 : ℂ) r, ‖modelDerivative q z‖ ≤ 2 := by
    filter_upwards [self_mem_nhdsWithin] with r hr z hz
    exact normalized_derivative_le_two (modelDerivative_analytic hq hqne) hne
      (modelDerivative_zero hqne) (modelDerivative_hasDerivAt_zero (hq 0 (by simp))).deriv
      hpos (sphere_subset_ball hr hz)
  have he := raw_laurent_energy_bound_of_length_upper hq hc hq0 hne hpos
    (by norm_num : (1 : ℝ) ≤ 2) hb hL
  convert he using 1
  ring

#print axioms raw_laurent_energy_bound_of_length_upper

end
end ExteriorReduction
