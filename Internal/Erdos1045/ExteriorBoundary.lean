import LaurentEnergyUpper

/-! Boundary estimates from the analytic model at infinity and radial length.
No Schwarz--Christoffel factors, boundary square root or boundary derivative. -/

namespace Erdos1045.ExteriorBoundary

open Complex Metric Set Filter ExteriorReduction ExteriorClassical
open scoped Topology
noncomputable section

def unit (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

@[simp] theorem norm_unit (t : ℝ) : ‖unit t‖ = 1 := by
  simp [unit, Complex.norm_exp]

structure BoundaryData where
  capacity : ℝ
  capacity_pos : 0 < capacity
  model : ℂ → ℂ
  model_analytic : AnalyticOnNhd ℂ model (ball 0 1)
  model_zero : model 0 = (capacity : ℂ)
  model_derivative_ne : ∀ z ∈ ball (0 : ℂ) 1, modelDerivative model z ≠ 0
  model_criterion : ∀ z ∈ ball (0 : ℂ) 1,
    0 ≤ (derivativeCriterion (modelDerivative model) z).re
  radial_perimeter : ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℝ in 𝓝[<] 1,
    capacity * radialMeanNorm (modelDerivative model) r ≤ 1 + ε

theorem BoundaryData.model_zero_ne (d : BoundaryData) : d.model 0 ≠ 0 :=
  d.model_zero ▸ Complex.ofReal_ne_zero.mpr d.capacity_pos.ne'

def BoundaryData.derivative (d : BoundaryData) (w : ℂ) : ℂ :=
  (d.capacity : ℂ) * modelDerivative d.model w⁻¹

def BoundaryData.energySquared (d : BoundaryData) : ℝ :=
  sobolevEnergySquared (modelLaurentCoefficient d.model)

theorem BoundaryData.energySquared_nonneg (d : BoundaryData) : 0 ≤ d.energySquared := by
  apply mul_nonneg (by positivity)
  exact tsum_nonneg fun m => mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem BoundaryData.capacity_le_one (d : BoundaryData) : d.capacity ≤ 1 := by
  have he := raw_laurent_coarse_energy_of_length_upper d.model_analytic d.capacity_pos d.model_zero
    d.model_derivative_ne d.model_criterion d.radial_perimeter
  have hh : 0 ≤ 12 * Real.pi * d.capacity * (1 - d.capacity) :=
    d.energySquared_nonneg.trans he
  have hc := nonneg_of_mul_nonneg_right hh
    (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 12) Real.pi_pos) d.capacity_pos)
  linarith

theorem BoundaryData.derivative_le (d : BoundaryData) {w : ℂ} (hw : 1 < ‖w‖) :
    ‖d.derivative w‖ ≤ 4 * d.capacity := by
  have hb := normalized_derivative_le_two
    (modelDerivative_analytic d.model_analytic d.model_zero_ne) d.model_derivative_ne
    (modelDerivative_zero d.model_zero_ne)
    (modelDerivative_hasDerivAt_zero (d.model_analytic 0 (by simp))).deriv d.model_criterion
    (inv_mem_disk_of_exterior hw)
  rw [BoundaryData.derivative, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos d.capacity_pos]
  nlinarith [d.capacity_pos]

theorem BoundaryData.coarse_energy (d : BoundaryData) :
    d.energySquared ≤ 18 * Real.pi * (1 - d.capacity) := by
  have he := raw_laurent_coarse_energy_of_length_upper d.model_analytic d.capacity_pos d.model_zero
    d.model_derivative_ne d.model_criterion d.radial_perimeter
  have hc := d.capacity_le_one
  have hm := mul_le_mul_of_nonneg_right hc (show 0 ≤ 12 * Real.pi * (1 - d.capacity) by positivity)
  change sobolevEnergySquared _ ≤ _
  nlinarith [Real.pi_pos]

/-- Interior-circle bounds give the sharp energy coefficient. -/
theorem BoundaryData.sharp_energy (d : BoundaryData) {e : ℝ} (he : 0 ≤ e)
    (hupper : ∀ᶠ r : ℝ in 𝓝[<] 1, ∀ z ∈ sphere (0 : ℂ) r,
      ‖modelDerivative d.model z‖ ≤ 1 + e) :
    d.energySquared ≤ 8 * Real.pi * d.capacity * (1 - d.capacity) * (1 + e / 2) := by
  have h := raw_laurent_energy_bound_of_length_upper d.model_analytic d.capacity_pos d.model_zero
    d.model_derivative_ne d.model_criterion (by linarith : (1 : ℝ) ≤ 1 + e)
    hupper d.radial_perimeter
  convert h using 1 <;> first | rfl | ring

/-- Propagate a bound on one interior circle to radii approaching one. -/
theorem BoundaryData.eventual_model_bound (d : BoundaryData) {a B : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1)
    (hB : ∀ u : ℂ, ‖u‖ = 1 → ‖modelDerivative d.model ((a : ℂ) * u)‖ ≤ a * B) :
    ∀ᶠ r : ℝ in 𝓝[<] 1, ∀ z ∈ sphere (0 : ℂ) r, ‖modelDerivative d.model z‖ ≤ B := by
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Ioi_mem_nhds ha1)] with r hr har z hz
  have hr0 : 0 < r := ha0.trans har
  have hzn : ‖z‖ = r := mem_sphere_zero_iff_norm.mp hz
  let u : ℂ := z / (r : ℂ)
  have hu : ‖u‖ = 1 := by simp [u, hzn, abs_of_pos hr0, hr0.ne']
  have hzu : (r : ℂ) * u = z := by
    dsimp [u]
    field_simp [Complex.ofReal_ne_zero.mpr hr0.ne']
  have hrad := normalized_derivative_radial_comparison
    (modelDerivative_analytic d.model_analytic d.model_zero_ne) d.model_derivative_ne
    d.model_criterion hu ha0 har.le hr
  rw [hzu] at hrad
  have hb := hB u hu
  have hnorm := norm_nonneg (modelDerivative d.model ((a : ℂ) * u))
  have hmul := mul_le_mul_of_nonneg_right hr.le hnorm
  nlinarith

#print axioms BoundaryData.sharp_energy

end
end Erdos1045.ExteriorBoundary
