import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic

/-!
# Capacity and the boundary square root

This is the integral argument applied to the actual boundary function
`G = sqrt (Ψ' / c)`. We use an arbitrary probability space so normalized
Haar measure on the circle is a direct specialization. Boundary identities
are explicit premises; neither the capacity inequality nor its sharp
improvement is included among the classical inputs.
-/

namespace Erdos1045.CapacityControl

open MeasureTheory
open scoped BigOperators
noncomputable section

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

def energy (c : ℝ) (G : α → ℂ) (μ : Measure α) : ℝ :=
  2 * Real.pi * c ^ 2 * ∫ t, ‖G t ^ 2 - 1‖ ^ 2 ∂μ

theorem norm_sub_one_sq (z : ℂ) :
    ‖z - 1‖ ^ 2 = ‖z‖ ^ 2 - 2 * z.re + 1 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.one_re, Complex.one_im]
  ring

theorem norm_square_sub_one (z : ℂ) :
    ‖z ^ 2 - 1‖ ^ 2 = ‖z - 1‖ ^ 2 * ‖z + 1‖ ^ 2 := by
  rw [show z ^ 2 - 1 = (z - 1) * (z + 1) by ring, norm_mul, mul_pow]

theorem variance_identity (G : α → ℂ)
    (hsq : Integrable (fun t => ‖G t‖ ^ 2) μ)
    (hre : Integrable (fun t => (G t).re) μ)
    (hmean : (∫ t, (G t).re ∂μ) = 1) :
    (∫ t, ‖G t - 1‖ ^ 2 ∂μ) = (∫ t, ‖G t‖ ^ 2 ∂μ) - 1 := by
  simp_rw [norm_sub_one_sq]
  rw [integral_add (f := fun t => ‖G t‖ ^ 2 - 2 * (G t).re)
    (g := fun _ => (1 : ℝ)) (hsq.sub (hre.const_mul 2)) (integrable_const 1),
    integral_sub hsq (hre.const_mul 2), integral_const_mul, hmean]
  simp
  ring

theorem variance_integrable (G : α → ℂ)
    (hsq : Integrable (fun t => ‖G t‖ ^ 2) μ)
    (hre : Integrable (fun t => (G t).re) μ) :
    Integrable (fun t => ‖G t - 1‖ ^ 2) μ := by
  simp_rw [norm_sub_one_sq]
  exact (hsq.sub (hre.const_mul 2)).add (integrable_const 1)

theorem capacity_le_one {c : ℝ} (hc : 0 < c) (G : α → ℂ)
    (hsq : Integrable (fun t => ‖G t‖ ^ 2) μ)
    (hre : Integrable (fun t => (G t).re) μ)
    (hmean : (∫ t, (G t).re ∂μ) = 1)
    (hlength : c * (∫ t, ‖G t‖ ^ 2 ∂μ) = 1) : c ≤ 1 := by
  have hv := integral_nonneg (μ := μ) (f := fun t : α => ‖G t - 1‖ ^ 2)
    (fun t => sq_nonneg ‖G t - 1‖)
  rw [variance_identity G hsq hre hmean] at hv
  nlinarith

/-- The exact loss factor is the supremum of `|G+1|²`. -/
theorem energy_le_variance_factor {c B : ℝ} (G : α → ℂ)
    (hsq : Integrable (fun t => ‖G t‖ ^ 2) μ)
    (hre : Integrable (fun t => (G t).re) μ)
    (henergy : Integrable (fun t => ‖G t ^ 2 - 1‖ ^ 2) μ)
    (hmean : (∫ t, (G t).re ∂μ) = 1)
    (hlength : c * (∫ t, ‖G t‖ ^ 2 ∂μ) = 1)
    (hB : ∀ᵐ t ∂μ, ‖G t + 1‖ ^ 2 ≤ B) :
    energy c G μ ≤ 2 * Real.pi * c * (1 - c) * B := by
  have hvint := variance_integrable G hsq hre
  have hbound : (∫ t, ‖G t ^ 2 - 1‖ ^ 2 ∂μ) ≤
      B * (∫ t, ‖G t - 1‖ ^ 2 ∂μ) := by
    rw [← integral_const_mul]
    apply integral_mono_ae henergy (hvint.const_mul B)
    filter_upwards [hB] with t ht
    rw [norm_square_sub_one]
    nlinarith [mul_le_mul_of_nonneg_left ht (sq_nonneg ‖G t - 1‖)]
  rw [variance_identity G hsq hre hmean] at hbound
  have hmul := mul_le_mul_of_nonneg_left hbound
    (show 0 ≤ 2 * Real.pi * c ^ 2 by positivity)
  have heq : 2 * Real.pi * c ^ 2 * (B * ((∫ t, ‖G t‖ ^ 2 ∂μ) - 1)) =
      2 * Real.pi * c * (1 - c) * B := by
    calc
      _ = 2 * Real.pi * c * B * (c * (∫ t, ‖G t‖ ^ 2 ∂μ) - c) := by ring
      _ = _ := by rw [hlength]; ring
  exact hmul.trans_eq heq

theorem norm_add_one_sq_le {z : ℂ} {B : ℝ} (hz : ‖z‖ ^ 2 ≤ B) :
    ‖z + 1‖ ^ 2 ≤ 2 * B + 2 := by
  have htri : ‖z + 1‖ ≤ ‖z‖ + 1 := by simpa using norm_add_le z 1
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) htri 2
  nlinarith [sq_nonneg (‖z‖ - 1)]

/-- Equation (3.4), using the classical SC bound `|G|≤2`. -/
theorem coarse_energy_bound {c : ℝ} (hc : 0 < c) (G : α → ℂ)
    (hsq : Integrable (fun t => ‖G t‖ ^ 2) μ)
    (hre : Integrable (fun t => (G t).re) μ)
    (henergy : Integrable (fun t => ‖G t ^ 2 - 1‖ ^ 2) μ)
    (hmean : (∫ t, (G t).re ∂μ) = 1)
    (hlength : c * (∫ t, ‖G t‖ ^ 2 ∂μ) = 1)
    (hG : ∀ᵐ t ∂μ, ‖G t‖ ≤ 2) :
    energy c G μ ≤ 18 * Real.pi * (1 - c) := by
  have hB : ∀ᵐ t ∂μ, ‖G t + 1‖ ^ 2 ≤ 9 := by
    filter_upwards [hG] with t ht
    have htri : ‖G t + 1‖ ≤ ‖G t‖ + 1 := by simpa using norm_add_le (G t) 1
    nlinarith [sq_nonneg ‖G t + 1‖, norm_nonneg (G t + 1)]
  have he := energy_le_variance_factor G hsq hre henergy hmean hlength hB
  have hc1 := capacity_le_one hc G hsq hre hmean hlength
  have hcδ := mul_le_mul_of_nonneg_right hc1 (show 0 ≤ 1 - c by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hcδ (show 0 ≤ 18 * Real.pi by positivity)]

/-- Equation (3.5), with a free error parameter that tends to zero later. -/
theorem sharp_energy_bound {c s : ℝ} (G : α → ℂ)
    (hsq : Integrable (fun t => ‖G t‖ ^ 2) μ)
    (hre : Integrable (fun t => (G t).re) μ)
    (henergy : Integrable (fun t => ‖G t ^ 2 - 1‖ ^ 2) μ)
    (hmean : (∫ t, (G t).re ∂μ) = 1)
    (hlength : c * (∫ t, ‖G t‖ ^ 2 ∂μ) = 1)
    (hG : ∀ᵐ t ∂μ, ‖G t‖ ^ 2 ≤ 1 + 3 * s) :
    energy c G μ ≤ 8 * Real.pi * c * (1 - c) * (1 + 3 * s / 2) := by
  have hB : ∀ᵐ t ∂μ, ‖G t + 1‖ ^ 2 ≤ 4 + 6 * s := by
    filter_upwards [hG] with t ht
    have h := norm_add_one_sq_le ht
    linarith
  have he := energy_le_variance_factor G hsq hre henergy hmean hlength hB
  nlinarith

/-- The elementary SC factor comparison used to move off the boundary. -/
theorem radial_factor_sq {r : ℝ} (hr : 1 ≤ r) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖1 - z‖ ^ 2 ≤ r * ‖1 - z / (r : ℂ)‖ ^ 2 := by
  have hr0 : (0 : ℝ) < r := by linarith
  have hrne : r ≠ 0 := ne_of_gt hr0
  have hzsq : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h := Complex.sq_norm z
    rw [hz] at h
    simpa [Complex.normSq_apply, pow_two] using h.symm
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.one_re, Complex.one_im, Complex.div_ofReal_re,
    Complex.div_ofReal_im]
  apply (mul_le_mul_iff_left₀ hr0).mp
  field_simp
  nlinarith [sq_nonneg (r - 1)]

end
end Erdos1045.CapacityControl
