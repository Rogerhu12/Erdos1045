import Mathlib.Analysis.Complex.Norm
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! Direct control of polar slope energy by position and velocity errors.
The pointwise estimate allows stationary boundary parameters and uses a tangent
cone condition, rather than a positive lower bound on parametrization speed. -/

namespace Erdos1045.EventualExact.PolarSlopeEnergy

open Complex MeasureTheory
open scoped ComplexConjugate
noncomputable section

def radialPairing (z v : ℂ) : ℂ := conj z * v

def angularSpeed (z v : ℂ) : ℝ := (radialPairing z v).im / ‖z‖ ^ 2

def polarSlope (z v : ℂ) : ℝ := (radialPairing z v).re / (radialPairing z v).im

def slopeDensity (z v : ℂ) : ℝ :=
  (radialPairing z v).re ^ 2 / (‖z‖ ^ 2 * (radialPairing z v).im)

theorem slopeDensity_eq (z v : ℂ) :
    slopeDensity z v = polarSlope z v ^ 2 * angularSpeed z v := by
  unfold slopeDensity polarSlope angularSpeed
  by_cases ha : (radialPairing z v).im = 0
  · simp [ha]
  · field_simp

theorem slopeDensity_nonneg {z v : ℂ} (hcone : |(radialPairing z v).re| ≤
    (radialPairing z v).im) : 0 ≤ slopeDensity z v := by
  have ha := (abs_nonneg (radialPairing z v).re).trans hcone
  unfold slopeDensity
  positivity

theorem quotient_le_error {a b : ℝ} (ha : 0 ≤ a) (hb : |b| ≤ a) :
    b ^ 2 / a ≤ 2 * (b ^ 2 + (a - 1) ^ 2) := by
  by_cases hz : a = 0
  · simp only [hz, div_zero]
    positivity
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
  by_cases hhalf : 1 / 2 ≤ a
  · apply (div_le_iff₀ ha').mpr
    nlinarith [mul_nonneg (show 0 ≤ 2 * a - 1 by linarith) (sq_nonneg b),
      mul_nonneg ha (sq_nonneg (a - 1))]
  · have hb2 : b ^ 2 ≤ a ^ 2 := by
      have h := (sq_le_sq₀ (abs_nonneg b) ha).mpr hb
      simpa only [sq_abs] using h
    have hdiv : b ^ 2 / a ≤ a := (div_le_iff₀ ha').mpr (by nlinarith)
    have hlast : a ≤ 2 * (a - 1) ^ 2 := by nlinarith
    nlinarith [sq_nonneg b]

theorem norm_sub_I_sq (q : ℂ) :
    ‖q - I‖ ^ 2 = q.re ^ 2 + (q.im - 1) ^ 2 := by
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply, pow_two]

theorem slopeDensity_le_pairing_error {z v : ℂ} (hz : 1 / 2 ≤ ‖z‖)
    (hcone : |(radialPairing z v).re| ≤ (radialPairing z v).im) :
    slopeDensity z v ≤ 8 * ‖radialPairing z v - I‖ ^ 2 := by
  have ha := (abs_nonneg (radialPairing z v).re).trans hcone
  have hn : 0 < ‖z‖ ^ 2 := by positivity
  have hnlow : 1 / 4 ≤ ‖z‖ ^ 2 := by nlinarith
  have hq := quotient_le_error ha hcone
  rw [← norm_sub_I_sq] at hq
  calc
    slopeDensity z v = ((radialPairing z v).re ^ 2 / (radialPairing z v).im) /
        ‖z‖ ^ 2 := by unfold slopeDensity; ring
    _ ≤ (2 * ‖radialPairing z v - I‖ ^ 2) / ‖z‖ ^ 2 :=
      div_le_div_of_nonneg_right hq hn.le
    _ ≤ 8 * ‖radialPairing z v - I‖ ^ 2 := by
      apply (div_le_iff₀ hn).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hnlow) (sq_nonneg ‖radialPairing z v - I‖)]

theorem pairing_error_decomposition {u : ℂ} (hu : ‖u‖ = 1) (z v : ℂ) :
    radialPairing z v - I = conj z * (v - I * u) + conj (z - u) * (I * u) := by
  have hn : normSq u = 1 := by rw [normSq_eq_norm_sq, hu]; norm_num
  have hc : conj u * u = 1 := by rw [← normSq_eq_conj_mul_self, hn]; norm_num
  unfold radialPairing
  rw [map_sub]
  linear_combination I * hc

theorem pairing_error_le {u z v : ℂ} (hu : ‖u‖ = 1) (hz : ‖z‖ ≤ 2) :
    ‖radialPairing z v - I‖ ≤ 2 * ‖v - I * u‖ + ‖z - u‖ := by
  rw [pairing_error_decomposition hu]
  calc
    _ ≤ ‖conj z * (v - I * u)‖ + ‖conj (z - u) * (I * u)‖ := norm_add_le _ _
    _ = ‖z‖ * ‖v - I * u‖ + ‖z - u‖ := by
      simp only [norm_mul, norm_conj, norm_I, hu, mul_one]
    _ ≤ _ := by gcongr

/-- No nonvanishing boundary velocity is needed in this direct energy estimate. -/
theorem slopeDensity_le_errors {u z v : ℂ} (hu : ‖u‖ = 1)
    (hzlo : 1 / 2 ≤ ‖z‖) (hzhi : ‖z‖ ≤ 2)
    (hcone : |(radialPairing z v).re| ≤ (radialPairing z v).im) :
    slopeDensity z v ≤ 64 * ‖v - I * u‖ ^ 2 + 16 * ‖z - u‖ ^ 2 := by
  have h1 := slopeDensity_le_pairing_error hzlo hcone
  have h2 := pairing_error_le (v := v) hu hzhi
  have hsq : ‖radialPairing z v - I‖ ^ 2 ≤
      (2 * ‖v - I * u‖ + ‖z - u‖) ^ 2 := by gcongr
  nlinarith [sq_nonneg (2 * ‖v - I * u‖ - ‖z - u‖)]

theorem integral_slopeDensity_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {u z v : α → ℂ}
    (hd : Integrable (fun t => slopeDensity (z t) (v t)) μ)
    (hv : Integrable (fun t => ‖v t - I * u t‖ ^ 2) μ)
    (hz : Integrable (fun t => ‖z t - u t‖ ^ 2) μ)
    (hgeom : ∀ᵐ t ∂μ, ‖u t‖ = 1 ∧ 1 / 2 ≤ ‖z t‖ ∧ ‖z t‖ ≤ 2 ∧
      |(radialPairing (z t) (v t)).re| ≤ (radialPairing (z t) (v t)).im) :
    (∫ t, slopeDensity (z t) (v t) ∂μ) ≤
      64 * (∫ t, ‖v t - I * u t‖ ^ 2 ∂μ) + 16 * (∫ t, ‖z t - u t‖ ^ 2 ∂μ) := by
  have hbound : ∀ᵐ t ∂μ, slopeDensity (z t) (v t) ≤
      64 * ‖v t - I * u t‖ ^ 2 + 16 * ‖z t - u t‖ ^ 2 := by
    filter_upwards [hgeom] with t ht
    exact slopeDensity_le_errors ht.1 ht.2.1 ht.2.2.1 ht.2.2.2
  have h := integral_mono_ae hd ((hv.const_mul 64).add (hz.const_mul 16)) hbound
  calc
    _ ≤ ∫ t, 64 * ‖v t - I * u t‖ ^ 2 + 16 * ‖z t - u t‖ ^ 2 ∂μ := h
    _ = _ := by
      rw [integral_add (hv.const_mul 64) (hz.const_mul 16), integral_const_mul, integral_const_mul]

end
end Erdos1045.EventualExact.PolarSlopeEnergy
