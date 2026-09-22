import EventualExact.PolarSlopeEnergy

/-! The polar tangent cone forced by an inner disk and a thin outer annulus. -/

namespace Erdos1045.EventualExact.PolarSlopeEnergy

open Complex Metric Set
open scoped ComplexConjugate
noncomputable section

theorem rotated_norm_sq {ν : ℂ} (hν : ‖ν‖ = 1) (z : ℂ) :
    (conj ν * z).re ^ 2 + (conj ν * z).im ^ 2 = ‖z‖ ^ 2 := by
  have h : ‖conj ν * z‖ ^ 2 = ‖z‖ ^ 2 := by simp [hν]
  rw [Complex.sq_norm] at h
  simpa only [normSq_apply, pow_two] using h

theorem support_distance_of_ball {K : Set ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hball : closedBall 0 r ⊆ K) {ν z : ℂ} (hν : ‖ν‖ = 1)
    (hsupport : ∀ w ∈ K, (conj ν * w).re ≤ (conj ν * z).re) :
    r ≤ (conj ν * z).re := by
  have hw : (r : ℂ) * ν ∈ closedBall 0 r := by
    simp [hν, abs_of_nonneg hr]
  have h := hsupport ((r : ℂ) * ν) (hball hw)
  have hnorm : normSq ν = 1 := by rw [normSq_eq_norm_sq, hν]; norm_num
  have hc : conj ν * ν = 1 := by rw [← normSq_eq_conj_mul_self, hnorm]; norm_num
  have he : conj ν * ((r : ℂ) * ν) = (r : ℂ) := by
    calc
      _ = (r : ℂ) * (conj ν * ν) := by ring
      _ = _ := by rw [hc, mul_one]
  simpa only [he, ofReal_re] using h

theorem radialPairing_tangent (z ν : ℂ) (speed : ℝ) :
    radialPairing z (I * (speed : ℂ) * ν) =
      (speed : ℂ) * ((conj ν * z).im + (conj ν * z).re * I) := by
  apply Complex.ext <;> simp [radialPairing, mul_re, mul_im] <;> ring

/-- The annulus alone controls the ratio of radial to angular velocity. -/
theorem tangent_slope_le {ν z : ℂ} (hν : ‖ν‖ = 1) {r ε speed : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (hsupport : r ≤ (conj ν * z).re)
    (houter : ‖z‖ ^ 2 ≤ r ^ 2 * (1 + ε ^ 2)) :
    |polarSlope z (I * (speed : ℂ) * ν)| ≤ ε := by
  have hn := rotated_norm_sq hν z
  have hre : 0 < (conj ν * z).re := hr.trans_le hsupport
  have hresq : r ^ 2 ≤ (conj ν * z).re ^ 2 := by nlinarith
  have hsq : (conj ν * z).im ^ 2 ≤ ε ^ 2 * (conj ν * z).re ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg ε) (sub_nonneg.mpr hresq)]
  have him : |(conj ν * z).im| ≤ ε * (conj ν * z).re := by
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hε hre.le)).mp
    simpa only [sq_abs, mul_pow] using hsq
  unfold polarSlope
  rw [radialPairing_tangent]
  simp only [mul_re, mul_im, ofReal_re, ofReal_im, add_re, add_im,
    I_re, I_im, mul_zero, zero_mul, add_zero, sub_zero, zero_add, mul_one]
  change |speed * (conj ν * z).im / (speed * (conj ν * z).re)| ≤ ε
  by_cases hspeed : speed = 0
  · simp [hspeed, hε]
  · rw [mul_div_mul_left _ _ hspeed, abs_div, abs_of_pos hre]
    exact (div_le_iff₀ hre).mpr him

theorem tangent_cone_of_support {ν z : ℂ} (hν : ‖ν‖ = 1) {r speed : ℝ}
    (hr : 0 ≤ r) (hspeed : 0 ≤ speed) (hsupport : r ≤ (conj ν * z).re)
    (houter : ‖z‖ ^ 2 ≤ 2 * r ^ 2) :
    |(radialPairing z (I * (speed : ℂ) * ν)).re| ≤
      (radialPairing z (I * (speed : ℂ) * ν)).im := by
  have hn := rotated_norm_sq hν z
  have hre : 0 ≤ (conj ν * z).re := hr.trans hsupport
  have hsq : (conj ν * z).im ^ 2 ≤ (conj ν * z).re ^ 2 := by nlinarith
  have him : |(conj ν * z).im| ≤ (conj ν * z).re := by
    apply (sq_le_sq₀ (abs_nonneg _) hre).mp
    simpa only [sq_abs] using hsq
  rw [radialPairing_tangent]
  simp only [mul_re, mul_im, ofReal_re, ofReal_im, add_re, add_im,
    I_re, I_im, mul_zero, zero_mul, add_zero, sub_zero, zero_add, mul_one]
  rw [abs_mul, abs_of_nonneg hspeed]
  exact mul_le_mul_of_nonneg_left him hspeed

theorem slopeDensity_le_errors_of_support {K : Set ℂ} {r speed : ℝ}
    (hr : 0 ≤ r) (hball : closedBall 0 r ⊆ K) {ν u z : ℂ}
    (hν : ‖ν‖ = 1) (hu : ‖u‖ = 1) (hspeed : 0 ≤ speed)
    (hsupport : ∀ w ∈ K, (conj ν * w).re ≤ (conj ν * z).re)
    (houter : ‖z‖ ^ 2 ≤ 2 * r ^ 2) (hzlo : 1 / 2 ≤ ‖z‖) (hzhi : ‖z‖ ≤ 2) :
    slopeDensity z (I * (speed : ℂ) * ν) ≤
      64 * ‖I * (speed : ℂ) * ν - I * u‖ ^ 2 + 16 * ‖z - u‖ ^ 2 :=
  slopeDensity_le_errors hu hzlo hzhi
    (tangent_cone_of_support hν hr hspeed (support_distance_of_ball hr hball hν hsupport) houter)

end
end Erdos1045.EventualExact.PolarSlopeEnergy
