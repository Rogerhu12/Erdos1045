import EventualExact.PhysicalAngles
import EventualExact.AngularHarmonicBound

/-! Converting physical separation to polar separation using finite support data. -/

namespace Erdos1045.EventualExact.ExteriorSupport

open Complex Set ExteriorClassical ExteriorBoundary Configuration CyclicAngles
open scoped ComplexConjugate
noncomputable section

theorem radius_pair_bound {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (hc : 1 / 2 ≤ d.capacity) (he : errorRadius d ≤ 1 / 4)
    {w v ν μ : ℂ} (hw : w ∈ hull z) (hv : v ∈ hull z)
    (hν : ‖ν‖ = 1) (hμ : ‖μ‖ = 1)
    (hsw : ∀ a ∈ hull z, (conj ν * (a - center d)).re ≤ (conj ν * (w - center d)).re)
    (hsv : ∀ a ∈ hull z, (conj μ * (a - center d)).re ≤ (conj μ * (v - center d)).re)
    {R S θ x : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hwpolar : w - center d = (R : ℂ) * unit θ)
    (hvpolar : v - center d = (S : ℂ) * unit (θ + x)) :
    |S - R| ≤ 12 * Real.sqrt (errorRadius d) * |x| := by
  have hr := point_radius_bounds d HF hc he hw hν hsw hR hwpolar
  have hs := point_radius_bounds d HF hc he hv hμ hsv hS hvpolar
  have hsp : |S - R| ≤ 2 * errorRadius d := by
    apply abs_le.mpr
    constructor <;> linarith [hr.1, hr.2.1, hs.1, hs.2.1]
  have ht := tangent_slope_le_error d HF hc he hν hw hsw 1
  have hu := tangent_slope_le_error d HF hc he hμ hv hsv 1
  simp only [ofReal_one, mul_one] at ht hu
  rw [hwpolar, tangent_slope_eq (by linarith [hr.2.2.1] : R ≠ 0)] at ht
  rw [hvpolar, tangent_slope_eq (by linarith [hs.2.2.1] : S ≠ 0)] at hu
  apply RadialControl.abs_radius_difference_le (errorRadius_nonneg d)
    hR hS hr.2.2.2.1 hs.2.2.2.1 hsp ht hu
  · apply support_polar_inequality hr.2.2.2.2
    simpa only [hwpolar, hvpolar] using hsw v hv
  · apply support_polar_inequality hs.2.2.2.2
    simpa only [hwpolar, hvpolar, add_neg_cancel_right] using hsv w hw

theorem unit_increment_norm_le (θ x : ℝ) : ‖unit (θ + x) - unit θ‖ ≤ |x| := by
  rw [unit_add, show unit θ * unit x - unit θ = unit θ * (unit x - 1) by ring,
    norm_mul, norm_unit, one_mul]
  simpa [unit, mul_comm, Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x))

theorem point_pair_bound {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (hc : 1 / 2 ≤ d.capacity) (he : errorRadius d ≤ 1 / 4)
    {w v ν μ : ℂ} (hw : w ∈ hull z) (hv : v ∈ hull z)
    (hν : ‖ν‖ = 1) (hμ : ‖μ‖ = 1)
    (hsw : ∀ a ∈ hull z, (conj ν * (a - center d)).re ≤ (conj ν * (w - center d)).re)
    (hsv : ∀ a ∈ hull z, (conj μ * (a - center d)).re ≤ (conj μ * (v - center d)).re)
    {R S θ x : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hwpolar : w - center d = (R : ℂ) * unit θ)
    (hvpolar : v - center d = (S : ℂ) * unit (θ + x)) :
    ‖v - w‖ ≤ 8 * |x| := by
  have hr := radius_pair_bound d HF hc he hw hv hν hμ hsw hsv hR hS hwpolar hvpolar
  have hs := point_radius_bounds d HF hc he hv hμ hsv hS hvpolar
  have heq : v - w = ((S - R : ℝ) : ℂ) * unit θ +
      (S : ℂ) * (unit (θ + x) - unit θ) := by
    rw [ofReal_sub]
    linear_combination hvpolar - hwpolar
  have ht := norm_add_le (((S - R : ℝ) : ℂ) * unit θ)
    ((S : ℂ) * (unit (θ + x) - unit θ))
  rw [← heq] at ht
  simp only [norm_mul, norm_unit, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hS] at ht
  have hu := mul_le_mul_of_nonneg_left (unit_increment_norm_le θ x) hS
  have hrt : Real.sqrt (errorRadius d) ≤ 1 / 2 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num, by nlinarith⟩
  have hm := mul_le_mul_of_nonneg_right hrt (abs_nonneg x)
  have hsm := mul_le_mul_of_nonneg_right hs.2.2.2.1 (abs_nonneg x)
  nlinarith [abs_nonneg x]

theorem unit_shortAngle {n : ℕ} (a : Angles n) (i j : Fin n) :
    unit (AngularHarmonicBound.shortAngle a i j) = unit (a.angle i - a.angle j) := by
  apply Complex.ext
  · simpa only [unit, Complex.exp_ofReal_mul_I_re] using AngularHarmonicBound.shortAngle_cos a i j
  · simpa only [unit, Complex.exp_ofReal_mul_I_im] using AngularHarmonicBound.shortAngle_sin a i j

theorem unit_add_shortAngle {n : ℕ} (a : Angles n) (i j : Fin n) :
    unit (a.angle j + AngularHarmonicBound.shortAngle a i j) = unit (a.angle i) := by
  rw [unit_add, unit_shortAngle, ← unit_add]
  congr 1
  ring

end
end Erdos1045.EventualExact.ExteriorSupport
