import EventualExact.ExteriorSupportBounds
import EventualExact.PointwiseRadialControl

/-! Pairwise logarithmic radial control directly from actual support normals. -/

namespace Erdos1045.EventualExact.ExteriorSupport

open Complex Set ExteriorClassical ExteriorBoundary Configuration
open scoped ComplexConjugate
noncomputable section

theorem tangent_slope_eq {R : ℝ} (hR : R ≠ 0) (ν : ℂ) (θ : ℝ) :
    PolarSlopeEnergy.polarSlope ((R : ℂ) * unit θ) (I * ν) =
      (conj ν * unit θ).im / (conj ν * unit θ).re := by
  have he := PolarSlopeEnergy.radialPairing_tangent ((R : ℂ) * unit θ) ν 1
  simp only [ofReal_one, mul_one, one_mul] at he
  have hc : conj ν * ((R : ℂ) * unit θ) = (R : ℂ) * (conj ν * unit θ) := by ring
  rw [hc] at he
  unfold PolarSlopeEnergy.polarSlope
  rw [he]
  simpa only [add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im,
    I_re, I_im, mul_zero, zero_mul, add_zero, zero_add, sub_zero, mul_one] using
    (mul_div_mul_left (conj ν * unit θ).im (conj ν * unit θ).re hR)

theorem unit_add (θ x : ℝ) : unit (θ + x) = unit θ * unit x := by
  unfold unit
  rw [ofReal_add, add_mul, Complex.exp_add]

theorem normal_unit_re (ν : ℂ) (θ x : ℝ) :
    (conj ν * unit (θ + x)).re =
      (conj ν * unit θ).re * Real.cos x - (conj ν * unit θ).im * Real.sin x := by
  rw [unit_add, ← mul_assoc, mul_re]
  simp [unit, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem support_polar_inequality {R S θ x : ℝ} {ν : ℂ}
    (ha : 0 < (conj ν * unit θ).re)
    (hs : (conj ν * ((S : ℂ) * unit (θ + x))).re ≤
      (conj ν * ((R : ℂ) * unit θ)).re) :
    S * (Real.cos x - ((conj ν * unit θ).im / (conj ν * unit θ).re) * Real.sin x) ≤ R := by
  have hsr : S * ((conj ν * unit θ).re * Real.cos x -
      (conj ν * unit θ).im * Real.sin x) ≤ R * (conj ν * unit θ).re := by
    have hc (r t : ℝ) : (conj ν * ((r : ℂ) * unit t)).re =
        r * (conj ν * unit t).re := by
      rw [show conj ν * ((r : ℂ) * unit t) = (r : ℂ) * (conj ν * unit t) by ring]
      simp
    simpa only [hc, normal_unit_re] using hs
  apply (mul_le_mul_iff_right₀ ha).mp
  calc
    _ = S * ((conj ν * unit θ).re * Real.cos x -
        (conj ν * unit θ).im * Real.sin x) := by field_simp [ha.ne']
    _ ≤ _ := by simpa only [mul_comm] using hsr

theorem point_radius_bounds {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (hc : 1 / 2 ≤ d.capacity) (he : errorRadius d ≤ 1 / 4)
    {w ν : ℂ} (hw : w ∈ hull z) (hν : ‖ν‖ = 1)
    (hs : ∀ v ∈ hull z, (conj ν * (v - center d)).re ≤ (conj ν * (w - center d)).re)
    {R θ : ℝ} (hR : 0 ≤ R) (hwpolar : w - center d = (R : ℂ) * unit θ) :
    d.capacity - errorRadius d ≤ R ∧ R ≤ d.capacity + errorRadius d ∧
      1 / 4 ≤ R ∧ R ≤ 5 / 4 ∧ 0 < (conj ν * unit θ).re := by
  have hn : ‖w - center d‖ = R := by rw [hwpolar]; simp [abs_of_nonneg hR]
  have hlo := support_lower d HF hν hs
  have hhi := hull_norm_le d hw
  have hre : (conj ν * (w - center d)).re ≤ ‖w - center d‖ := by
    calc
      _ ≤ ‖conj ν * (w - center d)‖ := re_le_norm _
      _ = _ := by simp [hν]
  rw [hn] at hre hhi
  have hl : d.capacity - errorRadius d ≤ R := hlo.trans hre
  have hl' : 1 / 4 ≤ R := by linarith
  refine ⟨hl, hhi, hl', by linarith [d.toBoundaryData.capacity_le_one], ?_⟩
  have hp : 0 < (conj ν * (w - center d)).re := by linarith
  have hprod : (conj ν * (w - center d)).re = R * (conj ν * unit θ).re := by
    rw [hwpolar, show conj ν * ((R : ℂ) * unit θ) = (R : ℂ) * (conj ν * unit θ) by ring]
    simp
  rw [hprod] at hp
  exact (mul_pos_iff_of_pos_left (by linarith : 0 < R)).mp hp

theorem log_radius_pair_bound {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (hc : 1 / 2 ≤ d.capacity) (he : errorRadius d ≤ 1 / 4)
    {w v ν μ : ℂ} (hw : w ∈ hull z) (hv : v ∈ hull z)
    (hν : ‖ν‖ = 1) (hμ : ‖μ‖ = 1)
    (hsw : ∀ a ∈ hull z, (conj ν * (a - center d)).re ≤ (conj ν * (w - center d)).re)
    (hsv : ∀ a ∈ hull z, (conj μ * (a - center d)).re ≤ (conj μ * (v - center d)).re)
    {R S θ x : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hwpolar : w - center d = (R : ℂ) * unit θ)
    (hvpolar : v - center d = (S : ℂ) * unit (θ + x)) :
    |Real.log S - Real.log R| ≤ 48 * Real.sqrt (errorRadius d) * |x| := by
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
  apply RadialControl.abs_log_difference_le_support (errorRadius_nonneg d)
    hr.2.2.1 hs.2.2.1 hr.2.2.2.1 hs.2.2.2.1 hsp ht hu
  · apply support_polar_inequality hr.2.2.2.2
    simpa only [hwpolar, hvpolar] using hsw v hv
  · apply support_polar_inequality hs.2.2.2.2
    simpa only [hwpolar, hvpolar, add_neg_cancel_right] using hsv w hw

end
end Erdos1045.EventualExact.ExteriorSupport
