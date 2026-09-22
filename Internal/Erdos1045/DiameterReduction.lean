import Erdos1045.HullGeometry

open scoped BigOperators Topology
open Filter

namespace Erdos1045.HullGeometry

open Configuration
noncomputable section

def perimeterMaximum (n : ℕ) : ℝ :=
  (2 * Real.pi / circlePerimeter n) ^ exponent n * (n : ℝ) ^ n

def diameterMaximumRatio (n : ℕ) : ℝ :=
  (diameterPerimeterBound n / circlePerimeter n) ^ exponent n * (n : ℝ) ^ n

def diameterMaximum (n : ℕ) : ℝ :=
  (n : ℝ) ^ n / (2 * Real.cos (Real.pi / (2 * n))) ^ exponent n

def unitRegular (n : ℕ) : Points n :=
  fun i => ((1 / (2 * Real.cos (Real.pi / (2 * n))) : ℝ) : ℂ) * regular n i

theorem diameterPerimeterBound_pos {n : ℕ} (hn : 3 ≤ n) : 0 < diameterPerimeterBound n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) < 2 * n := by exact_mod_cast (show 1 < 2 * n by omega)
  have hsin : 0 < Real.sin (Real.pi / (2 * n)) := by
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
    nlinarith [Real.pi_pos]
  unfold diameterPerimeterBound
  positivity

theorem regular_half_cos_pos {n : ℕ} (hn : 3 ≤ n) :
    0 < Real.cos (Real.pi / (2 * n)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have h : 0 < Real.pi / (2 * n) := by positivity
    linarith [Real.pi_pos]
  · apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
    nlinarith [Real.pi_pos]

theorem perimeter_ratio_regular_radius {n : ℕ} (hn : 3 ≤ n) :
    diameterPerimeterBound n / circlePerimeter n = 1 / (2 * Real.cos (Real.pi / (2 * n))) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hsin : Real.sin (Real.pi / (2 * n)) ≠ 0 := by
    have hp := diameterPerimeterBound_pos hn
    unfold diameterPerimeterBound at hp
    intro hz
    rw [hz, mul_zero] at hp
    linarith
  have hcos := (regular_half_cos_pos hn).ne'
  have hdouble : Real.pi / (n : ℝ) = 2 * (Real.pi / (2 * n)) := by field_simp
  unfold diameterPerimeterBound circlePerimeter
  rw [hdouble, Real.sin_two_mul]
  field_simp

theorem diameterMaximumRatio_eq {n : ℕ} (hn : 3 ≤ n) :
    diameterMaximumRatio n = diameterMaximum n := by
  unfold diameterMaximumRatio diameterMaximum
  rw [perimeter_ratio_regular_radius hn, div_pow, one_pow]
  ring

/-- This theorem's regularity premise is the new mathematical conclusion to be
proved by the manuscript's analytic argument. It is not a classical input. -/
theorem perimeter_bound_of_regular_extremals (H : ClassicalHullGeometry) {n : ℕ} (hn : 3 ≤ n)
    (hregular : ∀ z : Points n, PerimeterExtremal n z → Configuration.IsRegular z)
    (z : Points n) (hz : hullPerimeter z ≤ 2 * Real.pi) :
    discriminant z ≤ perimeterMaximum n := by
  obtain ⟨u, hu⟩ := exists_perimeterExtremal H (show 0 < n by omega)
  have hreg := hregular u hu
  have hratio : hullPerimeter u / circlePerimeter n ≤ 2 * Real.pi / circlePerimeter n :=
    div_le_div_of_nonneg_right hu.1 (circlePerimeter_pos hn).le
  have hnonneg : 0 ≤ hullPerimeter u / circlePerimeter n :=
    div_nonneg (H.nonneg n u) (circlePerimeter_pos hn).le
  calc
    discriminant z ≤ discriminant u := hu.2 z hz
    _ = (hullPerimeter u / circlePerimeter n) ^ exponent n * (n : ℝ) ^ n :=
      regular_discriminant_from_perimeter H hn hreg
    _ ≤ perimeterMaximum n := by
      unfold perimeterMaximum
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hnonneg hratio _)
        (by positivity)

theorem perimeterExtremal_of_attains (H : ClassicalHullGeometry) {n : ℕ} (hn : 3 ≤ n)
    (hregular : ∀ z : Points n, PerimeterExtremal n z → Configuration.IsRegular z)
    (z : Points n) (hP : hullPerimeter z ≤ 2 * Real.pi)
    (hD : discriminant z = perimeterMaximum n) : PerimeterExtremal n z := by
  refine ⟨hP, ?_⟩
  intro w hw
  rw [hD]
  exact perimeter_bound_of_regular_extremals H hn hregular w hw

theorem diameter_bound_of_regular_extremals (H : ClassicalHullGeometry) {n : ℕ} (hn : 3 ≤ n)
    (hregular : ∀ z : Points n, PerimeterExtremal n z → Configuration.IsRegular z)
    (z : Points n) (hz : DiameterAtMost 1 z) : discriminant z ≤ diameterMaximum n := by
  let r : ℝ := 2 * Real.pi / diameterPerimeterBound n
  have hr : 0 < r := by dsimp [r]; exact div_pos (by positivity) (diameterPerimeterBound_pos hn)
  let v : Points n := fun i => (r : ℂ) * z i
  have hvP : hullPerimeter v ≤ 2 * Real.pi := by
    have hP : hullPerimeter v = r * hullPerimeter z := by
      simpa [v, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using H.affine n z 0 (r : ℂ)
    rw [hP]
    have h := mul_le_mul_of_nonneg_left (H.reinhardt n hn z hz) hr.le
    have heq : r * diameterPerimeterBound n = 2 * Real.pi := by dsimp [r]; field_simp [(diameterPerimeterBound_pos hn).ne']
    rwa [heq] at h
  have hvD : discriminant v = r ^ exponent n * discriminant z := by
    simpa [v, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using discriminant_affine z 0 (r : ℂ)
  have htarget : r ^ exponent n * diameterMaximumRatio n = perimeterMaximum n := by
    unfold diameterMaximumRatio perimeterMaximum
    rw [← mul_assoc, ← mul_pow]
    have heq : r * (diameterPerimeterBound n / circlePerimeter n) = 2 * Real.pi / circlePerimeter n := by
      dsimp [r]
      field_simp [(diameterPerimeterBound_pos hn).ne']
    rw [heq]
  have hbound := perimeter_bound_of_regular_extremals H hn hregular v hvP
  rw [hvD, ← htarget] at hbound
  have h := le_of_mul_le_mul_left hbound (pow_pos hr (exponent n))
  rwa [diameterMaximumRatio_eq hn] at h

theorem diameter_equality_isRegular (H : ClassicalHullGeometry) {n : ℕ} (hn : 3 ≤ n)
    (hregular : ∀ z : Points n, PerimeterExtremal n z → Configuration.IsRegular z)
    (z : Points n) (hz : DiameterAtMost 1 z) (hD : discriminant z = diameterMaximum n) :
    Configuration.IsRegular z := by
  let r : ℝ := 2 * Real.pi / diameterPerimeterBound n
  have hr : 0 < r := by dsimp [r]; exact div_pos (by positivity) (diameterPerimeterBound_pos hn)
  let v : Points n := fun i => (r : ℂ) * z i
  have hvP : hullPerimeter v ≤ 2 * Real.pi := by
    have hP : hullPerimeter v = r * hullPerimeter z := by
      simpa [v, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using H.affine n z 0 (r : ℂ)
    rw [hP]
    have h := mul_le_mul_of_nonneg_left (H.reinhardt n hn z hz) hr.le
    have heq : r * diameterPerimeterBound n = 2 * Real.pi := by dsimp [r]; field_simp [(diameterPerimeterBound_pos hn).ne']
    rwa [heq] at h
  have hvD : discriminant v = perimeterMaximum n := by
    have hscale := discriminant_affine z 0 (r : ℂ)
    simp only [zero_add, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hD] at hscale
    rw [← diameterMaximumRatio_eq hn] at hscale
    change discriminant v = _ at hscale
    rw [hscale]
    unfold diameterMaximumRatio perimeterMaximum
    rw [← mul_assoc, ← mul_pow]
    have heq : r * (diameterPerimeterBound n / circlePerimeter n) = 2 * Real.pi / circlePerimeter n := by
      dsimp [r]
      field_simp [(diameterPerimeterBound_pos hn).ne']
    rw [heq]
  have hvreg := hregular v (perimeterExtremal_of_attains H hn hregular v hvP hvD)
  apply isRegular_of_affine z 0 (r : ℂ) (by exact_mod_cast hr.ne')
  simpa only [zero_add] using hvreg

/-- For odd cardinalities the bound is achieved by the diameter-one regular polygon. -/
theorem unitRegular_diameter (H : ClassicalHullGeometry) {n : ℕ}
    (hn : 3 ≤ n) (hodd : Odd n) : DiameterAtMost 1 (unitRegular n) := by
  have hc : 0 < 2 * Real.cos (Real.pi / (2 * n)) := by
    exact mul_pos (by norm_num) (regular_half_cos_pos hn)
  have hr : 0 < 1 / (2 * Real.cos (Real.pi / (2 * n))) := by positivity
  have h := diameter_affine (H.regular_diameter n hn hodd) 0
    (((1 / (2 * Real.cos (Real.pi / (2 * n))) : ℝ) : ℂ))
  simp only [zero_add, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at h
  have heq : (1 / (2 * Real.cos (Real.pi / (2 * n)))) *
      (2 * Real.cos (Real.pi / (2 * n))) = 1 := by field_simp [(regular_half_cos_pos hn).ne']
  rw [heq] at h
  exact h

theorem unitRegular_discriminant (H : ClassicalHullGeometry) {n : ℕ}
    (hn : 3 ≤ n) : discriminant (unitRegular n) = diameterMaximum n := by
  have hr : 0 < 1 / (2 * Real.cos (Real.pi / (2 * n))) := by
    have := regular_half_cos_pos hn
    positivity
  have h := discriminant_affine (regular n) 0
    (((1 / (2 * Real.cos (Real.pi / (2 * n))) : ℝ) : ℂ))
  simp only [zero_add, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    H.regular_discriminant n hn] at h
  change discriminant (unitRegular n) = _ at h
  rw [h]
  simp only [diameterMaximum, div_pow, one_pow]
  ring

theorem diameter_equality_iff (H : ClassicalHullGeometry) {n : ℕ} (hn : 3 ≤ n)
    (hregular : ∀ z : Points n, PerimeterExtremal n z → Configuration.IsRegular z)
    (z : Points n) (hz : DiameterAtMost 1 z) :
    discriminant z = diameterMaximum n ↔
      Configuration.IsRegular z ∧ hullPerimeter z = diameterPerimeterBound n := by
  constructor
  · intro hD
    have hreg := diameter_equality_isRegular H hn hregular z hz hD
    refine ⟨hreg, ?_⟩
    have hform := regular_discriminant_from_perimeter H hn hreg
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have he : exponent n ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
    have hprod : (hullPerimeter z / circlePerimeter n) ^ exponent n * (n : ℝ) ^ n =
        (diameterPerimeterBound n / circlePerimeter n) ^ exponent n * (n : ℝ) ^ n := by
      rw [← hform, hD, ← diameterMaximumRatio_eq hn]
      rfl
    have hpow := mul_right_cancel₀ (pow_ne_zero n hn0) hprod
    have hratio := (pow_left_inj₀
      (div_nonneg (H.nonneg n z) (circlePerimeter_pos hn).le)
      (div_nonneg (diameterPerimeterBound_pos hn).le (circlePerimeter_pos hn).le) he).mp hpow
    exact (div_left_inj' (circlePerimeter_pos hn).ne').mp hratio
  · rintro ⟨hreg, hP⟩
    rw [regular_discriminant_from_perimeter H hn hreg, hP, ← diameterMaximumRatio_eq hn]
    rfl

/-- The exact finite diameter maximization problem, conditional only on the
new perimeter-extremal regularity theorem and the declared classical geometry. -/
theorem diameter_maximum (H : ClassicalHullGeometry) {n : ℕ}
    (hn : 3 ≤ n) (hodd : Odd n)
    (hregular : ∀ z : Points n, PerimeterExtremal n z → Configuration.IsRegular z) :
    (∀ z : Points n, DiameterAtMost 1 z → discriminant z ≤ diameterMaximum n) ∧
    (∃ z : Points n, DiameterAtMost 1 z ∧ discriminant z = diameterMaximum n) ∧
    (∀ z : Points n, DiameterAtMost 1 z → discriminant z = diameterMaximum n →
      Configuration.IsRegular z) := by
  exact ⟨fun z hz => diameter_bound_of_regular_extremals H hn hregular z hz,
    ⟨unitRegular n, unitRegular_diameter H hn hodd, unitRegular_discriminant H hn⟩,
    fun z hz hD => diameter_equality_isRegular H hn hregular z hz hD⟩

end

end Erdos1045.HullGeometry

