import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Actual trigonometric coefficients of the local Hessian

This file proves the numerical coefficient estimates (6.10)--(6.11) from
ordinary sine inequalities. No bound on the manuscript's quadratic form is
assumed. The real parameters can be specialized to integer mode numbers.
-/

namespace Erdos1045.LocalTrigonometry

open Real
noncomputable section

def mode (n k : ℝ) : ℝ := sin (k * π / n) / sin (π / n)

def pairRatio (n k : ℝ) : ℝ :=
  (k - 2) * (n - k) / (mode n k * mode n (k - 2))

def leftWeight (n k : ℝ) : ℝ := k * (n - k) / mode n k ^ 2

def rightWeight (n k : ℝ) : ℝ := (n + 2 - k) * (k - 2) / mode n (k - 2) ^ 2

theorem base_sine_pos {n : ℝ} (hn : 1 < n) : 0 < sin (π / n) := by
  apply sin_pos_of_pos_of_lt_pi
  · exact div_pos pi_pos (by linarith)
  · apply (div_lt_iff₀ (show 0 < n by linarith)).2
    nlinarith [pi_pos]

theorem mode_pos {n k : ℝ} (hn : 1 < n) (hk : 0 < k) (hkn : k < n) :
    0 < mode n k := by
  apply div_pos _ (base_sine_pos hn)
  apply sin_pos_of_pos_of_lt_pi
  · positivity
  · apply (div_lt_iff₀ (show 0 < n by linarith)).2
    nlinarith [pi_pos]

/-- Concavity gives the decreasing-sinc inequality without a derivative lemma. -/
theorem sine_ratio_cross {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ π) :
    a * sin b ≤ b * sin a := by
  have hb0 : 0 < b := ha.trans_le hab
  have hx : 0 ≤ a / b := div_nonneg ha.le hb0.le
  have hx1 : a / b ≤ 1 := (div_le_one hb0).2 hab
  have hc := strictConcaveOn_sin_Icc.concaveOn.2
    (show (0 : ℝ) ∈ Set.Icc 0 π by constructor <;> linarith [pi_pos])
    (show b ∈ Set.Icc 0 π from ⟨hb0.le, hb⟩)
    (sub_nonneg.mpr hx1) hx (by ring : (1 - a / b) + a / b = 1)
  have hs : a / b * sin b ≤ sin a := by
    simpa [smul_eq_mul, div_mul_cancel₀ a hb0.ne'] using hc
  have hm := mul_le_mul_of_nonneg_right hs hb0.le
  field_simp at hm
  nlinarith

theorem mode_ratio_cross {n a b : ℝ} (hn : 1 < n) (ha : 0 < a)
    (hab : a ≤ b) (hbn : b < n) : a * mode n b ≤ b * mode n a := by
  have hn0 : 0 < n := by linarith
  have ht : 0 < π / n := div_pos pi_pos hn0
  have htheta : b * π / n ≤ π := by
    apply (div_le_iff₀ hn0).2
    nlinarith [pi_pos]
  have hc := sine_ratio_cross (show 0 < a * π / n by positivity)
    (show a * π / n ≤ b * π / n by gcongr) htheta
  have hscaled : (a * sin (b * π / n)) * (π / n) ≤
      (b * sin (a * π / n)) * (π / n) := by convert hc using 1 <;> ring
  have hs := (mul_le_mul_iff_of_pos_right ht).mp hscaled
  have hd := div_le_div_of_nonneg_right hs (base_sine_pos hn).le
  simpa only [mode, mul_div_assoc] using hd

/-- Jordan's sine inequality in coordinates scaled by the polygon order. -/
theorem scaled_sine_lower {n k : ℝ} (hn : 0 < n) (hk : 0 ≤ k) (hkn : 2 * k ≤ n) :
    2 * k / n ≤ sin (k * π / n) := by
  have h := mul_le_sin (show 0 ≤ k * π / n by positivity)
    (show k * π / n ≤ π / 2 by
      apply (div_le_iff₀ hn).2
      nlinarith [pi_pos])
  convert h using 1
  field_simp

theorem mode_lower_half {n k : ℝ} (hn : 1 < n) (hk : 0 ≤ k) (hkn : 2 * k ≤ n) :
    2 * k / π ≤ mode n k := by
  have hn0 : 0 < n := by linarith
  apply (le_div_iff₀ (base_sine_pos hn)).2
  calc
    2 * k / π * sin (π / n) ≤ 2 * k / π * (π / n) :=
      mul_le_mul_of_nonneg_left (sin_le (by positivity)) (by positivity)
    _ = 2 * k / n := by field_simp
    _ ≤ sin (k * π / n) := scaled_sine_lower hn0 hk hkn

theorem mode_reflect {n : ℝ} (hn : n ≠ 0) (k : ℝ) : mode n (n - k) = mode n k := by
  unfold mode
  have h : (n - k) * π / n = π - k * π / n := by field_simp
  rw [h, sin_pi_sub]

theorem paired_mode_eq {n : ℝ} (hn : n ≠ 0) (k : ℝ) :
    mode n (n + 2 - k) = mode n (k - 2) := by
  rw [show n + 2 - k = n - (k - 2) by ring, mode_reflect hn]

theorem paired_mode_monotone {n k : ℝ} (hn : 4 ≤ n) (hk : 3 ≤ k)
    (hkn : 2 * k ≤ n + 2) : mode n (k - 2) ≤ mode n k := by
  have hn0 : 0 < n := by linarith
  have hkm : 0 ≤ k - 2 := by linarith
  have hm0 : 0 ≤ (k - 2) * π / n := by positivity
  have hmhalf : (k - 2) * π / n ≤ π / 2 := by
    apply (div_le_iff₀ hn0).2
    nlinarith [pi_pos]
  apply div_le_div_of_nonneg_right _ (base_sine_pos (by linarith : 1 < n)).le
  by_cases hlow : 2 * k ≤ n
  · apply sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos])
    · apply (div_le_iff₀ hn0).2
      nlinarith [pi_pos]
    · exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) pi_pos.le) hn0.le
  · have href : sin (k * π / n) = sin ((n - k) * π / n) := by
      have heq : k * π / n = π - (n - k) * π / n := by field_simp; ring
      rw [heq, sin_pi_sub]
    rw [href]
    apply sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos])
    · apply (div_le_iff₀ hn0).2
      nlinarith [pi_pos]
    · exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) pi_pos.le) hn0.le

theorem paired_mode_le_three {n k : ℝ} (hn : 4 ≤ n) (hk : 3 ≤ k)
    (hkn : 2 * k ≤ n + 2) : mode n k ≤ 3 * mode n (k - 2) := by
  have hkpos : 0 < k - 2 := by linarith
  have hkn' : k < n := by linarith
  have hcross := mode_ratio_cross (by linarith : 1 < n) hkpos
    (by linarith : k - 2 ≤ k) hkn'
  have hs := mode_pos (by linarith : 1 < n) hkpos (by linarith : k - 2 < n)
  nlinarith

theorem pairRatio_pos {n k : ℝ} (hn : 4 ≤ n) (hk : 3 ≤ k)
    (hkn : 2 * k ≤ n + 2) : 0 < pairRatio n k := by
  unfold pairRatio
  have ha := mode_pos (by linarith : 1 < n) (by linarith : 0 < k)
    (by linarith : k < n)
  have hb := mode_pos (by linarith : 1 < n) (by linarith : 0 < k - 2)
    (by linarith : k - 2 < n)
  exact div_pos (mul_pos (by linarith) (by linarith)) (mul_pos ha hb)

/-- The first coefficient comparison in (6.11). -/
theorem leftWeight_le_three_ratio {n k : ℝ} (hn : 4 ≤ n) (hk : 3 ≤ k)
    (hkn : 2 * k ≤ n + 2) : leftWeight n k ≤ 3 * pairRatio n k := by
  have ha := mode_pos (by linarith : 1 < n) (by linarith : 0 < k)
    (by linarith : k < n)
  have hb := mode_pos (by linarith : 1 < n) (by linarith : 0 < k - 2)
    (by linarith : k - 2 < n)
  have hmono := paired_mode_monotone hn hk hkn
  have hbase : k * mode n (k - 2) ≤ 3 * (k - 2) * mode n k := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hbase
    (mul_nonneg (show 0 ≤ n - k by linarith) ha.le)
  unfold leftWeight pairRatio
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (sq_pos_of_pos ha) (mul_pos ha hb)).2
  nlinarith

/-- The second coefficient comparison in (6.11). -/
theorem rightWeight_le_nine_ratio {n k : ℝ} (hn : 4 ≤ n) (hk : 3 ≤ k)
    (hkn : 2 * k ≤ n + 2) : rightWeight n k ≤ 9 * pairRatio n k := by
  have ha := mode_pos (by linarith : 1 < n) (by linarith : 0 < k)
    (by linarith : k < n)
  have hb := mode_pos (by linarith : 1 < n) (by linarith : 0 < k - 2)
    (by linarith : k - 2 < n)
  have hthree := paired_mode_le_three hn hk hkn
  have hbase : (n + 2 - k) * mode n k ≤ 9 * (n - k) * mode n (k - 2) := by
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hbase
    (mul_nonneg (show 0 ≤ k - 2 by linarith) hb.le)
  unfold rightWeight pairRatio
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (sq_pos_of_pos hb) (mul_pos ha hb)).2
  nlinarith

/-- The two half-circle cases give the sharp enough `π²/12` coefficient. -/
theorem pairRatio_le_pi_sq {n k : ℝ} (hn : 4 ≤ n) (hk : 3 ≤ k)
    (hkn : 2 * k ≤ n + 2) : pairRatio n k ≤ π ^ 2 / 12 * (n - 1) := by
  have hn1 : 1 < n := by linarith
  have hn0 : n ≠ 0 := by linarith
  have hk0 : 0 < k := by linarith
  have hkm : 0 < k - 2 := by linarith
  have hnk : 0 < n - k := by linarith
  have ha := mode_pos hn1 hk0 (by linarith : k < n)
  have hb := mode_pos hn1 hkm (by linarith : k - 2 < n)
  have hnum : 0 ≤ (k - 2) * (n - k) := mul_nonneg hkm.le hnk.le
  have hbLower := mode_lower_half hn1 hkm.le (by linarith : 2 * (k - 2) ≤ n)
  by_cases hlow : 2 * k ≤ n
  · have haLower := mode_lower_half hn1 hk0.le hlow
    have hden : (2 * k / π) * (2 * (k - 2) / π) ≤ mode n k * mode n (k - 2) :=
      mul_le_mul haLower hbLower (by positivity) ha.le
    have hr : pairRatio n k ≤ π ^ 2 * (n - k) / (4 * k) := by
      calc
        pairRatio n k ≤ (k - 2) * (n - k) / ((2 * k / π) * (2 * (k - 2) / π)) :=
          div_le_div_of_nonneg_left hnum (by positivity) hden
        _ = π ^ 2 * (n - k) / (4 * k) := by
          field_simp
          ring
    have hrel : 3 * (n - k) ≤ k * (n - 1) := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hrel (sq_nonneg π)
    apply hr.trans
    apply (div_le_iff₀ (show 0 < 4 * k by positivity)).2
    nlinarith
  · have haLower : 2 * (n - k) / π ≤ mode n k := by
      simpa [mode_reflect hn0] using mode_lower_half hn1 hnk.le
        (show 2 * (n - k) ≤ n by linarith)
    have hden : (2 * (n - k) / π) * (2 * (k - 2) / π) ≤
        mode n k * mode n (k - 2) :=
      mul_le_mul haLower hbLower (by positivity) ha.le
    have hr : pairRatio n k ≤ π ^ 2 / 4 := by
      calc
        pairRatio n k ≤
            (k - 2) * (n - k) / ((2 * (n - k) / π) * (2 * (k - 2) / π)) :=
          div_le_div_of_nonneg_left hnum (by positivity) hden
        _ = π ^ 2 / 4 := by
          field_simp
          ring
    apply hr.trans
    nlinarith [sq_nonneg π]

/-- The rational uniform bound used in the already-verified block estimate. -/
theorem pairRatio_le_five_sixths {n k : ℝ} (hn : 4 ≤ n) (hk : 3 ≤ k)
    (hkn : 2 * k ≤ n + 2) : pairRatio n k ≤ (5 / 6 : ℝ) * (n - 1) := by
  have hp : π ^ 2 ≤ 10 := by nlinarith [pi_lt_d2, pi_pos]
  have hm := mul_le_mul_of_nonneg_right hp (show 0 ≤ n - 1 by linarith)
  have hr := pairRatio_le_pi_sq hn hk hkn
  linarith

theorem pairRatio_reflect {n : ℝ} (hn : n ≠ 0) (k : ℝ) :
    pairRatio n (n + 2 - k) = pairRatio n k := by
  unfold pairRatio
  rw [paired_mode_eq hn, show n + 2 - k - 2 = n - k by ring, mode_reflect hn]
  congr 1 <;> ring

theorem leftWeight_reflect {n : ℝ} (hn : n ≠ 0) (k : ℝ) :
    leftWeight n (n + 2 - k) = rightWeight n k := by
  unfold leftWeight rightWeight
  rw [paired_mode_eq hn]
  congr 1
  ring

/-- Uniform coefficient bounds for every paired mode, without choosing a
representative of the two-element orbit. -/
theorem all_mode_bounds {n k : ℝ} (hn : 4 ≤ n) (hk : 3 ≤ k) (hkn : k ≤ n - 1) :
    0 < pairRatio n k ∧ pairRatio n k ≤ (5 / 6 : ℝ) * (n - 1) ∧
      leftWeight n k ≤ 9 * pairRatio n k := by
  have hn0 : n ≠ 0 := by linarith
  by_cases hlow : 2 * k ≤ n + 2
  · have hp := pairRatio_pos hn hk hlow
    have ha := leftWeight_le_three_ratio hn hk hlow
    exact ⟨hp, pairRatio_le_five_sixths hn hk hlow, by linarith⟩
  · have hl : 3 ≤ n + 2 - k := by linarith
    have hlupper : 2 * (n + 2 - k) ≤ n + 2 := by linarith
    have hp := pairRatio_pos hn hl hlupper
    have hu := pairRatio_le_five_sixths hn hl hlupper
    have ha := rightWeight_le_nine_ratio hn hl hlupper
    rw [pairRatio_reflect hn0] at hp hu ha
    rw [← leftWeight_reflect hn0, show n + 2 - (n + 2 - k) = k by ring] at ha
    exact ⟨hp, hu, ha⟩

theorem second_mode_ge_one {n : ℝ} (hn : 4 ≤ n) : 1 ≤ mode n 2 := by
  have h := mode_lower_half (by linarith : 1 < n) (by norm_num : (0 : ℝ) ≤ 2)
    (by linarith : 2 * 2 ≤ n)
  have hp : (1 : ℝ) ≤ 2 * 2 / π := by
    apply (le_div_iff₀ pi_pos).2
    linarith [pi_lt_four]
  exact hp.trans h

end

end Erdos1045.LocalTrigonometry
