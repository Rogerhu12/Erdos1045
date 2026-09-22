import StructuralNote.CommonFiberNonlocalProjection

/-! Uniform scalar slack after the projection estimate. The offset two case
uses its stronger small-angle deficit; all larger offsets use Jordan's bound. -/

namespace StructuralNote.CommonFiberNonlocalSlack

open Erdos1045.EventualExact
noncomputable section

theorem cos_square_perturbation (x y : ℝ) :
    Real.cos y ^ 2 ≤ Real.cos x ^ 2 + 2 * |x| * |y - x| + |y - x| ^ 2 := by
  have he : Real.cos y ^ 2 - Real.cos x ^ 2 = -Real.sin (y + x) * Real.sin (y - x) := by
    have h := Real.cos_sub_cos (2 * y) (2 * x)
    rw [Real.cos_two_mul, Real.cos_two_mul] at h
    have h₁ : (2 * y + 2 * x) / 2 = y + x := by ring
    have h₂ : (2 * y - 2 * x) / 2 = y - x := by ring
    rw [h₁, h₂] at h
    linarith
  have hab : |y + x| ≤ 2 * |x| + |y - x| := by
    have hh := abs_add_le (y - x) (2 * x)
    rw [show y - x + 2 * x = y + x by ring, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
    linarith
  have hs₁ := (Real.abs_sin_le_abs (x := y + x)).trans hab
  have hs₂ := Real.abs_sin_le_abs (x := y - x)
  have hm := mul_le_mul hs₁ hs₂ (abs_nonneg _) (by positivity : 0 ≤ 2 * |x| + |y - x|)
  have hh := le_abs_self (-Real.sin (y + x) * Real.sin (y - x))
  rw [abs_mul, abs_neg] at hh
  nlinarith

theorem offset_two_sine {n : ℝ} (hn : 16 ≤ n) :
    25 / n ^ 2 ≤ Real.sin (2 * Real.pi / n) ^ 2 := by
  have hn0 : 0 < n := by linarith
  have hx0 : 0 ≤ 2 * Real.pi / n := by positivity
  have hx1 : 2 * Real.pi / n ≤ 1 := (div_le_one hn0).2 (by linarith [Real.pi_lt_four])
  have hsq : (2 * Real.pi / n) ^ 2 ≤ 1 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hsq hx0
  have hs := Real.sin_ge_sub_cube hx0
  have hlow : 5 * (2 * Real.pi / n) / 6 ≤ Real.sin (2 * Real.pi / n) := by nlinarith
  have hp : 5 / n ≤ 5 * (2 * Real.pi / n) / 6 := by
    apply (le_of_mul_le_mul_right ?_ hn0)
    field_simp
    linarith [Real.pi_gt_three]
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 5 / n) (hp.trans hlow) 2
  simpa only [div_pow, show (5 : ℝ) ^ 2 = 25 by norm_num] using hh

theorem projected_slack {n k : ℝ} (hn : 16 ≤ n) (hk : 2 ≤ k) (hkn : 2 * k ≤ n)
    (hdiscrete : k = 2 ∨ 3 ≤ k) :
    4 - 4 * Real.sin (Real.pi * k / n) ^ 2 + 40 * k / n ^ 2 + k ^ 2 / n ^ 2 < 4 := by
  have hn0 : 0 < n := by linarith
  rcases hdiscrete with rfl | hk3
  · have hs := offset_two_sine hn
    rw [mul_comm Real.pi 2]
    simp only [div_eq_mul_inv] at hs ⊢
    nlinarith [show (0 : ℝ) < (n ^ 2)⁻¹ by positivity]
  · have hx0 : 0 ≤ Real.pi * k / n := by positivity
    have hxπ : Real.pi * k / n ≤ Real.pi / 2 := by
      apply (div_le_iff₀ hn0).2
      nlinarith [Real.pi_pos]
    have hs := Real.mul_le_sin hx0 hxπ
    have he : (2 / Real.pi) * (Real.pi * k / n) = 2 * k / n := by field_simp
    rw [he] at hs
    have hs2 := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * k / n) hs 2
    have hg : 0 < 15 * k ^ 2 - 40 * k := by
      nlinarith [mul_nonneg (show 0 ≤ k by linarith) (show 0 ≤ k - 3 by linarith)]
    have hg' := div_pos hg (sq_pos_of_pos hn0)
    have he₂ : (2 * k / n) ^ 2 = 4 * k ^ 2 / n ^ 2 := by ring
    rw [he₂] at hs2
    have he₃ : (15 * k ^ 2 - 40 * k) / n ^ 2 = 15 * (k ^ 2 / n ^ 2) - 40 * k / n ^ 2 := by ring
    rw [he₃] at hg'
    simp only [div_eq_mul_inv] at hs2 hg' ⊢
    nlinarith

end
end StructuralNote.CommonFiberNonlocalSlack
