import StructuralNote.FixedDualClassificationKernelUniformWeights
import Mathlib.Algebra.BigOperators.Module

/-! Uniform Abel bounds for actual finite odd-frequency kernel tails. -/

namespace StructuralNote.FixedDualClassificationKernelUniformAbel

open Real Finset Erdos1045.EventualExact
open FixedDualClassificationKernelUniformWeights
open scoped BigOperators
noncomputable section

theorem odd_cosine_partial_sum (N : ℕ) (t : ℝ) :
    2 * sin t * (∑ k ∈ range N, cos ((2 * k + 1 : ℕ) * t)) = sin ((2 * N : ℕ) * t) := by
  have hp (k : ℕ) : sin ((2 * (k + 1) : ℕ) * t) - sin ((2 * k : ℕ) * t) =
      2 * sin t * cos ((2 * k + 1 : ℕ) * t) := by
    rw [sin_sub_sin]
    rw [show (((2 * (k + 1) : ℕ) : ℝ) * t + ((2 * k : ℕ) : ℝ) * t) / 2 =
        ((2 * k + 1 : ℕ) : ℝ) * t by push_cast; ring,
      show (((2 * (k + 1) : ℕ) : ℝ) * t - ((2 * k : ℕ) : ℝ) * t) / 2 = t by push_cast; ring]
  have h := sum_range_sub (fun k : ℕ => sin ((2 * k : ℕ) * t)) N
  simp_rw [hp] at h
  rw [← Finset.mul_sum] at h
  simpa only [mul_zero, Nat.cast_zero, zero_mul, sin_zero, sub_zero] using h

theorem odd_cosine_partial_bound (N : ℕ) {t : ℝ} (ht : sin t ≠ 0) :
    |∑ k ∈ range N, cos ((2 * k + 1 : ℕ) * t)| ≤ 1 / (2 * |sin t|) := by
  have h := congrArg abs (odd_cosine_partial_sum N t)
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  apply (le_div_iff₀ (mul_pos (by norm_num) (abs_pos.mpr ht))).mpr
  have hs := abs_sin_le_one (((2 * N : ℕ) : ℝ) * t)
  nlinarith

theorem abel_bound {u v : ℕ} (huv : u < v) (w g : ℕ → ℝ) {B : ℝ}
    (hw : ∀ k ∈ Ico u v, 0 ≤ w k)
    (hmono : ∀ k ∈ Ico u (v - 1), w (k + 1) ≤ w k)
    (hg : ∀ k ≤ v, |∑ i ∈ range k, g i| ≤ B) :
    |∑ i ∈ Ico u v, w i * g i| ≤ 2 * B * w u := by
  have hlast : v - 1 ∈ Ico u v := mem_Ico.mpr ⟨by omega, by omega⟩
  have hfirst : u ∈ Ico u v := mem_Ico.mpr ⟨le_rfl, huv⟩
  have he := sum_Ico_by_parts w g huv
  simp only [smul_eq_mul] at he
  rw [he]
  have hvar : (∑ i ∈ Ico u (v - 1), |w (i + 1) - w i|) = w u - w (v - 1) := by
    have heq : (∑ i ∈ Ico u (v - 1), |w (i + 1) - w i|) =
        -(∑ i ∈ Ico u (v - 1), (w (i + 1) - w i)) := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro i hi
      exact abs_of_nonpos (sub_nonpos.mpr (hmono i hi))
    rw [heq, sum_Ico_sub w (show u ≤ v - 1 by omega)]
    ring
  have hsum : |∑ i ∈ Ico u (v - 1), (w (i + 1) - w i) * ∑ j ∈ range (i + 1), g j| ≤
      B * (w u - w (v - 1)) := by
    apply (abs_sum_le_sum_abs _ _).trans
    rw [← hvar, mul_sum]
    apply sum_le_sum
    intro i hi
    rw [abs_mul]
    have hi' : i + 1 ≤ v := by have := (mem_Ico.mp hi).2; omega
    nlinarith [hg (i + 1) hi', abs_nonneg (w (i + 1) - w i)]
  have hl : |w (v - 1) * ∑ i ∈ range v, g i| ≤ w (v - 1) * B := by
    rw [abs_mul, abs_of_nonneg (hw _ hlast)]
    exact mul_le_mul_of_nonneg_left (hg v le_rfl) (hw _ hlast)
  have hf : |w u * ∑ i ∈ range u, g i| ≤ w u * B := by
    rw [abs_mul, abs_of_nonneg (hw _ hfirst)]
    exact mul_le_mul_of_nonneg_left (hg u huv.le) (hw _ hfirst)
  have h1 := norm_sub_le (w (v - 1) * ∑ i ∈ range v, g i) (w u * ∑ i ∈ range u, g i)
  have h2 := norm_sub_le (w (v - 1) * ∑ i ∈ range v, g i - w u * ∑ i ∈ range u, g i)
    (∑ i ∈ Ico u (v - 1), (w (i + 1) - w i) * ∑ j ∈ range (i + 1), g j)
  simp only [Real.norm_eq_abs] at h1 h2
  nlinarith

theorem lower_half_tail {n u v : ℕ} (hn : Even n) (hu : 0 < u) (huv : u < v)
    (hv : 2 * (2 * (v - 1) + 1) ≤ n) {t : ℝ} (ht : sin t ≠ 0) :
    |∑ k ∈ Ico u v, SchurWeights.weight n (2 * k + 1) * cos ((2 * k + 1 : ℕ) * t)| ≤
      1 / (((u : ℝ) + 1) * |sin t|) := by
  have hactive (k : ℕ) (hk : k ∈ Ico u v) : SchurWeights.Active n (2 * k + 1) := by
    have hk0 := (mem_Ico.mp hk).1
    have hkv := (mem_Ico.mp hk).2
    exact ⟨⟨k, by omega⟩, by omega, by omega⟩
  have hbound := abel_bound huv (fun k => SchurWeights.weight n (2 * k + 1))
    (fun k => cos ((2 * k + 1 : ℕ) * t))
    (fun k _ => SchurWeights.weight_nonneg _ _)
    (fun k hk => weight_antitone_lower_half
      (hactive k (mem_Ico.mpr ⟨(mem_Ico.mp hk).1, by have := (mem_Ico.mp hk).2; omega⟩))
      (hactive (k + 1) (mem_Ico.mpr ⟨by have := (mem_Ico.mp hk).1; omega,
        by have := (mem_Ico.mp hk).2; omega⟩)) (by omega)
      (by have := (mem_Ico.mp hk).2; omega))
    (fun k _ => odd_cosine_partial_bound k ht)
  have hup : 2 * u + 1 ≤ n := by omega
  have hmin : min (2 * u + 1) (n - (2 * u + 1)) = 2 * u + 1 := by
    apply min_eq_left
    omega
  have hw := SchurWeights.weight_le_two_div_min hup hn
  rw [hmin] at hw
  push_cast at hw
  calc
    _ ≤ 2 * (1 / (2 * |sin t|)) * SchurWeights.weight n (2 * u + 1) := hbound
    _ ≤ 2 * (1 / (2 * |sin t|)) * (2 / ((2 * (u : ℝ) + 1) + 1)) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ = _ := by field_simp; ring

end
end StructuralNote.FixedDualClassificationKernelUniformAbel
