import StructuralNote.FixedSchurNormalExpansion

/-! Lipschitz estimates for the rationalized normal correction. -/

namespace StructuralNote.FixedSchurNormalScalarDifference

noncomputable section

def rootHeight (ε s : ℝ) : ℝ := Real.sqrt (4 - (ε * s) ^ 2)

def rootCorrection (ε s : ℝ) : ℝ := s ^ 2 / (2 + rootHeight ε s)

theorem rootHeight_ge_one {ε s : ℝ} (hs : |ε * s| ≤ 1) :
    1 ≤ rootHeight ε s := by
  have hsq : (ε * s) ^ 2 ≤ 1 := by nlinarith [sq_abs (ε * s), abs_nonneg (ε * s)]
  exact (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1)
    (by linarith : 0 ≤ 4 - (ε * s) ^ 2)).2 (by nlinarith)

theorem rootHeight_sq {ε s : ℝ} (hs : |ε * s| ≤ 1) :
    rootHeight ε s ^ 2 + (ε * s) ^ 2 = 4 := by
  have hsq : (ε * s) ^ 2 ≤ 1 := by nlinarith [sq_abs (ε * s), abs_nonneg (ε * s)]
  rw [rootHeight, Real.sq_sqrt (by linarith : 0 ≤ 4 - (ε * s) ^ 2)]
  ring

theorem rootCorrection_difference {ε s t : ℝ} (hε : ε ≠ 0)
    (hs : |ε * s| ≤ 1) (ht : |ε * t| ≤ 1) :
    rootCorrection ε s - rootCorrection ε t =
      (s ^ 2 - t ^ 2) / (rootHeight ε s + rootHeight ε t) := by
  have hs1 := rootHeight_ge_one hs
  have ht1 := rootHeight_ge_one ht
  have hs2 := rootHeight_sq hs
  have ht2 := rootHeight_sq ht
  have hsd : 2 + rootHeight ε s ≠ 0 := by linarith
  have htd : 2 + rootHeight ε t ≠ 0 := by linarith
  have hsum : rootHeight ε s + rootHeight ε t ≠ 0 := by linarith
  have hr (a : ℝ) (ha : rootHeight ε a ^ 2 + (ε * a) ^ 2 = 4)
      (hd : 2 + rootHeight ε a ≠ 0) :
      ε ^ 2 * rootCorrection ε a = 2 - rootHeight ε a := by
    unfold rootCorrection
    field_simp
    nlinarith only [ha]
  have hrel : ε ^ 2 * (rootCorrection ε s - rootCorrection ε t) =
      rootHeight ε t - rootHeight ε s := by
    rw [mul_sub, hr s hs2 hsd, hr t ht2 htd]
    ring
  apply (mul_left_cancel₀ (pow_ne_zero 2 hε))
  rw [hrel]
  rw [← mul_div_assoc]
  apply (eq_div_iff hsum).2
  nlinarith only [hs2, ht2]

theorem rootCorrection_abs_le {ε s P : ℝ} (hP : 0 ≤ P) (hs : |s| ≤ P) :
    |rootCorrection ε s| ≤ P ^ 2 / 2 := by
  have hd : (2 : ℝ) ≤ 2 + rootHeight ε s := by
    exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hsq : s ^ 2 ≤ P ^ 2 := by nlinarith [sq_abs s, abs_nonneg s]
  rw [rootCorrection, abs_of_nonneg (div_nonneg (sq_nonneg s) (by linarith))]
  exact div_le_div₀ (sq_nonneg P) hsq (by norm_num) hd

theorem rootCorrection_lipschitz {ε s t P : ℝ} (hε : ε ≠ 0)
    (hP : 0 ≤ P) (hs : |s| ≤ P) (ht : |t| ≤ P)
    (hes : |ε * s| ≤ 1) (het : |ε * t| ≤ 1) :
    |rootCorrection ε s - rootCorrection ε t| ≤ P * |s - t| := by
  have hs1 := rootHeight_ge_one hes
  have ht1 := rootHeight_ge_one het
  have hd : (0 : ℝ) < rootHeight ε s + rootHeight ε t := by linarith
  rw [rootCorrection_difference hε hes het, abs_div, abs_of_pos hd]
  apply (div_le_iff₀ hd).2
  have hsum : |s + t| ≤ 2 * P := (abs_add_le _ _).trans (by linarith)
  calc
    |s ^ 2 - t ^ 2| = |s + t| * |s - t| := by rw [← abs_mul]; congr 1; ring
    _ ≤ (2 * P) * |s - t| := mul_le_mul_of_nonneg_right hsum (abs_nonneg _)
    _ ≤ P * |s - t| * (rootHeight ε s + rootHeight ε t) := by
      have hh := mul_le_mul_of_nonneg_left (show 2 ≤ rootHeight ε s + rootHeight ε t by linarith)
        (mul_nonneg hP (abs_nonneg (s - t)))
      nlinarith only [hh]

theorem signed_rootCorrection_difference {ε s t P σ τ : ℝ} (hε : ε ≠ 0)
    (hP : 0 ≤ P) (hs : |s| ≤ P) (ht : |t| ≤ P)
    (hes : |ε * s| ≤ 1) (het : |ε * t| ≤ 1)
    (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    |σ * rootCorrection ε s - τ * rootCorrection ε t| ≤
      P * |s - t| + if σ ≠ τ then P ^ 2 else 0 := by
  have hsig : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hsplit : σ * rootCorrection ε s - τ * rootCorrection ε t =
      σ * (rootCorrection ε s - rootCorrection ε t) +
        (σ - τ) * rootCorrection ε t := by ring
  rw [hsplit]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, hsig, one_mul]
  apply add_le_add (rootCorrection_lipschitz hε hP hs ht hes het)
  split_ifs with h
  · have hdiff : |σ - τ| ≤ 2 := by rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> norm_num
    have hbound := mul_le_mul hdiff (rootCorrection_abs_le (ε := ε) hP ht)
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [hbound]
  · have heq : σ = τ := not_ne_iff.mp h
    simp only [heq, sub_self, abs_zero, zero_mul, le_refl]

end
end StructuralNote.FixedSchurNormalScalarDifference
