import EventualExact.LensClosureNonlinear

/-! Comparing actual nonlinear closure roots at common continuous parameters. -/

namespace StructuralNote.CommonClosureDifference

open Erdos1045.EventualExact Erdos1045.EventualExact.LensClosure
open Complex Set Metric
open scoped BigOperators
noncomputable section

theorem increment_word_difference (α L s r t : ℝ) :
    increment α L s t - increment α L r t =
      unit α * (((s - r) * Lens.width L t : ℝ) : ℂ) := by
  simp only [increment, ofReal_mul, ofReal_sub]
  ring

theorem increment_word_difference_norm (α L s r t : ℝ) :
    ‖increment α L s t - increment α L r t‖ = |s - r| * |Lens.width L t| := by
  rw [increment_word_difference, norm_mul, norm_unit, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_mul]

theorem closure_word_difference {m : ℕ} (α L s r t : Fin m → ℝ) (ξ : ℂ) :
    ‖closure α L s t ξ - closure α L r t ξ‖ ≤
      ∑ j, |s j - r j| * |Lens.width (L j) (heightParameter t ξ j)| := by
  simp only [LensClosure.closure, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j, ‖increment (α j) (L j) (s j) (heightParameter t ξ j) -
        increment (α j) (L j) (r j) (heightParameter t ξ j)‖ := norm_sum_le _ _
    _ = _ := by simp only [increment_word_difference_norm]

/-- Root sensitivity to a residual at the same parameters, obtained from the actual contraction. -/
theorem root_residual_bound {m : ℕ} (hm : 2 ≤ m) (α L s t : Fin m → ℝ)
    {R : ℝ} (hs : ∀ j, |s j| ≤ 1)
    (hsmall : ∀ j, |α j - midpoint m j| + |t j| + R ≤ 1 / 4)
    {ξ η : ℂ} (hξ : ‖ξ‖ ≤ R) (hη : ‖η‖ ≤ R) (hz : closure α L s t ξ = 0) :
    ‖ξ - η‖ ≤ (4 / m : ℝ) * ‖closure α L s t η‖ := by
  have hf := (correction_fixed_iff (by omega) α L s t ξ).mpr hz
  have hl := (lipschitzOnWith_iff_norm_sub_le.mp
    (correction_lipschitz_on_ball hm α L s t hs hsmall))
    (mem_closedBall_zero_iff.mpr hξ) (mem_closedBall_zero_iff.mpr hη)
  rw [hf] at hl
  norm_num at hl
  have he : ‖correction α L s t η - η‖ =
      (2 / m : ℝ) * ‖closure α L s t η‖ := by
    simp only [correction, sub_sub_cancel_left, norm_neg, norm_mul, norm_inverseScale]
  have htri := norm_sub_le (ξ - correction α L s t η) (η - correction α L s t η)
  have he2 : (ξ - correction α L s t η) - (η - correction α L s t η) = ξ - η := by ring
  rw [he2, norm_sub_rev η, he] at htri
  calc
    ‖ξ - η‖ ≤ 2 * ((2 / m : ℝ) * ‖closure α L s t η‖) := by linarith
    _ = _ := by ring

/-- The two roots are compared directly, retaining cancellation between the two words. -/
theorem root_word_difference {m : ℕ} (hm : 2 ≤ m) (α L s r t : Fin m → ℝ)
    {R : ℝ} (hs : ∀ j, |s j| ≤ 1)
    (hsmall : ∀ j, |α j - midpoint m j| + |t j| + R ≤ 1 / 4)
    {ξ η : ℂ} (hξ : ‖ξ‖ ≤ R) (hη : ‖η‖ ≤ R)
    (hξz : closure α L s t ξ = 0) (hηz : closure α L r t η = 0) :
    ‖ξ - η‖ ≤ (4 / m : ℝ) *
      ∑ j, |s j - r j| * |Lens.width (L j) (heightParameter t η j)| := by
  have hd := closure_word_difference α L s r t η
  rw [hηz, sub_zero] at hd
  exact (root_residual_bound hm α L s t hs hsmall hξ hη hξz).trans
    (mul_le_mul_of_nonneg_left hd (by positivity))

/-- If the words differ on `J`, the source difference has exactly that support. -/
theorem sparse_word_source {m : ℕ} (L s r t : Fin m → ℝ) (η : ℂ) (J : Finset (Fin m))
    {w : ℝ} (hs : ∀ j, |s j| ≤ 1) (hr : ∀ j, |r j| ≤ 1)
    (hagree : ∀ j, j ∉ J → s j = r j)
    (hwidth : ∀ j ∈ J, |Lens.width (L j) (heightParameter t η j)| ≤ w) :
    (∑ j, |s j - r j| * |Lens.width (L j) (heightParameter t η j)|) ≤
      2 * J.card * w := by
  classical
  have he : (∑ j, |s j - r j| * |Lens.width (L j) (heightParameter t η j)|) =
      ∑ j ∈ J, |s j - r j| * |Lens.width (L j) (heightParameter t η j)| := by
    symm
    apply Finset.sum_subset (Finset.subset_univ J)
    intro j _ hj
    simp only [hagree j hj, sub_self, abs_zero, zero_mul]
  rw [he]
  calc
    _ ≤ ∑ _j ∈ J, 2 * w := by
      apply Finset.sum_le_sum
      intro j hj
      have hd : |s j - r j| ≤ 2 := (abs_sub _ _).trans (by linarith [hs j, hr j])
      exact (mul_le_mul_of_nonneg_right hd (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (hwidth j hj) (by norm_num))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

theorem root_sparse_word_difference {m : ℕ} (hm : 2 ≤ m) (α L s r t : Fin m → ℝ)
    {R w : ℝ} (hs : ∀ j, |s j| ≤ 1) (hr : ∀ j, |r j| ≤ 1)
    (hsmall : ∀ j, |α j - midpoint m j| + |t j| + R ≤ 1 / 4)
    {ξ η : ℂ} (hξ : ‖ξ‖ ≤ R) (hη : ‖η‖ ≤ R)
    (hξz : closure α L s t ξ = 0) (hηz : closure α L r t η = 0)
    (J : Finset (Fin m)) (hagree : ∀ j, j ∉ J → s j = r j)
    (hwidth : ∀ j ∈ J, |Lens.width (L j) (heightParameter t η j)| ≤ w) :
    ‖ξ - η‖ ≤ (8 * J.card / m : ℝ) * w := by
  calc
    _ ≤ (4 / m : ℝ) *
        ∑ j, |s j - r j| * |Lens.width (L j) (heightParameter t η j)| :=
      root_word_difference hm α L s r t hs hsmall hξ hη hξz hηz
    _ ≤ (4 / m : ℝ) * (2 * J.card * w) :=
      mul_le_mul_of_nonneg_left (sparse_word_source L s r t η J hs hr hagree hwidth)
        (by positivity)
    _ = _ := by ring

end
end StructuralNote.CommonClosureDifference
