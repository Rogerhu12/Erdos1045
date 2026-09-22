import StructuralNote.FixedDualClassificationKernelUniformFold

/-! Direct pointwise bounds for the finite kernel, requiring no limiting-kernel identification. -/

namespace StructuralNote.FixedDualClassificationKernelUniformBounds

open Real Finset Erdos1045.EventualExact
open FixedDualClassificationKernel FixedDualClassificationKernelUniformFold
open scoped BigOperators
noncomputable section

theorem grid_kernel_bound {m r : ℕ} (hm : 2 ≤ m) {t : ℝ}
    (hgrid : (2 * m : ℕ) * t = (r : ℝ) * (2 * Real.pi)) (ht : sin t ≠ 0) :
    |finiteKernel (2 * m) t| ≤ 1 / (2 * |sin t|) := by
  have h := grid_kernel_tail (u := 1) (by omega) (by omega) hgrid ht
  have hw : SchurWeights.weight (2 * m) 1 = 0 :=
    SchurWeights.weight_eq_zero (by simp [SchurWeights.Active])
  simpa only [sum_range_one, mul_zero, zero_add, hw, zero_mul, sub_zero,
    Nat.cast_one, one_add_one_eq_two] using h

theorem grid_kernel_bound_uniform {m r : ℕ} (hm : 2 ≤ m) {t η : ℝ}
    (hgrid : (2 * m : ℕ) * t = (r : ℝ) * (2 * Real.pi))
    (hη : 0 < η) (ht : η ≤ |sin t|) :
    |finiteKernel (2 * m) t| ≤ 1 / (2 * η) := by
  exact (grid_kernel_bound hm hgrid (abs_pos.mp (hη.trans_le ht))).trans
    (one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left ht (by norm_num)))

theorem first_grid_equation {m : ℕ} (hm : 0 < m) :
    (2 * m : ℕ) * (Real.pi / m) = (1 : ℝ) * (2 * Real.pi) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp

theorem first_grid_sine_lower {m : ℕ} (hm : 2 ≤ m) :
    2 / (m : ℝ) ≤ sin (Real.pi / m) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have ht : Real.pi / m ≤ Real.pi / 2 :=
    div_le_div_of_nonneg_left pi_pos.le (by norm_num) hmR
  have h := mul_le_sin (show 0 ≤ Real.pi / m by positivity) ht
  have he : (2 / Real.pi) * (Real.pi / m) = 2 / (m : ℝ) := by field_simp
  rwa [he] at h

theorem first_grid_tail_bound {m : ℕ} (hm : 4 ≤ m) :
    |finiteKernel (2 * m) (Real.pi / m) -
      ∑ k ∈ range (m / 4), SchurWeights.weight (2 * m) (2 * k + 1) *
        cos ((2 * k + 1 : ℕ) * (Real.pi / m))| ≤ 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hs := first_grid_sine_lower (m := m) (by omega)
  have hs0 : 0 < sin (Real.pi / m) := lt_of_lt_of_le (by positivity) hs
  have h := grid_kernel_tail (m := m) (r := 1) (u := m / 4) (by omega) (by omega)
    (by simpa only [Nat.cast_one] using first_grid_equation (m := m) (by omega)) hs0.ne'
  rw [abs_of_pos hs0] at h
  apply h.trans
  apply (div_le_iff₀ (mul_pos (by positivity) hs0)).mpr
  have hu : (m : ℝ) ≤ 4 * ((m / 4 : ℕ) + 1 : ℝ) := by
    exact_mod_cast (show m ≤ 4 * (m / 4 + 1) by omega)
  have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ ((m / 4 : ℕ) : ℝ) + 1 by positivity)
  have hx : (1 : ℝ) ≤ 2 * ((((m / 4 : ℕ) : ℝ) + 1) * (2 / m)) := by
    rw [show 2 * ((((m / 4 : ℕ) : ℝ) + 1) * (2 / m)) =
      (4 * (((m / 4 : ℕ) : ℝ) + 1)) / m by ring]
    exact (le_div_iff₀ hmR).mpr (by simpa only [one_mul] using hu)
  linarith

end
end StructuralNote.FixedDualClassificationKernelUniformBounds
