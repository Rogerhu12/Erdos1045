import Mathlib

/-! Pure real inequalities used by the fixed-Schur source estimate. -/

namespace StructuralNote.FixedSchurSourceArithmetic

theorem source_error_bound {N L H : ℝ} (hN : 0 < N) (_hL : 1 ≤ L) (_hH : 0 ≤ H) :
    (N ^ 2 / 4) *
        (40 * L / N ^ 3 + 25 * L ^ 2 / N ^ 4 +
          16 * L ^ 2 * H ^ 2 / N ^ 4 +
          (8 * L * (H + 11) / N ^ 2) ^ 2 / 2) ≤
      10 * L / N + 2000 * L ^ 2 * (1 + H ^ 2) / N ^ 2 := by
  have hN0 : N ≠ 0 := ne_of_gt hN
  have hcoeff :
      25 / 4 + 4 * H ^ 2 + 8 * (H + 11) ^ 2 ≤ 2000 * (1 + H ^ 2) := by
    nlinarith [sq_nonneg (H - 11)]
  have hfactor : 0 ≤ L ^ 2 / N ^ 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hcoeff hfactor
  have hident :
      (N ^ 2 / 4) *
          (40 * L / N ^ 3 + 25 * L ^ 2 / N ^ 4 +
            16 * L ^ 2 * H ^ 2 / N ^ 4 +
            (8 * L * (H + 11) / N ^ 2) ^ 2 / 2) =
        10 * L / N + (L ^ 2 / N ^ 2) *
          (25 / 4 + 4 * H ^ 2 + 8 * (H + 11) ^ 2) := by
    field_simp [hN0]
    ring
  calc
    (N ^ 2 / 4) *
          (40 * L / N ^ 3 + 25 * L ^ 2 / N ^ 4 +
            16 * L ^ 2 * H ^ 2 / N ^ 4 +
            (8 * L * (H + 11) / N ^ 2) ^ 2 / 2) =
        10 * L / N + (L ^ 2 / N ^ 2) *
          (25 / 4 + 4 * H ^ 2 + 8 * (H + 11) ^ 2) := hident
    _ ≤ 10 * L / N + (L ^ 2 / N ^ 2) * (2000 * (1 + H ^ 2)) :=
      add_le_add le_rfl hscaled
    _ = 10 * L / N + 2000 * L ^ 2 * (1 + H ^ 2) / N ^ 2 := by ring

theorem source_error_bound_under_unit_ratio {N L H : ℝ}
    (hN : 0 < N) (hL : 1 ≤ L) (_hH : 0 ≤ H)
    (hsmall : L * (1 + H ^ 2) / N ≤ 1) :
    10 * L / N + 2000 * L ^ 2 * (1 + H ^ 2) / N ^ 2 ≤ 2048 * L / N := by
  have hN0 : N ≠ 0 := ne_of_gt hN
  have hLN : 0 ≤ L / N := by positivity
  have hratio :
      L ^ 2 * (1 + H ^ 2) / N ^ 2 =
        (L / N) * (L * (1 + H ^ 2) / N) := by
    field_simp [hN0]
  have hprod :
      L ^ 2 * (1 + H ^ 2) / N ^ 2 ≤ L / N := by
    rw [hratio]
    simpa using (mul_le_mul_of_nonneg_left hsmall hLN)
  have hterm :
      2000 * (L ^ 2 * (1 + H ^ 2) / N ^ 2) ≤ 2000 * (L / N) := by
    exact mul_le_mul_of_nonneg_left hprod (by norm_num)
  calc
    10 * L / N + 2000 * L ^ 2 * (1 + H ^ 2) / N ^ 2 =
        10 * L / N + 2000 * (L ^ 2 * (1 + H ^ 2) / N ^ 2) := by ring
    _ ≤ 10 * L / N + 2000 * (L / N) := add_le_add le_rfl hterm
    _ = 2010 * (L / N) := by ring
    _ ≤ 2048 * (L / N) := by nlinarith
    _ = 2048 * L / N := by ring

theorem abs_source_term_le {N L H ε σ Y p : ℝ}
    (_hN : 0 < N) (hL : 0 ≤ L) (_hH : 0 ≤ H) (hε : 0 < ε)
    (hε_upper : ε ≤ 8 / N ^ 2) (hσ : σ = 1 ∨ σ = -1)
    (hY : |Y| ≤ 8 * L * H / N ^ 2) (hp : |p| ≤ 11 * L) :
    |Y + σ * ε * p| ≤ 8 * L * (H + 11) / N ^ 2 := by
  have hσabs : |σ| = 1 := by
    rcases hσ with rfl | rfl <;> norm_num
  have hε0 : 0 ≤ ε := le_of_lt hε
  have h11L : 0 ≤ 11 * L := by positivity
  have hep : ε * |p| ≤ (8 / N ^ 2) * (11 * L) := by
    exact (mul_le_mul_of_nonneg_left hp hε0).trans
      (mul_le_mul_of_nonneg_right hε_upper h11L)
  calc
    |Y + σ * ε * p| ≤ |Y| + |σ * ε * p| := abs_add_le _ _
    _ = |Y| + ε * |p| := by
      rw [abs_mul, abs_mul, hσabs, one_mul, abs_of_pos hε]
    _ ≤ 8 * L * H / N ^ 2 + (8 / N ^ 2) * (11 * L) := by
      exact add_le_add hY hep
    _ = 8 * L * (H + 11) / N ^ 2 := by ring

end StructuralNote.FixedSchurSourceArithmetic
