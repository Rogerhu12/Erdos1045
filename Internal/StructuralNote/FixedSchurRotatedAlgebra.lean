import StructuralNote.FixedSchurData

/-! Exact rotation and rationalization of the selected crossing equation. -/

namespace StructuralNote.FixedSchurRotatedAlgebra

noncomputable section

def radial (b q p : ℝ) : ℝ := q * Real.cos b + p * Real.sin b
def tangential (b q p : ℝ) : ℝ := p * Real.cos b - q * Real.sin b

theorem rotated_square (L ε σ b q p : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    (L * Real.cos b + σ * ε * q) ^ 2 + (L * Real.sin b + σ * ε * p) ^ 2 =
      (L + σ * ε * radial b q p) ^ 2 + (ε * tangential b q p) ^ 2 := by
  unfold radial tangential
  rcases hσ with rfl | rfl <;>
    linear_combination (L ^ 2 - ε ^ 2 * (q ^ 2 + p ^ 2)) * Real.sin_sq_add_cos_sq b

theorem rotated_root {L ε σ b q p : ℝ} (hε : 0 < ε) (hσ : σ = 1 ∨ σ = -1)
    (hsq : (L * Real.cos b + σ * ε * q) ^ 2 +
      (L * Real.sin b + σ * ε * p) ^ 2 = 4)
    (hpos : 0 < L + σ * ε * radial b q p) :
    radial b q p = σ / ε * (Real.sqrt (4 - (ε * tangential b q p) ^ 2) - L) := by
  rw [rotated_square L ε σ b q p hσ] at hsq
  have he : 4 - (ε * tangential b q p) ^ 2 = (L + σ * ε * radial b q p) ^ 2 := by
    linarith only [hsq]
  rw [he, Real.sqrt_sq_eq_abs, abs_of_pos hpos]
  rcases hσ with rfl | rfl <;> field_simp <;> ring

theorem rationalized_height {ε s H : ℝ} (hH : H ^ 2 + (ε * s) ^ 2 = 4)
    (hden : 2 + H ≠ 0) : H - 2 = -(ε ^ 2 * s ^ 2) / (2 + H) := by
  apply (eq_div_iff hden).2
  nlinarith only [hH]

theorem normal_expansion {L ε σ b q p H : ℝ} (hε : ε ≠ 0)
    (hc : Real.cos b ≠ 0) (hH : H ^ 2 + (ε * tangential b q p) ^ 2 = 4)
    (hden : 2 + H ≠ 0) (hr : radial b q p = σ / ε * (H - L)) :
    q = σ / ε * ((2 - L) / Real.cos b) - p * Real.tan b -
      σ * ε * (tangential b q p) ^ 2 / (Real.cos b * (2 + H)) := by
  have hh := rationalized_height hH hden
  have hq : q * Real.cos b = σ / ε * (H - L) - p * Real.sin b := by
    unfold radial at hr
    linarith only [hr]
  apply (mul_right_cancel₀ hc)
  rw [Real.tan_eq_sin_div_cos]
  have hh' : (H - 2) * (2 + H) = -(ε ^ 2 * (tangential b q p) ^ 2) :=
    (eq_div_iff hden).mp hh
  field_simp at hq
  field_simp
  linear_combination (2 + H) * hq + σ * hh'

end
end StructuralNote.FixedSchurRotatedAlgebra
