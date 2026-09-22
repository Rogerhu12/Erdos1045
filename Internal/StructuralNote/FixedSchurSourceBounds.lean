import StructuralNote.FixedSchurScalarRoot
import StructuralNote.FixedSchurSourceArithmetic

/-! The scalar source estimate keeps the sine factor in the chord error.
This is the estimate of the displacement at the finite-box vertex. -/

namespace StructuralNote.FixedSchurSourceBounds

open FixedSchurScalarRoot FixedSchurSourceArithmetic

noncomputable section

theorem scalar_source_bound {N L H ε σ X X₀ Y p A : ℝ}
    (hN : 0 < N) (hL : 1 ≤ L) (hH : 0 ≤ H) (hε : 0 < ε)
    (hε_upper : ε ≤ 8 / N ^ 2) (hscale : ε⁻¹ ≤ N ^ 2 / 4)
    (hσ : σ = 1 ∨ σ = -1) (hA : ε * A = 2 - X₀)
    (hX : |X - X₀| ≤ 40 * L / N ^ 3 + 25 * L ^ 2 / N ^ 4 + 16 * L ^ 2 * H ^ 2 / N ^ 4)
    (hY : |Y| ≤ 8 * L * H / N ^ 2) (hp : |p| ≤ 11 * L)
    (hz : |Y + σ * ε * p| ≤ 1) :
    |rootValue σ ε X Y p - A * σ| ≤
      10 * L / N + 2000 * L ^ 2 * (1 + H ^ 2) / N ^ 2 := by
  have hZ := abs_source_term_le hN (by linarith : 0 ≤ L) hH hε hε_upper hσ hY hp
  have hZsq : (Y + σ * ε * p) ^ 2 ≤ (8 * L * (H + 11) / N ^ 2) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hZ
  have hroot := rootValue_source_bound (X := X) hσ hε hA hz
  calc
    |rootValue σ ε X Y p - A * σ| ≤ (|X - X₀| + (Y + σ * ε * p) ^ 2 / 2) / ε := hroot
    _ = ε⁻¹ * (|X - X₀| + (Y + σ * ε * p) ^ 2 / 2) := by ring
    _ ≤ (N ^ 2 / 4) * (|X - X₀| + (Y + σ * ε * p) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right hscale (by positivity)
    _ ≤ (N ^ 2 / 4) *
        (40 * L / N ^ 3 + 25 * L ^ 2 / N ^ 4 + 16 * L ^ 2 * H ^ 2 / N ^ 4 +
          (8 * L * (H + 11) / N ^ 2) ^ 2 / 2) := by gcongr
    _ ≤ 10 * L / N + 2000 * L ^ 2 * (1 + H ^ 2) / N ^ 2 := source_error_bound hN hL hH

end
end StructuralNote.FixedSchurSourceBounds
