import StructuralNote.FixedSchurDerivativeScales

/-! Product estimates and the uniform actual radial bound needed for the
second-variation equation. -/

namespace StructuralNote.FixedSchurSecondSourceTools

open Filter Complex Erdos1045.EventualExact FiniteBox SchurSpectrum SchurLiftBounds
open CommonDomainClosure CommonClosureEnergy CommonFiberNormalAverage
open FixedSchurNormalInnerEnergy FixedSchurData FixedSchurChart FixedSchurLinear
open FixedSchurRadialAlgebra FixedSchurChartRadial FixedSchurNormalExpansion
open FixedSchurRotatedPath CommonFiberNormalProjectionScaled
open scoped BigOperators Topology

noncomputable section

theorem normalized_product_l1 {n : ℕ} (f g : Fin n → ℝ) :
    (∑ j, |f j * g j|) / (n : ℝ) ≤
      Real.sqrt (meanSquare f) * Real.sqrt (meanSquare g) := by
  simpa only [abs_mul, average, meanSquare] using mixed_average f g

theorem product_meanSquare_le {n : ℕ} (f g : Fin n → ℝ) :
    meanSquare (fun j => f j * g j) ≤ ‖f‖ ^ 2 * meanSquare g := by
  apply meanSquare_domination _ g (norm_nonneg f)
  intro j
  rw [abs_mul]
  have hj : |f j| ≤ ‖f‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm f j
  exact mul_le_mul_of_nonneg_right hj (abs_nonneg _)

theorem square_meanSquare_le {n : ℕ} (f : Fin n → ℝ) :
    meanSquare (fun j => f j ^ 2) ≤ ‖f‖ ^ 2 * meanSquare f := by
  simpa only [pow_two] using product_meanSquare_le f f

def radialCoefficient {m : ℕ} (hm : 0 < m) (s : SignPattern hm)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) (j : Fin (2 * m)) : ℝ :=
  r (coordinate hm s θ v j) (rotatedP (by omega) v (coordinate hm s θ v) j)
    (angleAverage (by omega) θ j)

theorem eventual_radialCoefficient_bound :
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      ∀ j, |radialCoefficient (by omega) s θ v j| ≤ (5 / 2 : ℝ) := by
  filter_upwards [eventual_coordinate_radial] with m hrad
  intro hm s θ v hdom j
  have hd := hrad hm s θ v hdom j
  rw [center_difference hm _ _ hdom.2.2.1.2.2, radial_edgeIncrement] at hd
  change |epsilon (2 * m) * radialCoefficient (by omega) s θ v j| ≤
    10 / (2 * m : ℝ) ^ 2 at hd
  have hε := epsilon_pos (show 2 ≤ 2 * m by omega)
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  rw [abs_mul, abs_of_pos hε] at hd
  have hscale := (scale_bounds (show 2 ≤ 2 * m by omega)).2
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hscale
  calc
    _ = (epsilon (2 * m))⁻¹ * (epsilon (2 * m) * |radialCoefficient (by omega) s θ v j|) := by
      field_simp
    _ ≤ (epsilon (2 * m))⁻¹ * (10 / (2 * m : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hε.le)
    _ = scale (2 * m) * (10 / (2 * m : ℝ) ^ 2) := by rw [epsilon_inv (show 2 ≤ 2 * m by omega)]
    _ ≤ ((2 * m : ℝ) ^ 2 / 4) * (10 / (2 * m : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hscale (by positivity)
    _ = 5 / 2 := by field_simp; ring

end
end StructuralNote.FixedSchurSecondSourceTools
