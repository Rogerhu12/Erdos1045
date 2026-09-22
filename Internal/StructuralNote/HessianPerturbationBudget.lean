import StructuralNote.HessianDenominator
import StructuralNote.HessianVelocityEnergy

/-! Quantitative stability of the velocity Hessian at a nearby configuration.
All errors are measured by the regular chord energy. -/

namespace StructuralNote.HessianPerturbationBudget

open Erdos1045 Erdos1045.EventualExact Complex SchurSpectrum
open LogDiscriminantHessian HessianReferencePotential HessianDenominator
open scoped BigOperators
noncomputable section

theorem sqrt_product_bound {x y B ε : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hB : 0 ≤ B) (hε : 0 ≤ ε) (hxb : x ≤ 12 * B) (hyb : y ≤ ε ^ 2 * B) :
    Real.sqrt x * Real.sqrt y ≤ 4 * ε * B := by
  have hp := mul_le_mul hxb hyb hy (by positivity : 0 ≤ 12 * B)
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt hx, Real.sq_sqrt hy]
  nlinarith only [hp, sq_nonneg (ε * B)]

theorem quadratic_perturbation {n : ℕ} (hn : 4 ≤ n) (z u e : Fin n → ℂ)
    {δ ε B : ℝ} (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 2) (hε : 0 ≤ ε) (hB : 0 ≤ B)
    (hrelative : ∀ i j, i ≠ j → ‖(z i - z j) / (root n i - root n j) - 1‖ ≤ δ)
    (hu : pairEnergy (by omega) u ≤ 12 * B)
    (he : pairEnergy (by omega) e ≤ ε ^ 2 * B) :
    |quadratic z (u + e) - quadratic (root n) u| ≤
      (20 * δ * (24 + 2 * ε ^ 2) + 16 * ε + 2 * ε ^ 2) * B := by
  have he0 := pairEnergy_nonneg (by omega : 0 < n) e
  have hu0 := pairEnergy_nonneg (by omega : 0 < n) u
  have hs := sqrt_product_bound hu0 he0 hB hε hu he
  have hv := QuadraticStability.pairEnergy_add_le (by omega : 0 < n) u e
  have hvb : pairEnergy (by omega) (u + e) ≤ (24 + 2 * ε ^ 2) * B := by
    linarith only [hv, hu, he]
  have hd := regular_denominator_bound (by omega : 0 < n) z (u + e)
    (HessianAngularReference.root_injective hn) hδsmall hrelative
  have hdb := mul_le_mul_of_nonneg_left hvb (by positivity : 0 ≤ 20 * δ)
  have hvel := quadratic_velocity_error (by omega : 0 < n) u e
  have hsum := abs_add_le (quadratic z (u + e) - quadratic (root n) (u + e))
    (quadratic (root n) (u + e) - quadratic (root n) u)
  rw [sub_add_sub_cancel] at hsum
  nlinarith only [hd, hdb, hvel, hsum, hs, he]

end
end StructuralNote.HessianPerturbationBudget
