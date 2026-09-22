import StructuralNote.CommonFiberHeightVelocity
import StructuralNote.CommonFiberDifferentialEstimate

/-! Uniform square-sum control of the actual first height derivative on the
common domain. This includes the derivative of the nonlinear closure root. -/

namespace StructuralNote.CommonFiberHeightEstimate

open Erdos1045.EventualExact Complex LensClosure LensIncrementDerivatives
open CommonClosureEnergy CommonTangentialParameters CommonDomainClosure CommonDomainRadius
open CommonFiberFirstDerivative CommonFiberDerivativeEnergy CommonFiberSmallCoefficients
open CommonFiberDifferentialEstimate CommonFiberHeightVelocity SchurSpectrum
open scoped BigOperators
noncomputable section

theorem height_angular_coefficient {n : ℝ} (hn : 1 ≤ n) :
    384 * (2 / n) ^ 2 * n + 768 * Real.pi ^ 2 * (5 / n) ^ 2 ≤ 400000 / n := by
  have hn0 : 0 < n := by linarith
  have hp : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hn0)).mp
  have he : n ^ 2 * (384 * (2 / n) ^ 2 * n + 768 * Real.pi ^ 2 * (5 / n) ^ 2) =
      1536 * n + 19200 * Real.pi ^ 2 := by field_simp; ring
  have hf : n ^ 2 * (400000 / n) = 400000 * n := by field_simp
  rw [he, hf]
  nlinarith

theorem domain_height_velocity_energy {m : ℕ} (hm : 128 ≤ m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ) (η : Fin (2 * m) → ℝ)
    (h : Fin (2 * m) → ℂ) (ξ' : ℂ)
    (hdom : InDomain (by omega) θ v) (hξ : ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2)
    (hmean : ∑ j, (η j : ℂ) = 0) (hh : ParameterSpace (by omega) h)
    (hz : (∑ j, velocity (by omega) θ v σ ξ η h ξ' j) = 0) (hσ : ∀ j, |σ j| ≤ 1)
    (hscale : energyRadius (2 * m) ≤ 1 / (2 * m : ℝ))
    (horder : 10 * (logOrder (2 * m) : ℝ) + 1024 ≤ 2 * m) :
    (2 * m : ℝ) ^ 2 * (∑ j, heightParameter (coordinates (by omega) h) ξ' j ^ 2) ≤
      400000 / (2 * m : ℝ) * pairEnergy (by omega) (fun j => (η j : ℂ)) +
      400000 * pairEnergy (by omega) h := by
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hn25 : (25 : ℝ) ≤ 2 * m := by exact_mod_cast (show 25 ≤ 2 * m by omega)
  have hsmall := domain_jacobian_small hm θ v σ hdom hξ hscale
  have hB : bodyNorm (by omega) θ v σ ξ ≤ 2 / (2 * m : ℝ) := by
    calc
      _ ≤ (10 * (logOrder (2 * m) : ℝ) + 1049) / (2 * m : ℝ) ^ 2 :=
        domain_bodyNorm_bound (by omega) θ v σ hdom hξ hσ horder
      _ ≤ (2 * (2 * m)) / (2 * m : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
      _ = _ := by field_simp
  have hS := domain_sineNorm_bound (by omega) θ v hdom horder
  have hbase := height_velocity_energy (by omega) θ v σ ξ η h ξ' hmean hh hz hσ hsmall
    (B := 2 / (2 * m : ℝ)) (S := 5 / (2 * m : ℝ)) (T := 1 / 4)
    (fun j => (norm_le_pi_norm (fun k : Fin m => body
      (2 * Real.cos (halfAngle (by omega) θ k)) (σ k)
      (heightParameter (coordinates (by omega) v) ξ k)) j).trans hB)
    (fun j => ((Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm
      (fun k : Fin m => Real.sin (halfAngle (by omega) θ k)) j)).trans hS) hsmall
  have hA := height_angular_coefficient (n := (2 * m : ℝ)) (by linarith)
  have hT : 16 * Real.pi ^ 2 + 768 * Real.pi ^ 2 * (1 / 4 : ℝ) ^ 2 ≤ 400000 := by
    nlinarith [Real.pi_pos, Real.pi_lt_four]
  exact hbase.trans (add_le_add
    (mul_le_mul_of_nonneg_right hA (pairEnergy_nonneg _ _))
    (mul_le_mul_of_nonneg_right hT (pairEnergy_nonneg _ _)))

end
end StructuralNote.CommonFiberHeightEstimate
