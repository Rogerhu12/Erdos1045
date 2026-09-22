import StructuralNote.CommonFiberDerivativeEnergy

/-! The height velocity contains the derivative of the actual closure root.
Its square sum is controlled using closure, rather than a derivative hypothesis. -/

namespace StructuralNote.CommonFiberHeightVelocity

open Erdos1045.EventualExact Complex LensClosure LensClosurePathDerivatives
open CommonClosureEnergy CommonTangentialParameters CommonFiberFirstDerivative
open CommonFiberFirstBounds CommonFiberDerivativeEnergy SchurSpectrum
open scoped BigOperators
noncomputable section

theorem height_velocity_square {m : ℕ} (hm : 2 ≤ m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ) (η : Fin (2 * m) → ℝ)
    (h : Fin (2 * m) → ℂ) (ξ' : ℂ) (hh : ParameterSpace (by omega) h)
    (hz : (∑ j, velocity (by omega) θ v σ ξ η h ξ' j) = 0) (hσ : ∀ j, |σ j| ≤ 1)
    (hsmall : ∀ j, |phase (by omega) θ j - LensClosure.midpoint m j| +
      |heightParameter (coordinates (by omega) v) ξ j| ≤ 1 / 4) :
    (∑ j, heightParameter (coordinates (by omega) h) ξ' j ^ 2) ≤
      2 * (∑ j, coordinates (by omega) h j ^ 2) +
      32 * ∑ j, ‖residual (by omega) θ v σ ξ η h j‖ ^ 2 := by
  have hc := correction_square_bound hm (phase (by omega) θ) σ (coordinates (by omega) v) ξ ξ'
    (residual (by omega) θ v σ ξ η h) hσ hsmall
    (residual_closure_eq (by omega) θ v σ ξ η h ξ' hh hz)
  have hj (j : Fin m) : heightParameter (coordinates (by omega) h) ξ' j ^ 2 ≤
      2 * coordinates (by omega) h j ^ 2 + 2 * ‖ξ'‖ ^ 2 := by
    have hs := pow_le_pow_left₀ (abs_nonneg _) (harmonicFunctional_le_norm (LensClosure.midpoint m j) ξ') 2
    rw [sq_abs] at hs
    unfold heightParameter
    nlinarith [sq_nonneg (coordinates (by omega) h j - harmonicFunctional (LensClosure.midpoint m j) ξ')]
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hj j)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  linarith

theorem height_velocity_energy {m : ℕ} (hm : 2 ≤ m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ) (η : Fin (2 * m) → ℝ)
    (h : Fin (2 * m) → ℂ) (ξ' : ℂ) {B S T : ℝ}
    (hmean : ∑ j, (η j : ℂ) = 0) (hh : ParameterSpace (by omega) h)
    (hz : (∑ j, velocity (by omega) θ v σ ξ η h ξ' j) = 0) (hσ : ∀ j, |σ j| ≤ 1)
    (hsmall : ∀ j, |phase (by omega) θ j - LensClosure.midpoint m j| +
      |heightParameter (coordinates (by omega) v) ξ j| ≤ 1 / 4)
    (hb : ∀ j, ‖LensIncrementDerivatives.body (2 * Real.cos (halfAngle (by omega) θ j)) (σ j)
      (heightParameter (coordinates (by omega) v) ξ j)‖ ≤ B)
    (hs : ∀ j, |Real.sin (halfAngle (by omega) θ j)| ≤ S)
    (he : ∀ j, |phase (by omega) θ j - LensClosure.midpoint m j| +
      |heightParameter (coordinates (by omega) v) ξ j| ≤ T) :
    (2 * m : ℝ) ^ 2 * (∑ j, heightParameter (coordinates (by omega) h) ξ' j ^ 2) ≤
      (384 * B ^ 2 * (2 * m : ℝ) + 768 * Real.pi ^ 2 * S ^ 2) *
        pairEnergy (by omega) (fun j => (η j : ℂ)) +
      (16 * Real.pi ^ 2 + 768 * Real.pi ^ 2 * T ^ 2) * pairEnergy (by omega) h := by
  have ht (j : Fin m) : |heightParameter (coordinates (by omega) v) ξ j| ≤ 1 := by
    have hj := hsmall j
    linarith [abs_nonneg (phase (by omega) θ j - LensClosure.midpoint m j)]
  have hR := residual_sum_energy (by omega) θ v σ ξ η h hmean hσ ht hb hs he
  have hC := coordinate_energy (by omega) h
  have hH := mul_le_mul_of_nonneg_left
    (height_velocity_square hm θ v σ ξ η h ξ' hh hz hσ hsmall) (sq_nonneg (2 * m : ℝ))
  nlinarith only [hR, hC, hH]

end
end StructuralNote.CommonFiberHeightVelocity
