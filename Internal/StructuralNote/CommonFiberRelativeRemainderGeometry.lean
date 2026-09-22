import StructuralNote.CommonFiberHessianGeometryEnergy
import StructuralNote.CommonFiberHessianGeometryDomain
import StructuralNote.RelativeDenominator
import StructuralNote.CommonFiberSparseVariation

/-! Center quotients and their sparse differences with the actual angular
denominators, uniformly on the common domain. -/

namespace StructuralNote.CommonFiberRelativeRemainderGeometry

open Erdos1045 Erdos1045.EventualExact Complex LensClosure
open FiniteFourierLift FourierMultiplier SchurSpectrum SchurLift
open CommonClosureEnergy CommonTangentialParameters CommonDomainClosure CommonDomainRadius
open CommonFiberGeometry CommonFiberBounds CommonFiberSmallCoefficients CommonFiberNonlocalFrames
open CommonFiberHessianGeometryChord CommonFiberHessianGeometryEnergy
open SignedPressureAngular GeometricRelativeRemainder AngularFirstEnergy TotalVariation
open scoped BigOperators
noncomputable section

theorem domain_center_regular_quotient {m : ℕ} (hm : 8 ≤ m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ)
    (hdom : InDomain (by omega) θ v) (hσ : ∀ j, |σ j| ≤ 1)
    (hξ : ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2)
    (hz : closure (phase (by omega) θ) (fun j => 2 * Real.cos (halfAngle (by omega) θ j)) σ (coordinates (by omega) v) ξ = 0)
    (horder : 10 * (logOrder (2 * m) : ℝ) + 1024 ≤ 2 * m) (i j : Fin (2 * m)) :
    ‖quotient (center (by omega) θ v σ ξ) (root (2 * m)) (i, j)‖ ≤
      300 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) := by
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hstep (j : Fin (2 * m)) : ‖difference (by omega) (center (by omega) θ v σ ξ) j‖ ≤
      1200 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2 := by
    apply center_step_bound (by omega) θ v σ ξ hz
    intro k
    have hb := domain_bodyNorm_bound hm θ v σ hdom hξ hσ horder
    have hp := norm_le_pi_norm (fun k => LensIncrementDerivatives.body
      (2 * Real.cos (halfAngle (by omega) θ k)) (σ k)
      (heightParameter (coordinates (by omega) v) ξ k)) k
    have he : ‖fiberIncrement (by omega) θ v σ ξ k‖ = ‖LensIncrementDerivatives.body
        (2 * Real.cos (halfAngle (by omega) θ k)) (σ k)
        (heightParameter (coordinates (by omega) v) ξ k)‖ := by
      simp only [fiberIncrement, LensClosure.increment, LensIncrementDerivatives.body, norm_mul, norm_unit, one_mul]
    rw [he]
    apply (hp.trans hb).trans
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    have hL := logOrder_one_le (show 2 ≤ 2 * m by omega)
    linarith
  have hb := quotient_of_step (by omega) _ (by positivity) hstep i j
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hb
  exact hb.trans_eq (by field_simp; ring)

theorem quotient_true_le {n : ℕ} (θ : Fin n → ℝ) (C : Fin n → ℂ)
    (hw : Function.Injective (root n))
    (hsmall : ∀ i j, ‖quotient (angularError θ) (root n) (i, j)‖ ≤ 1 / 2)
    (p : Fin n × Fin n) :
    ‖quotient C (diameterVector θ) p‖ ≤ 2 * ‖quotient C (root n) p‖ := by
  by_cases hij : p.1 = p.2
  · simp only [quotient, hij, sub_self, zero_div, norm_zero, mul_zero, le_refl]
  have hne := sub_ne_zero.mpr (hw.ne hij)
  have hf : quotient C (diameterVector θ) p =
      quotient C (root n) p / (1 + quotient (angularError θ) (root n) p) := by
    have he : 1 + quotient (angularError θ) (root n) p =
        (diameterVector θ p.1 - diameterVector θ p.2) / (root n p.1 - root n p.2) := by
      unfold quotient angularError
      field_simp
      ring
    rw [he]
    exact (div_div_div_cancel_right₀ hne (C p.1 - C p.2)
      (diameterVector θ p.1 - diameterVector θ p.2)).symm
  rw [hf, norm_div]
  have hb := RelativeDenominator.denominator_norm_lower (hsmall p.1 p.2)
  apply (div_le_iff₀ (by linarith : 0 < ‖1 + quotient (angularError θ) (root n) p‖)).mpr
  nlinarith [norm_nonneg (quotient C (root n) p)]

theorem domain_diameter_injective {m : ℕ} (hm : 2 ≤ m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (hdom : InDomain (by omega) θ v)
    (hsmall : 11 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ≤ 1 / 2) :
    Function.Injective (diameterVector θ) := by
  have he : GeometricRelativeRemainder.configuration (root (2 * m)) (angularError θ) = diameterVector θ := by
    funext j
    simp only [GeometricRelativeRemainder.configuration, angularError, add_sub_cancel]
  rw [← he]
  apply configuration_injective _ _ (HessianAngularReference.root_injective (by omega))
  intro p
  exact ((domain_angularError_ratio (by omega) θ v hdom p.1 p.2).trans hsmall).trans_lt (by norm_num)

theorem domain_center_true_quotient {m : ℕ} (hm : 8 ≤ m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ)
    (hdom : InDomain (by omega) θ v) (hσ : ∀ j, |σ j| ≤ 1)
    (hξ : ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2)
    (hz : closure (phase (by omega) θ) (fun j => 2 * Real.cos (halfAngle (by omega) θ j)) σ (coordinates (by omega) v) ξ = 0)
    (horder : 10 * (logOrder (2 * m) : ℝ) + 1024 ≤ 2 * m)
    (hsmall : 11 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ≤ 1 / 2) (p : Fin (2 * m) × Fin (2 * m)) :
    ‖quotient (center (by omega) θ v σ ξ) (diameterVector θ) p‖ ≤
      600 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) := by
  have ht := quotient_true_le θ (center (by omega) θ v σ ξ)
    (HessianAngularReference.root_injective (by omega))
    (fun i j => (domain_angularError_ratio (by omega) θ v hdom i j).trans hsmall) p
  have hr := domain_center_regular_quotient hm θ v σ ξ hdom hσ hξ hz horder p.1 p.2
  have hh := ht.trans (mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 2))
  exact hh.trans_eq (by ring)

theorem quotient_norm_sum_eq {n : ℕ} (hn : 0 < n) (C : Fin n → ℂ) :
    (∑ p : Fin n × Fin n, ‖quotient C (root n) p‖) = 2 * pairNormSum n (periodize hn C) := by
  have he : Finset.Ico 1 n = (Finset.range n).erase 0 := by ext k; simp; omega
  rw [pairNormSum, he, cyclic_pair_sum hn C norm (by simp)]
  ring

theorem true_quotient_norm_sum {m : ℕ} (hm : 2 ≤ m) (θ : Fin (2 * m) → ℝ)
    (v C : Fin (2 * m) → ℂ) (hdom : InDomain (by omega) θ v)
    (hsmall : 11 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ≤ 1 / 2) :
    (∑ p : Fin (2 * m) × Fin (2 * m), ‖quotient C (diameterVector θ) p‖) ≤
      4 * pairNormSum (2 * m) (periodize (by omega) C) := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun p _ => quotient_true_le θ C
    (HessianAngularReference.root_injective (by omega))
    (fun i j => (domain_angularError_ratio (by omega) θ v hdom i j).trans hsmall) p)
  rw [← Finset.mul_sum, quotient_norm_sum_eq (by omega) C] at hs
  exact hs.trans_eq (by ring)

end
end StructuralNote.CommonFiberRelativeRemainderGeometry
