import StructuralNote.CommonFiberDerivativeEnergy
import StructuralNote.CommonFiberBounds

/-! The three derivative coefficients are uniformly small on the literal
logarithmic common energy domain, including the actual closure correction. -/

namespace StructuralNote.CommonFiberSmallCoefficients

open Erdos1045.EventualExact Complex LensClosure LensIncrementDerivatives
open CommonClosureEnergy CommonTangentialParameters CommonDomainClosure CommonDomainRadius
open CommonFiberBounds CommonFiberDerivativeEnergy FiniteFourierLift SchurSpectrum
open scoped BigOperators
noncomputable section

theorem domain_angle_bounds {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (hdom : InDomain hm θ v)
    (horder : 10 * (logOrder (2 * m) : ℝ) + 1024 ≤ 2 * m) (j : Fin m) :
    2 / (2 * m : ℝ) ≤ halfAngle hm θ j ∧ halfAngle hm θ j ≤ 5 / (2 * m : ℝ) := by
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hsmall : 10 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2 ≤ 1 / (2 * m) := by
    have he : 1 / (2 * m : ℝ) = (2 * m) / (2 * m) ^ 2 := by field_simp
    rw [he]
    exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
  have hη := (domain_angle_difference hm θ v hdom (CommonClosureEnergy.halfIndex j)).trans hsmall
  have hlow : (3 : ℝ) / (2 * m) < Real.pi / (2 * m) := div_lt_div_of_pos_right Real.pi_gt_three hn
  have hhigh : Real.pi / (2 * m) < (4 : ℝ) / (2 * m) := div_lt_div_of_pos_right Real.pi_lt_four hn
  unfold halfAngle
  simp only [div_eq_mul_inv] at hlow hhigh hη ⊢
  constructor <;> linarith [(abs_le.mp hη).1, (abs_le.mp hη).2]

theorem domain_width_bound {m : ℕ} (hm : 8 ≤ m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (hdom : InDomain (by omega) θ v) {ξ : ℂ}
    (hξ : ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2)
    (horder : 10 * (logOrder (2 * m) : ℝ) + 1024 ≤ 2 * m) (j : Fin m) :
    0 ≤ Lens.width (2 * Real.cos (halfAngle (by omega) θ j)) (heightParameter (coordinates (by omega) v) ξ j) ∧
      Lens.width (2 * Real.cos (halfAngle (by omega) θ j)) (heightParameter (coordinates (by omega) v) ξ j) ≤
        25 / (2 * m : ℝ) ^ 2 := by
  obtain ⟨_, ht, hw⟩ := domain_lens_positive hm θ v hdom hξ horder j
  have ha := domain_angle_bounds (by omega) θ v hdom horder j
  have ha0 : 0 ≤ halfAngle (by omega) θ j := (by positivity : (0 : ℝ) ≤ 2 / (2 * m)).trans ha.1
  have hJ := Lens.height_sq ht
  have hJ0 := Lens.height_nonneg (heightParameter (coordinates (by omega) v) ξ j)
  have hJ2 : Lens.height (heightParameter (coordinates (by omega) v) ξ j) ≤ 2 := by
    nlinarith [sq_nonneg (heightParameter (coordinates (by omega) v) ξ j)]
  have hcos := Real.one_sub_sq_div_two_le_cos (x := halfAngle (by omega) θ j)
  have hasq := pow_le_pow_left₀ ha0 ha.2 2
  norm_num [div_pow] at hasq
  constructor
  · exact (by positivity : (0 : ℝ) ≤ 1 / (2 * (2 * m : ℝ) ^ 2)).trans hw
  · unfold Lens.width
    nlinarith

theorem domain_bodyNorm_bound {m : ℕ} (hm : 8 ≤ m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (hdom : InDomain (by omega) θ v) {ξ : ℂ}
    (hξ : ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2) (hσ : ∀ j, |σ j| ≤ 1)
    (horder : 10 * (logOrder (2 * m) : ℝ) + 1024 ≤ 2 * m) :
    bodyNorm (by omega) θ v σ ξ ≤ (10 * (logOrder (2 * m) : ℝ) + 1049) / (2 * m : ℝ) ^ 2 := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  obtain ⟨hw0, hw⟩ := domain_width_bound hm θ v hdom hξ horder j
  have ht := domain_height_bound (by omega) θ v hdom hξ j
  have hh := norm_add_le
    (((σ j * Lens.width (2 * Real.cos (halfAngle (by omega) θ j))
      (heightParameter (coordinates (by omega) v) ξ j) : ℝ) : ℂ))
    ((heightParameter (coordinates (by omega) v) ξ j : ℂ) * I)
  simp only [norm_mul, norm_real, Real.norm_eq_abs, norm_I, mul_one,
    abs_of_nonneg hw0] at hh
  change ‖body (2 * Real.cos (halfAngle (by omega) θ j)) (σ j)
    (heightParameter (coordinates (by omega) v) ξ j)‖ ≤ _
  have hs := mul_le_mul_of_nonneg_right (hσ j) hw0
  dsimp [body]
  have hfinal : 25 / (2 * m : ℝ) ^ 2 + (10 * (logOrder (2 * m) : ℝ) + 1024) / (2 * m : ℝ) ^ 2 =
      (10 * (logOrder (2 * m) : ℝ) + 1049) / (2 * m : ℝ) ^ 2 := by ring
  rw [← hfinal]
  nlinarith

theorem domain_sineNorm_bound {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (hdom : InDomain hm θ v)
    (horder : 10 * (logOrder (2 * m) : ℝ) + 1024 ≤ 2 * m) : sineNorm hm θ ≤ 5 / (2 * m : ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  have ha := domain_angle_bounds hm θ v hdom horder j
  have ha0 : 0 ≤ halfAngle hm θ j := (by positivity : (0 : ℝ) ≤ 2 / (2 * m)).trans ha.1
  rw [Real.norm_eq_abs]
  exact Real.abs_sin_le_abs.trans ((abs_of_nonneg ha0).le.trans ha.2)

theorem domain_theta_bound {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (hdom : InDomain hm θ v) (j : Fin (2 * m)) :
    |θ j| ≤ 4 * (logOrder (2 * m) : ℝ) * Real.sqrt (Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2 := by
  have hn : (2 : ℝ) ≤ 2 * m := by exact_mod_cast (show 2 ≤ 2 * m by omega)
  have hlog : 0 ≤ Real.log (2 * m : ℝ) := Real.log_nonneg (by linarith)
  have hA := (domain_energy_bounds hm θ v hdom).1
  have hp := DiscreteSobolev.pointwise_sq_le (by omega : 2 ≤ 2 * m)
    (fun j => (θ j : ℂ)) hdom.2.1 j
  simp only [norm_real, Real.norm_eq_abs, sq_abs, Nat.cast_mul, Nat.cast_ofNat] at hp
  have hb : pairEnergy (by omega) (fun j => (θ j : ℂ)) ≤
      (logOrder (2 * m) : ℝ) ^ 2 / (2 * m : ℝ) ^ 2 := by
    simpa only [energyRadius, Nat.cast_mul, Nat.cast_ofNat] using hA
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs]
  calc
    _ ≤ 12 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 *
        ((logOrder (2 * m) : ℝ) ^ 2 / (2 * m : ℝ) ^ 2) :=
      hp.trans (mul_le_mul_of_nonneg_left hb (by positivity))
    _ ≤ 16 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 *
        ((logOrder (2 * m) : ℝ) ^ 2 / (2 * m : ℝ) ^ 2) := by gcongr; norm_num
    _ = _ := by simp only [div_pow, mul_pow, Real.sq_sqrt hlog]; ring

theorem domain_tangentErrorNorm_bound {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (hdom : InDomain hm θ v) {ξ : ℂ}
    (hξ : ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2) :
    tangentErrorNorm hm θ v ξ ≤
      (4 * (logOrder (2 * m) : ℝ) * Real.sqrt (Real.log (2 * m : ℝ)) +
        10 * (logOrder (2 * m) : ℝ) + 1024) / (2 * m : ℝ) ^ 2 := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  have h₁ := domain_theta_bound hm θ v hdom (CommonClosureEnergy.halfIndex j)
  have h₂ := domain_theta_bound hm θ v hdom (successor (by omega) (CommonClosureEnergy.halfIndex j))
  have hsum := abs_add_le (θ (CommonClosureEnergy.halfIndex j))
    (θ (successor (by omega) (CommonClosureEnergy.halfIndex j)))
  have ht := domain_height_bound hm θ v hdom hξ j
  rw [Real.norm_of_nonneg (by positivity)]
  simp only [phase, add_sub_cancel_left, angleAverage, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have he :
      (4 * (logOrder (2 * m) : ℝ) * Real.sqrt (Real.log (2 * m : ℝ)) +
        10 * (logOrder (2 * m) : ℝ) + 1024) / (2 * m : ℝ) ^ 2 =
      4 * (logOrder (2 * m) : ℝ) * Real.sqrt (Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2 +
        (10 * (logOrder (2 * m) : ℝ) + 1024) / (2 * m : ℝ) ^ 2 := by ring
  rw [he]
  linarith

end
end StructuralNote.CommonFiberSmallCoefficients
