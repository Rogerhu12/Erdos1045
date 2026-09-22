import StructuralNote.FixedSchurSourceBounds
import StructuralNote.FixedSchurChordBounds
import StructuralNote.FixedSchurDomainBounds
import StructuralNote.FixedSchurDomainSmallness
import StructuralNote.FixedSchurEquations

/-! The source bound on the manuscript's actual common energy domain. -/

namespace StructuralNote.FixedSchurDomainSource

open Real Complex
open Erdos1045.EventualExact FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open CommonClosureEnergy CommonDomainClosure CommonDomainRadius CommonTangentialParameters
open CommonFiberBounds FixedSchurData FixedSchurDomainBounds FixedSchurDomainSmallness
open FixedSchurEquations FixedSchurHarmonicBounds FixedSchurSourceBounds EdgeCoordinates

noncomputable section

theorem domain_X_bound_half {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (hdom : InDomain hm θ v) (j : Fin m) :
    |X (by omega) θ (CommonClosureEnergy.halfIndex j) - 2 * Real.cos (Real.pi / (2 * m : ℝ))| ≤
      40 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 3 +
      25 * (logOrder (2 * m) : ℝ) ^ 2 / (2 * m : ℝ) ^ 4 +
      16 * (logOrder (2 * m) : ℝ) ^ 2 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 4 := by
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hlog : 0 ≤ Real.log (2 * m : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * m by omega))
  have hd := domain_angle_difference hm θ v hdom (CommonClosureEnergy.halfIndex j)
  have hb := domain_angleAverage_bound hm θ v hdom j
  have hs : |Real.sin (Real.pi / (2 * m : ℝ))| ≤ 4 / (2 * m : ℝ) := by
    apply (Real.abs_sin_le_abs).trans
    rw [abs_of_pos (by positivity : 0 < Real.pi / (2 * m : ℝ))]
    exact div_le_div_of_nonneg_right Real.pi_lt_four.le hn.le
  have hdsq : angleDifference (by omega) θ (CommonClosureEnergy.halfIndex j) ^ 2 ≤
      (10 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hd
  have hbsq : angleAverage (by omega) θ (CommonClosureEnergy.halfIndex j) ^ 2 ≤
      (4 * (logOrder (2 * m) : ℝ) * Real.sqrt (Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hb
  calc
    _ ≤ |Real.sin (Real.pi / (2 * m : ℝ))| *
        |angleDifference (by omega) θ (CommonClosureEnergy.halfIndex j)| +
        angleDifference (by omega) θ (CommonClosureEnergy.halfIndex j) ^ 2 / 4 +
        angleAverage (by omega) θ (CommonClosureEnergy.halfIndex j) ^ 2 :=
      FixedSchurChordBounds.actual_X_error hm θ j
    _ ≤ (4 / (2 * m : ℝ)) * (10 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2) +
        (10 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2) ^ 2 / 4 +
        (4 * (logOrder (2 * m) : ℝ) * Real.sqrt (Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2) ^ 2 := by
      gcongr
    _ = _ := by
      simp only [mul_pow, div_pow, Real.sq_sqrt hlog]
      ring

theorem domain_X_bound {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (hdom : InDomain hm θ v) (j : Fin (2 * m)) :
    |X (by omega) θ j - 2 * Real.cos (Real.pi / (2 * m : ℝ))| ≤
      40 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 3 +
      25 * (logOrder (2 * m) : ℝ) ^ 2 / (2 * m : ℝ) ^ 4 +
      16 * (logOrder (2 * m) : ℝ) ^ 2 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 4 := by
  obtain ⟨k, hj | hj⟩ := half_decomposition hm j
  · rw [hj]
    exact domain_X_bound_half hm θ v hdom k
  · rw [hj, X_halfTurn hm θ hdom.1]
    exact domain_X_bound_half hm θ v hdom k

theorem domain_source_bound {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin (2 * m) → ℝ) (hdom : InDomain hm θ v)
    (hσ : ∀ j, σ j = 1 ∨ σ j = -1)
    (hsmall : ∀ j, |Y (by omega) θ j + σ j * epsilon (2 * m) *
      (tangent (by omega) v j + J (baseWord σ) j)| ≤ 1) :
    ‖equationMap hm θ v σ (baseWord σ) - baseWord σ‖ ≤
      10 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) +
      2000 * (logOrder (2 * m) : ℝ) ^ 2 * (1 + Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2 := by
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hlog : 0 ≤ Real.log (2 * m : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * m by omega))
  have hL := FixedSchurDomainSmallness.logOrder_one_le (show 2 ≤ 2 * m by omega)
  have hf := baseWord_norm_le_four (show 2 ≤ 2 * m by omega) hσ
  have hJ : ‖J (baseWord σ)‖ ≤ 8 := (J_norm_le (by omega) _).trans (by linarith)
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro j
  have hp : |tangent (by omega) v j + J (baseWord σ) j| ≤ 11 * (logOrder (2 * m) : ℝ) := by
    have hpoint : |J (baseWord σ) j| ≤ 8 := by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (J (baseWord σ)) j).trans hJ
    have ht := domain_tangent_bound hm θ v hdom j
    have ha := abs_add_le (tangent (by omega) v j) (J (baseWord σ) j)
    linarith
  have hscale : (epsilon (2 * m))⁻¹ ≤ (2 * m : ℝ) ^ 2 / 4 := by
    rw [epsilon_inv (show 2 ≤ 2 * m by omega)]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (CommonFiberNormalProjectionScaled.scale_bounds (show 2 ≤ 2 * m by omega)).2
  have hX := domain_X_bound hm θ v hdom j
  have hb := scalar_source_bound (N := (2 * m : ℝ)) (H := Real.sqrt (Real.log (2 * m : ℝ)))
    hn hL (Real.sqrt_nonneg _) (epsilon_pos (show 2 ≤ 2 * m by omega))
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using epsilon_le (show 2 ≤ 2 * m by omega))
    hscale (hσ j) (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using epsilon_amplitude (show 2 ≤ 2 * m by omega))
    (by simpa only [Real.sq_sqrt hlog] using hX) (domain_Y_bound hm θ v hdom j) hp (hsmall j)
  simpa only [Pi.sub_apply, Real.norm_eq_abs, equationMap, FixedSchurContraction.crossingMap,
    baseWord, Real.sq_sqrt hlog] using hb

end
end StructuralNote.FixedSchurDomainSource
