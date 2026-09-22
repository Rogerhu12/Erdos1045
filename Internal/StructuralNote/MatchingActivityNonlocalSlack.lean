import StructuralNote.CommonFiberNonlocalChain

/-! Quantitative distant-pair slack, stable under unsaturated radial deficits. -/

namespace StructuralNote.MatchingActivityNonlocalSlack

open Erdos1045 Erdos1045.EventualExact Complex
open LensClosure FiniteFourierLift FourierMultiplier SchurSpectrum
open CommonFiberGeometry CommonFiberNonlocalFrames CommonFiberNonlocalAngles
open CommonFiberNonlocalProjection CommonFiberNonlocalSlack CommonFiberNonlocalChain
open scoped BigOperators
noncomputable section

theorem projected_slack_margin {n k : ℝ} (hn : 16 ≤ n) (hk : 2 ≤ k) (hkn : 2 * k ≤ n)
    (hdiscrete : k = 2 ∨ 3 ≤ k) :
    4 - 4 * Real.sin (Real.pi * k / n) ^ 2 + 40 * k / n ^ 2 + k ^ 2 / n ^ 2 ≤
      4 - k ^ 2 / n ^ 2 := by
  have hn0 : 0 < n := by linarith
  rcases hdiscrete with rfl | hk3
  · have hs := offset_two_sine hn
    rw [mul_comm Real.pi 2]
    simp only [div_eq_mul_inv] at hs ⊢
    nlinarith [show (0 : ℝ) ≤ (n ^ 2)⁻¹ by positivity]
  · have hx0 : 0 ≤ Real.pi * k / n := by positivity
    have hxπ : Real.pi * k / n ≤ Real.pi / 2 := by
      apply (div_le_iff₀ hn0).2
      nlinarith [Real.pi_pos]
    have hs := Real.mul_le_sin hx0 hxπ
    have he : (2 / Real.pi) * (Real.pi * k / n) = 2 * k / n := by field_simp
    rw [he] at hs
    have hs2 := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * k / n) hs 2
    have hg : 0 ≤ 14 * k ^ 2 - 40 * k := by
      nlinarith [mul_nonneg (show 0 ≤ k by linarith) (show 0 ≤ k - 3 by linarith)]
    have hg' := div_nonneg hg (sq_nonneg n)
    have he₂ : (2 * k / n) ^ 2 = 4 * k ^ 2 / n ^ 2 := by ring
    rw [he₂] at hs2
    simp only [div_eq_mul_inv] at hs2 hg' ⊢
    nlinarith

theorem chain_pair_squared_slack {n k : ℕ} (hn : 16 ≤ n) (hk : 2 ≤ k) (hkn : 2 * k ≤ n)
    (θ : Fin n → ℝ) (c : Fin n → ℂ)
    (hθ : ∀ i, |θ i| ≤ 1 / (1000 * (n : ℝ)))
    (hstep : ∀ i, ‖difference (by omega) c i‖ ≤ 1 / (1000 * (n : ℝ)))
    (hrad : ∀ i, |radial (meanFrame (by omega) θ i) (difference (by omega) c i)| ≤ 10 / (n : ℝ) ^ 2)
    (j : ℕ) :
    ‖periodize (by omega) (diameterVector θ) j + periodize (by omega) (diameterVector θ) (j + k) +
      (periodize (by omega) c (j + k) - periodize (by omega) c j)‖ ^ 2 ≤ 4 - (k : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hp := chain_projection (by omega) θ c hθ hstep hrad j k
  have hb := LocalChord.norm_chain (periodize (by omega) c)
    (NonlocalFeasibility.periodize_step_bound (by omega) c hstep) j k
  have hd := pair_distance_sq_bound (angleLift (by omega) θ j) (angleLift (by omega) θ (j + k))
    (periodize (by omega) c (j + k) - periodize (by omega) c j) hp hb
  have he := half_angle_error (by omega) θ hθ j k
  have hc := cos_square_perturbation (Real.pi * k / n)
    ((angleLift (by omega) θ (j + k) - angleLift (by omega) θ j) / 2)
  rw [abs_of_nonneg (by positivity : 0 ≤ Real.pi * k / n)] at hc
  have herr := projection_error_bound hn0 (show (1 : ℝ) ≤ k by linarith)
  have hs := projected_slack_margin (n := n) (k := k) (by exact_mod_cast hn) hkR
    (by exact_mod_cast hkn) (by
      by_cases h : k = 2
      · left; exact_mod_cast h
      · right; exact_mod_cast (show 3 ≤ k by omega))
  have he2 := pow_le_pow_left₀ (abs_nonneg _) he 2
  have he1 := mul_le_mul_of_nonneg_left he (show 0 ≤ 2 * (Real.pi * k / n) by positivity)
  have htrig := Real.sin_sq_add_cos_sq (Real.pi * k / n)
  rw [diameter_periodize, diameter_periodize]
  simp only [div_eq_mul_inv] at hd hc herr hs he1 he2 htrig ⊢
  nlinarith

theorem small_perturbation_strict {n k : ℝ} (hn : 1 ≤ n) (hk : 2 ≤ k) {x e : ℂ}
    (hx : ‖x‖ ^ 2 ≤ 4 - k ^ 2 / n ^ 2) (he : ‖e‖ ≤ 1 / (10 * n ^ 2)) : ‖x + e‖ < 2 := by
  have hn0 : 0 < n := by linarith
  have hn2 : 1 ≤ n ^ 2 := by nlinarith
  have hk2 : 4 ≤ k ^ 2 := by nlinarith
  have hx2 : ‖x‖ ≤ 2 := by nlinarith [div_nonneg (sq_nonneg k) (sq_nonneg n), norm_nonneg x]
  have he1 : ‖e‖ ≤ 1 := by
    have hh : 1 / (10 * n ^ 2) ≤ (1 : ℝ) := (div_le_one (by positivity)).2 (by nlinarith)
    exact he.trans hh
  have he2 : ‖e‖ ^ 2 ≤ ‖e‖ := by nlinarith [norm_nonneg e]
  have hm := mul_le_mul_of_nonneg_right hx2 (norm_nonneg e)
  have hb := norm_add_le x e
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hsmall : 5 * ‖e‖ ≤ 1 / (2 * n ^ 2) := by
    have hh := mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 5)
    calc
      _ ≤ 5 * (1 / (10 * n ^ 2)) := hh
      _ = _ := by ring
  have hg : 1 / (2 * n ^ 2) < k ^ 2 / n ^ 2 := by
    have hh : (1 : ℝ) / 2 < k ^ 2 := by linarith
    simpa only [div_mul_eq_div_div] using (div_lt_div_of_pos_right hh (sq_pos_of_pos hn0))
  nlinarith only [hx, he2, hm, hsq, hsmall, hg, norm_nonneg (x + e)]

end
end StructuralNote.MatchingActivityNonlocalSlack
