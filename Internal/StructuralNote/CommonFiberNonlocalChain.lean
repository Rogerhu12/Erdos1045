import StructuralNote.CommonFiberNonlocalAngles
import StructuralNote.CommonFiberNonlocalSlack

/-! Summed radial projections control every nonlocal chord, with the angular
factor retained instead of estimating its entire center correction radially. -/

namespace StructuralNote.CommonFiberNonlocalChain

open Erdos1045 Erdos1045.EventualExact Complex
open LensClosure FiniteFourierLift FourierMultiplier SchurSpectrum
open CommonFiberGeometry CommonFiberNonlocalFrames CommonFiberNonlocalAngles
open CommonFiberNonlocalProjection CommonFiberNonlocalSlack
open scoped BigOperators
noncomputable section

theorem periodize_difference {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) (j : ℕ) :
    periodize hn c (j + 1) - periodize hn c j =
      difference hn c ⟨j % n, Nat.mod_lt _ hn⟩ := by
  simp only [periodize, difference, successor, Nat.mod_add_mod]

theorem chain_sum (c : ℕ → ℂ) (j k : ℕ) :
    c (j + k) - c j = ∑ r ∈ Finset.range k, (c (j + r + 1) - c (j + r)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp only [Nat.add_assoc]
    ring

theorem chain_projection {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) (c : Fin n → ℂ)
    {S B R : ℝ} (hθ : ∀ i, |θ i| ≤ S)
    (hstep : ∀ i, ‖difference hn c i‖ ≤ B)
    (hrad : ∀ i, |radial (meanFrame hn θ i) (difference hn c i)| ≤ R) (j k : ℕ) :
    |radial (unit ((angleLift hn θ j + angleLift hn θ (j + k)) / 2))
      (periodize hn c (j + k) - periodize hn c j)| ≤
        k * (R + (Real.pi * k / n + 2 * S) * B) := by
  rw [chain_sum]
  apply (radial_sum_bound (Finset.range k) _
    (fun r => periodize hn (meanFrame hn θ) (j + r)) _
    (R := R) (B := B) (δ := Real.pi * k / n + 2 * S) ?_ ?_ ?_).trans_eq
    (by simp)
  · intro r _
    rw [periodize_difference]
    exact hrad _
  · intro r _
    rw [periodize_difference]
    exact hstep _
  · intro r hr
    exact meanFrame_distance hn θ hθ j k r (Finset.mem_range.mp hr)

theorem projection_error_bound {n k : ℝ} (hn : 0 < n) (hk : 1 ≤ k) :
    8 * (Real.pi * k / n) * (1 / (1000 * n)) + 4 * (1 / (1000 * n)) ^ 2 +
      4 * k * ((Real.pi * k / n + 2 * (1 / (1000 * n))) * (1 / (1000 * n))) +
      (k * (1 / (1000 * n))) ^ 2 ≤ k ^ 2 / n ^ 2 := by
  have hp := Real.pi_lt_four.le
  have hk0 : 0 ≤ k := by linarith
  have hkk : k ≤ k ^ 2 := by nlinarith [mul_nonneg hk0 (show 0 ≤ k - 1 by linarith)]
  apply (le_of_mul_le_mul_right ?_ (sq_pos_of_pos hn))
  field_simp
  nlinarith [mul_le_mul_of_nonneg_right hp hk0,
    mul_le_mul_of_nonneg_right hp (sq_nonneg k)]

theorem chain_pair_strict {n k : ℕ} (hn : 16 ≤ n) (hk : 2 ≤ k) (hkn : 2 * k ≤ n)
    (θ : Fin n → ℝ) (c : Fin n → ℂ)
    (hθ : ∀ i, |θ i| ≤ 1 / (1000 * (n : ℝ)))
    (hstep : ∀ i, ‖difference (by omega) c i‖ ≤ 1 / (1000 * (n : ℝ)))
    (hrad : ∀ i, |radial (meanFrame (by omega) θ i) (difference (by omega) c i)| ≤ 10 / (n : ℝ) ^ 2)
    (j : ℕ) :
    ‖periodize (by omega) (diameterVector θ) j + periodize (by omega) (diameterVector θ) (j + k) +
      (periodize (by omega) c (j + k) - periodize (by omega) c j)‖ < 2 := by
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
  have hs := projected_slack (n := n) (k := k) (by exact_mod_cast hn) hkR
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

end
end StructuralNote.CommonFiberNonlocalChain
