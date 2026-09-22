import EventualExact.FiniteCircleRigidity
import Erdos1045.GapRigidity

/-! Uniform gap control gives relative edge control without an L2 gap hypothesis. -/

namespace Erdos1045.EventualExact.SupGapEdges

open Complex CyclicAngles GapRigidity FiniteCircleRigidity
open scoped BigOperators
noncomputable section

theorem relativeGap_bound {n : ℕ} (a : Angles n) (hn : 0 < n) (j : ℕ) :
    |relativeGap a j - 1| ≤ ‖gapDeviation a‖ := by
  rw [periodic_mod (relativeGap a) (relativeGap_period a) j]
  exact (norm_le_pi_norm (gapDeviation a) ⟨j % n, Nat.mod_lt _ hn⟩)

theorem angleError_bound {n : ℕ} (a : Angles n) (hn : 0 < n) (j : ℕ) :
    |angleError a j| ≤ 2 * Real.pi * ‖gapDeviation a‖ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hfinite (j : ℕ) (hj : j < n) : |angleError a j| ≤ 2 * Real.pi * ‖gapDeviation a‖ := by
    have hs := scaled_window_error a hn j 0
    have hid : (n : ℝ) * angleError a j =
        2 * Real.pi * (∑ i ∈ Finset.range j, (relativeGap a i - 1)) := by
      simp only [window, zero_add, Nat.cast_zero] at hs
      unfold angleError
      have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
      field_simp at hs ⊢
      nlinarith
    have hab := Finset.abs_sum_le_sum_abs (f := fun i => relativeGap a i - 1) (Finset.range j)
    have hb := Finset.sum_le_sum (s := Finset.range j) (fun i _ => relativeGap_bound a hn i)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hb
    have hm := congrArg abs hid
    rw [abs_mul, abs_of_pos hnR, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)] at hm
    have hjR : (j : ℝ) ≤ n := by exact_mod_cast hj.le
    have hs' := mul_le_mul_of_nonneg_right hjR (norm_nonneg (gapDeviation a))
    nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left (hab.trans hb)
      (show 0 ≤ 2 * Real.pi by positivity)]
  rw [periodic_mod (angleError a) (angleError_period a hn) j]
  exact hfinite _ (Nat.mod_lt _ hn)

theorem circlePerturbation_bound {n : ℕ} (a : Angles n) (hn : 0 < n) (j : ℕ) :
    ‖circlePerturbation a j‖ ≤ 2 * Real.pi * ‖gapDeviation a‖ := by
  unfold circlePerturbation circlePoints
  rw [root_power_eq_circle]
  exact (circle_lipschitz _ _).trans (angleError_bound a hn j)

theorem gap_angle_bound {n : ℕ} (a : Angles n) (hn : 0 < n) (j : ℕ) :
    |window a 1 j - 2 * Real.pi / n| ≤ (2 * Real.pi / n) * ‖gapDeviation a‖ := by
  have hd : 0 < 2 * Real.pi / (n : ℝ) := by positivity
  have he : window a 1 j - 2 * Real.pi / n =
      (2 * Real.pi / n) * (relativeGap a j - 1) := by
    unfold relativeGap
    field_simp
  rw [he, abs_mul, abs_of_pos hd]
  exact mul_le_mul_of_nonneg_left (relativeGap_bound a hn j) hd.le

theorem circle_edge_bound {n : ℕ} (a : Angles n) (hn : 2 ≤ n) (j : ℕ) :
    ‖circlePerturbation a (j + 1) - circlePerturbation a j‖ ≤
      (5 * Real.pi / 2 * ‖gapDeviation a‖) * ‖LocalPhase.regularRoot n - 1‖ := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have he : circlePerturbation a (j + 1) - circlePerturbation a j =
      circlePerturbation a j * (LocalPhase.regularRoot n - 1) +
        circlePoints a j * (circle (window a 1 j) - LocalPhase.regularRoot n) := by
    unfold circlePerturbation
    rw [circlePoints_step, pow_succ]
    ring
  have hg : ‖circle (window a 1 j) - LocalPhase.regularRoot n‖ ≤
      (2 * Real.pi / n) * ‖gapDeviation a‖ :=
    (circle_lipschitz _ _).trans (gap_angle_bound a hn0 j)
  have hp : ‖circlePoints a j‖ = 1 := circle_norm _
  have hld : 4 ≤ (n : ℝ) * ‖LocalPhase.regularRoot n - 1‖ := by
    simpa [mul_comm] using (div_le_iff₀ hnR).mp (root_edge_lower hn)
  have hscale : (2 * Real.pi / (n : ℝ)) * ‖gapDeviation a‖ ≤
      (Real.pi / 2 * ‖gapDeviation a‖) * ‖LocalPhase.regularRoot n - 1‖ := by
    have hm := mul_le_mul_of_nonneg_left hld
      (mul_nonneg (by positivity : 0 ≤ Real.pi / 2) (norm_nonneg (gapDeviation a)))
    apply (mul_le_mul_iff_right₀ hnR).mp
    have hcancel : (n : ℝ) * ((2 * Real.pi / n) * ‖gapDeviation a‖) =
        2 * Real.pi * ‖gapDeviation a‖ := by field_simp
    rw [hcancel]
    nlinarith
  rw [he]
  calc
    _ ≤ ‖circlePerturbation a j * (LocalPhase.regularRoot n - 1)‖ +
        ‖circlePoints a j * (circle (window a 1 j) - LocalPhase.regularRoot n)‖ := norm_add_le _ _
    _ = ‖circlePerturbation a j‖ * ‖LocalPhase.regularRoot n - 1‖ +
        ‖circle (window a 1 j) - LocalPhase.regularRoot n‖ := by rw [norm_mul, norm_mul, hp, one_mul]
    _ ≤ (2 * Real.pi * ‖gapDeviation a‖) * ‖LocalPhase.regularRoot n - 1‖ +
        (Real.pi / 2 * ‖gapDeviation a‖) * ‖LocalPhase.regularRoot n - 1‖ :=
      add_le_add (mul_le_mul_of_nonneg_right (circlePerturbation_bound a hn0 j) (norm_nonneg _))
        (hg.trans hscale)
    _ = _ := by ring

theorem window_le_edge {n : ℕ} (a : Angles n) (hn : 2 ≤ n) (j : ℕ) :
    window a 1 j ≤ (Real.pi / 2) * (1 + ‖gapDeviation a‖) * ‖LocalPhase.regularRoot n - 1‖ := by
  have hgap := (le_abs_self _).trans (gap_angle_bound a (by omega) j)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hr := (div_le_iff₀ hnR).mp (root_edge_lower hn)
  have hb : window a 1 j ≤ (2 * Real.pi / n) * (1 + ‖gapDeviation a‖) := by linarith
  apply hb.trans
  apply (mul_le_mul_iff_right₀ hnR).mp
  have hm := mul_le_mul_of_nonneg_left hr
    (show 0 ≤ Real.pi / 2 * (1 + ‖gapDeviation a‖) by positivity)
  field_simp
  nlinarith

end
end Erdos1045.EventualExact.SupGapEdges
