import Erdos1045.LocalConfiguration

/-!
# From the circle energy deficit to uniform relative edge control

The stronger 1/sqrt(n) angular estimate of the manuscript is unnecessary here:
the elementary bound 2*pi*sqrt(gap variance) already tends to zero and gives
the required relative, rather than absolute, edge estimate.
-/

namespace Erdos1045.GapRigidity

open Complex CyclicAngles
open scoped BigOperators Topology
open Filter
noncomputable section

def variance {n : ℕ} (a : Angles n) : ℝ :=
  LogDefect.deviation (Finset.range n) (relativeGap a)

def gapError {n : ℕ} (a : Angles n) : ℝ := Real.sqrt (variance a)

def angleError {n : ℕ} (a : Angles n) (j : ℕ) : ℝ :=
  a.angle j - a.angle 0 - (2 * Real.pi / n) * j

def circle (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * I)

def circlePoints {n : ℕ} (a : Angles n) (j : ℕ) : ℂ := circle (a.angle j - a.angle 0)

def circlePerturbation {n : ℕ} (a : Angles n) (j : ℕ) : ℂ :=
  circlePoints a j - LocalPhase.regularRoot n ^ j

theorem variance_nonneg {n : ℕ} (a : Angles n) : 0 ≤ variance a :=
  LogDefect.deviation_nonneg _ _

theorem gapError_nonneg {n : ℕ} (a : Angles n) : 0 ≤ gapError a := Real.sqrt_nonneg _

theorem energy_nonneg {n : ℕ} (a : Angles n) (hn : 3 ≤ n) : 0 ≤ energy a := by
  have hd := LogDefect.total_nonneg (Finset.range n) (relativeGap a)
    (fun i _ => relativeGap_pos a (by omega) i)
  linarith [energy_ge_gapDefect a hn]

theorem gap_deviation_bound {n : ℕ} (a : Angles n) (hn : 0 < n) (j : ℕ) :
    |relativeGap a j - 1| ≤ gapError a := by
  have hb : (relativeGap a (j % n) - 1) ^ 2 ≤ variance a :=
    Finset.single_le_sum (fun i _ => sq_nonneg (relativeGap a i - 1))
      (Finset.mem_range.mpr (Nat.mod_lt _ hn))
  rw [periodic_mod (relativeGap a) (relativeGap_period a) j]
  exact Real.abs_le_sqrt hb

theorem variance_tendsto_zero {N : ℕ → ℕ} (a : ∀ k, Angles (N k))
    (hN : ∀ k, 3 ≤ N k) (hE : Tendsto (fun k => energy (a k)) atTop (nhds 0)) :
    Tendsto (fun k => variance (a k)) atTop (nhds 0) := by
  have hbound (k : ℕ) : variance (a k) ≤ (2 * energy (a k) + 6) * energy (a k) / 2 :=
    gap_deviation_of_energy_le (a k) (hN k) (energy_nonneg (a k) (hN k)) le_rfl
  have ht : Tendsto (fun k => (2 * energy (a k) + 6) * energy (a k) / 2)
      atTop (nhds 0) := by
    convert (((tendsto_const_nhds.mul hE).add tendsto_const_nhds).mul hE).div_const 2 using 1
    norm_num
  exact squeeze_zero (fun k => variance_nonneg (a k)) hbound ht

theorem gapError_tendsto_zero {N : ℕ → ℕ} (a : ∀ k, Angles (N k))
    (hN : ∀ k, 3 ≤ N k) (hE : Tendsto (fun k => energy (a k)) atTop (nhds 0)) :
    Tendsto (fun k => gapError (a k)) atTop (nhds 0) := by
  simpa [gapError, Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp
    (variance_tendsto_zero a hN hE)

theorem angleError_period {n : ℕ} (a : Angles n) (hn : 0 < n) (j : ℕ) :
    angleError a (j + n) = angleError a j := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [angleError, Nat.cast_add, a.period]
  field_simp
  ring

theorem angleError_bound {n : ℕ} (a : Angles n) (hn : 0 < n) (j : ℕ) :
    |angleError a j| ≤ 2 * Real.pi * gapError a := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hfinite (j : ℕ) (hj : j < n) : |angleError a j| ≤ 2 * Real.pi * gapError a := by
    have hs := scaled_window_error a hn j 0
    have hid : (n : ℝ) * angleError a j =
        2 * Real.pi * (∑ i ∈ Finset.range j, (relativeGap a i - 1)) := by
      simp only [window, zero_add, Nat.cast_zero] at hs
      unfold angleError
      have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
      field_simp at hs ⊢
      nlinarith
    have hab := Finset.abs_sum_le_sum_abs (f := fun i => relativeGap a i - 1) (Finset.range j)
    have hb := Finset.sum_le_sum (s := Finset.range j) (fun i _ => gap_deviation_bound a hn i)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hb
    have hm := congrArg abs hid
    rw [abs_mul, abs_of_pos hnR, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)] at hm
    have hjR : (j : ℝ) ≤ n := by exact_mod_cast hj.le
    have hs' := mul_le_mul_of_nonneg_right hjR (gapError_nonneg a)
    nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left (hab.trans hb)
      (show 0 ≤ 2 * Real.pi by positivity)]
  rw [periodic_mod (angleError a) (angleError_period a hn) j]
  exact hfinite _ (Nat.mod_lt _ hn)

theorem circle_norm (t : ℝ) : ‖circle t‖ = 1 := Complex.norm_exp_ofReal_mul_I t

theorem circle_add (s t : ℝ) : circle (s + t) = circle s * circle t := by
  simp [circle, add_mul, Complex.exp_add]

theorem circle_lipschitz (s t : ℝ) : ‖circle s - circle t‖ ≤ |s - t| := by
  have he : circle s - circle t = circle t * (circle (s - t) - 1) := by
    rw [mul_sub, ← circle_add, show t + (s - t) = s by ring, mul_one]
  rw [he, norm_mul, circle_norm, one_mul]
  simpa [circle, mul_comm, Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := s - t))

theorem root_power_eq_circle (n j : ℕ) :
    LocalPhase.regularRoot n ^ j = circle ((2 * Real.pi / n) * j) := by
  unfold LocalPhase.regularRoot circle
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem circlePerturbation_bound {n : ℕ} (a : Angles n) (hn : 0 < n) (j : ℕ) :
    ‖circlePerturbation a j‖ ≤ 2 * Real.pi * gapError a := by
  unfold circlePerturbation circlePoints
  rw [root_power_eq_circle]
  exact (circle_lipschitz _ _).trans (angleError_bound a hn j)

theorem gap_angle_bound {n : ℕ} (a : Angles n) (hn : 0 < n) (j : ℕ) :
    |window a 1 j - 2 * Real.pi / n| ≤ (2 * Real.pi / n) * gapError a := by
  have hd : 0 < 2 * Real.pi / (n : ℝ) := by positivity
  have he : window a 1 j - 2 * Real.pi / n =
      (2 * Real.pi / n) * (relativeGap a j - 1) := by
    unfold relativeGap
    field_simp
  rw [he, abs_mul, abs_of_pos hd]
  exact mul_le_mul_of_nonneg_left (gap_deviation_bound a hn j) hd.le

theorem root_edge_lower {n : ℕ} (hn : 2 ≤ n) :
    4 / (n : ℝ) ≤ ‖LocalPhase.regularRoot n - 1‖ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hs := LocalTrigonometry.scaled_sine_lower hnR (by norm_num : (0 : ℝ) ≤ 1) (by linarith)
  have hp := LocalTrigonometry.base_sine_pos (by linarith : (1 : ℝ) < n)
  unfold LocalPhase.regularRoot
  rw [mul_comm _ I, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs]
  have he : (2 * Real.pi / (n : ℝ)) / 2 = Real.pi / n := by ring
  rw [he, abs_of_pos (mul_pos (by norm_num) hp)]
  norm_num at hs
  calc
    4 / (n : ℝ) = 2 * (2 / n) := by ring
    _ ≤ 2 * Real.sin (Real.pi / n) := mul_le_mul_of_nonneg_left hs (by norm_num)

theorem circlePoints_step {n : ℕ} (a : Angles n) (j : ℕ) :
    circlePoints a (j + 1) = circlePoints a j * circle (window a 1 j) := by
  unfold circlePoints
  rw [← circle_add]
  unfold window
  simp only [Nat.cast_add, Nat.cast_one]
  congr 1
  ring

theorem circlePoints_periodic {n : ℕ} (a : Angles n) : Function.Periodic (circlePoints a) n := by
  intro j
  unfold circlePoints
  simp only [Nat.cast_add, a.period]
  rw [show a.angle (j : ℤ) + 2 * Real.pi - a.angle 0 =
    (a.angle (j : ℤ) - a.angle 0) + 2 * Real.pi by ring, circle_add]
  have hp : circle (2 * Real.pi) = 1 := by simp [circle, Complex.exp_two_pi_mul_I]
  rw [hp, mul_one]

theorem circlePerturbation_periodic {n : ℕ} (a : Angles n) (hn : 0 < n) :
    Function.Periodic (circlePerturbation a) n := by
  intro j
  simp only [circlePerturbation, circlePoints_periodic a j, pow_add,
    LocalDFT.regularRoot_pow hn, mul_one]

theorem circle_edge_bound {n : ℕ} (a : Angles n) (hn : 2 ≤ n) (j : ℕ) :
    ‖circlePerturbation a (j + 1) - circlePerturbation a j‖ ≤
      (5 * Real.pi / 2 * gapError a) * ‖LocalPhase.regularRoot n - 1‖ := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have he : circlePerturbation a (j + 1) - circlePerturbation a j =
      circlePerturbation a j * (LocalPhase.regularRoot n - 1) +
        circlePoints a j * (circle (window a 1 j) - LocalPhase.regularRoot n) := by
    unfold circlePerturbation
    rw [circlePoints_step, pow_succ]
    ring
  have hg : ‖circle (window a 1 j) - LocalPhase.regularRoot n‖ ≤
      (2 * Real.pi / n) * gapError a := by
    exact (circle_lipschitz _ _).trans (gap_angle_bound a hn0 j)
  have hp : ‖circlePoints a j‖ = 1 := circle_norm _
  have hl := root_edge_lower hn
  have hld : 4 ≤ (n : ℝ) * ‖LocalPhase.regularRoot n - 1‖ := by
    simpa [mul_comm] using (div_le_iff₀ hnR).mp hl
  have hscale : (2 * Real.pi / (n : ℝ)) * gapError a ≤
      (Real.pi / 2 * gapError a) * ‖LocalPhase.regularRoot n - 1‖ := by
    have hm := mul_le_mul_of_nonneg_left hld
      (mul_nonneg (by positivity : 0 ≤ Real.pi / 2) (gapError_nonneg a))
    apply (mul_le_mul_iff_right₀ hnR).mp
    have hcancel : (n : ℝ) * ((2 * Real.pi / n) * gapError a) =
        2 * Real.pi * gapError a := by field_simp
    rw [hcancel]
    nlinarith
  rw [he]
  calc
    _ ≤ ‖circlePerturbation a j * (LocalPhase.regularRoot n - 1)‖ +
        ‖circlePoints a j * (circle (window a 1 j) - LocalPhase.regularRoot n)‖ := norm_add_le _ _
    _ = ‖circlePerturbation a j‖ * ‖LocalPhase.regularRoot n - 1‖ +
        ‖circle (window a 1 j) - LocalPhase.regularRoot n‖ := by rw [norm_mul, norm_mul, hp, one_mul]
    _ ≤ (2 * Real.pi * gapError a) * ‖LocalPhase.regularRoot n - 1‖ +
        (Real.pi / 2 * gapError a) * ‖LocalPhase.regularRoot n - 1‖ :=
      add_le_add (mul_le_mul_of_nonneg_right (circlePerturbation_bound a hn0 j) (norm_nonneg _))
        (hg.trans hscale)
    _ = _ := by ring

def circleEdgeError {n : ℕ} (a : Angles n) : ℝ := 5 * Real.pi / 2 * gapError a

theorem circleEdgeError_tendsto_zero {N : ℕ → ℕ} (a : ∀ k, Angles (N k))
    (hN : ∀ k, 3 ≤ N k) (hE : Tendsto (fun k => energy (a k)) atTop (nhds 0)) :
    Tendsto (fun k => circleEdgeError (a k)) atTop (nhds 0) := by
  simpa [circleEdgeError] using (gapError_tendsto_zero a hN hE).const_mul (5 * Real.pi / 2)

end
end Erdos1045.GapRigidity
