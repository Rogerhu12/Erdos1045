import StructuralNote.FixedDualClassificationLogFourier

/-! Actual cosine Fourier integrals of the explicit singular kernel in (8.3). -/

namespace StructuralNote.FixedDualClassificationKernelFourier

open Real Set MeasureTheory FixedDualPrimitive FixedDualClassificationLogFourier
open scoped BigOperators
noncomputable section

def weightedSine (k : ℕ) (u : ℝ) : ℝ := (Real.pi / 2 - u) * sin ((2 * k : ℕ) * u)

theorem weightedSine_integrable (k : ℕ) :
    IntervalIntegrable (weightedSine k) volume 0 Real.pi := by
  apply Continuous.intervalIntegrable
  unfold weightedSine
  fun_prop

theorem integral_weightedSine {k : ℕ} (hk : 0 < k) :
    (∫ u in 0..Real.pi, weightedSine k u) = Real.pi / (2 * k) := by
  let c : ℝ := (2 * k : ℕ)
  have hc : c ≠ 0 := by dsimp [c]; positivity
  have hd (u : ℝ) :
      HasDerivAt (fun u : ℝ => (u - Real.pi / 2) * cos (c * u) / c - sin (c * u) / c ^ 2)
        (weightedSine k u) u := by
    have h := ((((hasDerivAt_id u).sub_const (Real.pi / 2)).mul
      (((hasDerivAt_id u).const_mul c).cos)).div_const c).sub
        ((((hasDerivAt_id u).const_mul c).sin).div_const (c ^ 2))
    dsimp only [id_eq, mul_one] at h
    convert h using 1 <;> try rfl
    unfold weightedSine
    change (Real.pi / 2 - u) * sin (c * u) = _
    field_simp
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le Real.pi_pos.le
    (show Continuous (fun u : ℝ => (u - Real.pi / 2) * cos (c * u) / c -
      sin (c * u) / c ^ 2) by fun_prop).continuousOn
    (fun u _ => hd u) (weightedSine_integrable k)
  rw [h]
  simp only [c, sin_nat_mul_pi, cos_nat_mul_pi, mul_zero, sin_zero, cos_zero,
    zero_div, sub_zero, zero_sub, mul_one]
  rw [pow_mul]
  norm_num
  ring

theorem kernel_times_odd_cos (k : ℕ) (u : ℝ) :
    kernel u * cos ((2 * k + 1 : ℕ) * u) =
      -(1 / 4) * (cos ((2 * k : ℕ) * u) + cos ((2 * (k + 1) : ℕ) * u)) -
      (1 / 4) * (cos ((2 * k : ℕ) * u) * logSine u +
        cos ((2 * (k + 1) : ℕ) * u) * logSine u) +
      (1 / 4) * (weightedSine (k + 1) u - weightedSine k u) := by
  have hc : cos u * cos ((2 * k + 1 : ℕ) * u) =
      (cos ((2 * k : ℕ) * u) + cos ((2 * (k + 1) : ℕ) * u)) / 2 := by
    have h := cos_add_cos (((2 * k : ℕ) : ℝ) * u) (((2 * (k + 1) : ℕ) : ℝ) * u)
    rw [show (((2 * k : ℕ) : ℝ) * u + ((2 * (k + 1) : ℕ) : ℝ) * u) / 2 =
        ((2 * k + 1 : ℕ) : ℝ) * u by push_cast; ring,
      show (((2 * k : ℕ) : ℝ) * u - ((2 * (k + 1) : ℕ) : ℝ) * u) / 2 = -u by
        push_cast; ring, cos_neg] at h
    linarith
  have hs : sin u * cos ((2 * k + 1 : ℕ) * u) =
      (sin ((2 * (k + 1) : ℕ) * u) - sin ((2 * k : ℕ) * u)) / 2 := by
    have h := sin_sub_sin (((2 * (k + 1) : ℕ) : ℝ) * u) (((2 * k : ℕ) : ℝ) * u)
    rw [show (((2 * (k + 1) : ℕ) : ℝ) * u - ((2 * k : ℕ) : ℝ) * u) / 2 = u by
        push_cast; ring,
      show (((2 * (k + 1) : ℕ) : ℝ) * u + ((2 * k : ℕ) : ℝ) * u) / 2 =
        ((2 * k + 1 : ℕ) : ℝ) * u by push_cast; ring] at h
    linarith
  calc
    _ = -(1 / 2) * (cos u * cos ((2 * k + 1 : ℕ) * u)) -
        (1 / 2) * (cos u * cos ((2 * k + 1 : ℕ) * u)) * logSine u +
        (1 / 2) * (Real.pi / 2 - u) * (sin u * cos ((2 * k + 1 : ℕ) * u)) := by
      unfold kernel logSine
      ring
    _ = _ := by rw [hc, hs]; unfold weightedSine; ring

theorem kernel_odd_cos_integrable (k : ℕ) :
    IntervalIntegrable (fun u => kernel u * cos ((2 * k + 1 : ℕ) * u)) volume 0 Real.pi := by
  simp_rw [kernel_times_odd_cos]
  exact (((even_cos_integrable k).add (even_cos_integrable (k + 1))).const_mul _).sub
    (((cosine_logSine_integrable k).add (cosine_logSine_integrable (k + 1))).const_mul _) |>.add
      (((weightedSine_integrable (k + 1)).sub (weightedSine_integrable k)).const_mul _)

theorem kernel_odd_cos_integral_split (k : ℕ) :
    (∫ u in 0..Real.pi, kernel u * cos ((2 * k + 1 : ℕ) * u)) =
      -(1 / 4) * ((∫ u in 0..Real.pi, cos ((2 * k : ℕ) * u)) +
        (∫ u in 0..Real.pi, cos ((2 * (k + 1) : ℕ) * u))) -
      (1 / 4) * ((∫ u in 0..Real.pi, cos ((2 * k : ℕ) * u) * logSine u) +
        (∫ u in 0..Real.pi, cos ((2 * (k + 1) : ℕ) * u) * logSine u)) +
      (1 / 4) * ((∫ u in 0..Real.pi, weightedSine (k + 1) u) -
        (∫ u in 0..Real.pi, weightedSine k u)) := by
  simp_rw [kernel_times_odd_cos]
  rw [intervalIntegral.integral_add
      ((((even_cos_integrable k).add (even_cos_integrable (k + 1))).const_mul _).sub
        (((cosine_logSine_integrable k).add (cosine_logSine_integrable (k + 1))).const_mul _))
      (((weightedSine_integrable (k + 1)).sub (weightedSine_integrable k)).const_mul _),
    intervalIntegral.integral_sub
      (((even_cos_integrable k).add (even_cos_integrable (k + 1))).const_mul _)
      (((cosine_logSine_integrable k).add (cosine_logSine_integrable (k + 1))).const_mul _)]
  simp_rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_add (even_cos_integrable k) (even_cos_integrable (k + 1)),
    intervalIntegral.integral_add (cosine_logSine_integrable k) (cosine_logSine_integrable (k + 1)),
    intervalIntegral.integral_sub (weightedSine_integrable (k + 1)) (weightedSine_integrable k)]

theorem kernel_odd_cos_integral {k : ℕ} (hk : 0 < k) :
    (∫ u in 0..Real.pi, kernel u * cos ((2 * k + 1 : ℕ) * u)) =
      Real.pi / (4 * (k + 1)) := by
  rw [kernel_odd_cos_integral_split, integral_even_cos hk, integral_even_cos (by omega),
    integral_even_cos_logSine hk, integral_even_cos_logSine (by omega),
    integral_weightedSine hk, integral_weightedSine (by omega)]
  have hkR : (k : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem kernel_first_cos_integral : (∫ u in 0..Real.pi, kernel u * cos u) = 0 := by
  have h := kernel_odd_cos_integral_split 0
  norm_num only [Nat.reduceMul, Nat.reduceAdd, Nat.cast_one, one_mul, Nat.cast_zero,
    zero_mul, cos_zero, one_mul] at h
  have hc := integral_even_cos (by decide : 0 < 1)
  have hl := integral_even_cos_logSine (by decide : 0 < 1)
  norm_num only [Nat.reduceMul, Nat.cast_ofNat] at hc hl
  rw [hc, hl, integral_weightedSine (by decide : 0 < 1)] at h
  simp only [weightedSine, Nat.cast_zero, zero_mul, sin_zero, mul_zero,
    intervalIntegral.integral_zero, intervalIntegral.integral_const, sub_zero, smul_eq_mul,
    mul_one, integral_logSine] at h
  norm_num at h
  linarith

theorem kernel_multiplier {p : ℕ} (hp : Odd p) (hp3 : 3 ≤ p) :
    (2 / Real.pi) * (∫ u in 0..Real.pi, kernel u * cos (p * u)) = 1 / (p + 1) := by
  obtain ⟨k, rfl⟩ := hp
  rw [kernel_odd_cos_integral (by omega)]
  push_cast
  field_simp
  ring

end
end StructuralNote.FixedDualClassificationKernelFourier

