import StructuralNote.FixedDualEndpointContinuity
import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Fourier integrals of the actual logarithmic sine, proved by a finite
trigonometric identity and endpoint-safe integration by parts. -/

namespace StructuralNote.FixedDualClassificationLogFourier

open Real Set MeasureTheory
open scoped BigOperators
noncomputable section

def logSine (u : ℝ) : ℝ := log (2 * sin u)

theorem logSine_integrable : IntervalIntegrable logSine volume 0 Real.pi := by
  have h : IntervalIntegrable (fun u => log 2 + log (sin u)) volume 0 Real.pi :=
    intervalIntegrable_const.add intervalIntegrable_log_sin
  apply h.congr_uIoo
  intro u hu
  rw [uIoo_of_lt Real.pi_pos] at hu
  exact (Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (sin_pos_of_pos_of_lt_pi hu.1 hu.2).ne').symm

theorem integral_logSine : (∫ u in 0..Real.pi, logSine u) = 0 := by
  calc
    _ = ∫ u in 0..Real.pi, log 2 + log (sin u) := by
      apply intervalIntegral.integral_congr_Ioo_of_le Real.pi_pos.le
      intro u hu
      exact Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (sin_pos_of_pos_of_lt_pi hu.1 hu.2).ne'
    _ = 0 := by
      rw [intervalIntegral.integral_add intervalIntegrable_const
          (show IntervalIntegrable (fun u => log (sin u)) volume 0 Real.pi from
            intervalIntegrable_log_sin),
        intervalIntegral.integral_const, integral_log_sin_zero_pi]
      simp only [sub_zero, smul_eq_mul]
      ring

theorem sine_log_continuous : Continuous (fun u => sin u * logSine u) := by
  have he : (fun u : ℝ => sin u * logSine u) =
      fun u => ((2 * sin u) * log (2 * sin u)) / 2 := by
    funext u
    unfold logSine
    ring
  rw [he]
  exact (continuous_mul_log.comp (continuous_const.mul continuous_sin)).div_const 2

theorem multiple_sine_log_continuous (k : ℕ) :
    Continuous (fun u => sin (k * u) * logSine u) := by
  induction k with
  | zero => simpa using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
  | succ k ih =>
    have he : (fun u : ℝ => sin ((k + 1 : ℕ) * u) * logSine u) =
        fun u => (sin (k * u) * logSine u) * cos u +
          cos (k * u) * (sin u * logSine u) := by
      funext u
      push_cast
      rw [add_mul, one_mul, sin_add]
      ring
    rw [he]
    exact (ih.mul continuous_cos).add
      ((continuous_cos.comp (continuous_const.mul continuous_id)).mul sine_log_continuous)

/-- A continuous trigonometric polynomial representing `sin(2ku) cot u`. -/
def cotPolynomial : ℕ → ℝ → ℝ
  | 0, _ => 0
  | k + 1, u => cotPolynomial k u + cos ((2 * (k + 1) : ℕ) * u) + cos ((2 * k : ℕ) * u)

theorem cotPolynomial_continuous (k : ℕ) : Continuous (cotPolynomial k) := by
  induction k with
  | zero => exact continuous_const
  | succ k ih =>
    change Continuous (fun u => cotPolynomial k u + cos ((2 * (k + 1) : ℕ) * u) +
      cos ((2 * k : ℕ) * u))
    fun_prop

theorem cotPolynomial_identity (k : ℕ) (u : ℝ) :
    sin u * cotPolynomial k u = sin ((2 * k : ℕ) * u) * cos u := by
  induction k with
  | zero => simp [cotPolynomial]
  | succ k ih =>
    have hd : (sin ((2 * (k + 1) : ℕ) * u) - sin ((2 * k : ℕ) * u)) * cos u =
        sin u * (cos ((2 * (k + 1) : ℕ) * u) + cos ((2 * k : ℕ) * u)) := by
      rw [sin_sub_sin, cos_add_cos]
      have he : (((2 * (k + 1) : ℕ) : ℝ) * u - (2 * k : ℕ) * u) / 2 = u := by
        push_cast
        ring
      rw [he]
      ring
    rw [cotPolynomial]
    nlinarith

theorem cotPolynomial_eq {u : ℝ} (hu : sin u ≠ 0) (k : ℕ) :
    cotPolynomial k u = sin ((2 * k : ℕ) * u) * (cos u / sin u) := by
  rw [← mul_div_assoc]
  apply (eq_div_iff hu).2
  simpa only [mul_comm] using cotPolynomial_identity k u

theorem even_cos_integrable (k : ℕ) :
    IntervalIntegrable (fun u => cos ((2 * k : ℕ) * u)) volume 0 Real.pi :=
  (show Continuous (fun u : ℝ => cos ((2 * k : ℕ) * u)) by fun_prop).intervalIntegrable _ _

theorem integral_even_cos {k : ℕ} (hk : 0 < k) :
    (∫ u in 0..Real.pi, cos ((2 * k : ℕ) * u)) = 0 := by
  have hkR : ((2 * k : ℕ) : ℝ) ≠ 0 := by positivity
  rw [intervalIntegral.integral_comp_mul_left _ hkR, integral_cos]
  simp only [mul_zero, sin_zero, sub_zero, sin_nat_mul_pi, smul_zero]

theorem integral_cotPolynomial {k : ℕ} (hk : 0 < k) :
    (∫ u in 0..Real.pi, cotPolynomial k u) = Real.pi := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  induction k with
  | zero =>
    simp only [cotPolynomial, Nat.reduceMul, Nat.cast_zero, zero_mul, cos_zero, zero_add]
    norm_num only [Nat.cast_ofNat]
    rw [intervalIntegral.integral_add
        (by simpa using even_cos_integrable 1) intervalIntegrable_const,
      show (∫ u in 0..Real.pi, cos (2 * u)) = 0 from by
        simp]
    simp
  | succ k ih =>
    change (∫ u in 0..Real.pi, cotPolynomial (k + 1) u +
      cos ((2 * (k + 1 + 1) : ℕ) * u) + cos ((2 * (k + 1) : ℕ) * u)) = _
    rw [intervalIntegral.integral_add
        (((cotPolynomial_continuous _).intervalIntegrable _ _).add (even_cos_integrable _))
          (even_cos_integrable _),
      intervalIntegral.integral_add ((cotPolynomial_continuous _).intervalIntegrable _ _)
        (even_cos_integrable _),
      ih (by omega), integral_even_cos (by omega), integral_even_cos (by omega)]
    ring

theorem logSine_hasDerivAt {u : ℝ} (hu : sin u ≠ 0) :
    HasDerivAt logSine (cos u / sin u) u := by
  have h := ((Real.hasDerivAt_sin u).const_mul 2).log (mul_ne_zero (by norm_num) hu)
  convert h using 1
  · rfl
  · field_simp

theorem multiple_sine_log_hasDerivAt (k : ℕ) {u : ℝ} (hu : sin u ≠ 0) :
    HasDerivAt (fun u => sin ((2 * k : ℕ) * u) * logSine u)
      (((2 * k : ℕ) : ℝ) * (cos ((2 * k : ℕ) * u) * logSine u) + cotPolynomial k u) u := by
  have h := (((hasDerivAt_id u).const_mul ((2 * k : ℕ) : ℝ)).sin).mul
    (logSine_hasDerivAt hu)
  dsimp only [id_eq, Pi.mul_apply, mul_one] at h
  convert h using 1 <;> try rfl
  rw [cotPolynomial_eq hu]
  ring

theorem cosine_logSine_integrable (k : ℕ) :
    IntervalIntegrable (fun u => cos ((2 * k : ℕ) * u) * logSine u) volume 0 Real.pi :=
  logSine_integrable.continuousOn_mul (by fun_prop)

theorem integral_even_cos_logSine {k : ℕ} (hk : 0 < k) :
    (∫ u in 0..Real.pi, cos ((2 * k : ℕ) * u) * logSine u) = -Real.pi / (2 * k) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le Real.pi_pos.le
    (multiple_sine_log_continuous (2 * k)).continuousOn
    (fun u hu => multiple_sine_log_hasDerivAt k (sin_pos_of_pos_of_lt_pi hu.1 hu.2).ne')
    (((cosine_logSine_integrable k).const_mul ((2 * k : ℕ) : ℝ)).add
      ((cotPolynomial_continuous k).intervalIntegrable _ _))
  rw [intervalIntegral.integral_add ((cosine_logSine_integrable k).const_mul _)
      ((cotPolynomial_continuous k).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, integral_cotPolynomial hk] at h
  simp only [sin_nat_mul_pi, zero_mul, mul_zero, sin_zero, sub_zero] at h
  push_cast at h
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  apply (eq_div_iff (by positivity : (2 : ℝ) * k ≠ 0)).2
  push_cast
  linarith

end
end StructuralNote.FixedDualClassificationLogFourier
