import Erdos1045.KernelWeights
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.SpecificLimits.Basic

open scoped BigOperators Topology
open Filter

namespace Erdos1045.KernelWeights

noncomputable section

def regularTerm (n q : ℕ) : ℝ :=
  ((n : ℝ) - 1) ^ 2 / (((q : ℝ) + 1) * n - 1) ^ 2

def regularEnergy (n : ℕ) : ℝ := ∑' q, regularTerm n q

theorem regularTerm_nonneg (n q : ℕ) : 0 ≤ regularTerm n q := by
  unfold regularTerm
  positivity

theorem regularTerm_bounds {n : ℕ} (hn : 2 ≤ n) (q : ℕ) :
    (1 - 2 / (n : ℝ)) * (1 / ((q : ℝ) + 1) ^ 2) ≤ regularTerm n q ∧
      regularTerm n q ≤ 1 / ((q : ℝ) + 1) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have hden : 0 < ((q : ℝ) + 1) * n - 1 := by nlinarith
  have hn1 : 0 ≤ (n : ℝ) - 1 := by linarith
  have hupper : ((n : ℝ) - 1) / (((q : ℝ) + 1) * n - 1) ≤ 1 / ((q : ℝ) + 1) := by
    apply (div_le_div_iff₀ hden hq1).mpr
    nlinarith
  have hlower : (((n : ℝ) - 1) / n) / ((q : ℝ) + 1) ≤
      ((n : ℝ) - 1) / (((q : ℝ) + 1) * n - 1) := by
    rw [div_div]
    apply div_le_div_of_nonneg_left hn1 hden
    nlinarith
  have hsupper := (sq_le_sq₀ (div_nonneg hn1 hden.le) (by positivity)).mpr hupper
  have hslower := (sq_le_sq₀ (by positivity) (div_nonneg hn1 hden.le)).mpr hlower
  have hfactor : 1 - 2 / (n : ℝ) ≤ (((n : ℝ) - 1) / n) ^ 2 := by
    field_simp
    nlinarith
  unfold regularTerm
  rw [← div_pow]
  constructor
  · calc
      (1 - 2 / (n : ℝ)) * (1 / ((q : ℝ) + 1) ^ 2) ≤
          (((n : ℝ) - 1) / n) ^ 2 * (1 / ((q : ℝ) + 1) ^ 2) := by
        gcongr
      _ = ((((n : ℝ) - 1) / n) / ((q : ℝ) + 1)) ^ 2 := by simp only [div_pow]; ring
      _ ≤ (((n : ℝ) - 1) / (((q : ℝ) + 1) * n - 1)) ^ 2 := hslower
  · simpa only [div_pow, one_pow] using hsupper

theorem hasSum_reciprocal_square_shift :
    HasSum (fun q : ℕ => 1 / ((q : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
  have h : HasSum (fun q : ℕ => 1 / ((q + 1 : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 6) := by
    apply (hasSum_nat_add_iff (f := fun q : ℕ => (1 : ℝ) / (q : ℝ) ^ 2) 1).mpr
    simpa using hasSum_zeta_two
  simpa using h

theorem summable_regularTerm {n : ℕ} (hn : 2 ≤ n) : Summable (regularTerm n) := by
  apply hasSum_reciprocal_square_shift.summable.of_norm_bounded
  intro q
  rw [Real.norm_eq_abs, abs_of_nonneg (regularTerm_nonneg n q)]
  exact (regularTerm_bounds hn q).2

theorem regularEnergy_bounds {n : ℕ} (hn : 2 ≤ n) :
    (1 - 2 / (n : ℝ)) * (Real.pi ^ 2 / 6) ≤ regularEnergy n ∧
      regularEnergy n ≤ Real.pi ^ 2 / 6 := by
  have hr := summable_regularTerm hn
  have hb := hasSum_reciprocal_square_shift.summable
  constructor
  · have h := (hb.mul_left (1 - 2 / (n : ℝ))).tsum_le_tsum
      (fun q => (regularTerm_bounds hn q).1) hr
    simpa only [tsum_mul_left, hasSum_reciprocal_square_shift.tsum_eq, regularEnergy] using h
  · have h := hr.tsum_le_tsum (fun q => (regularTerm_bounds hn q).2) hb
    simpa only [hasSum_reciprocal_square_shift.tsum_eq, regularEnergy] using h

theorem regularEnergy_error {n : ℕ} (hn : 2 ≤ n) :
    |regularEnergy n - Real.pi ^ 2 / 6| ≤ (2 / (n : ℝ)) * (Real.pi ^ 2 / 6) := by
  have h := regularEnergy_bounds hn
  rw [abs_of_nonpos (sub_nonpos.mpr h.2)]
  nlinarith [h.1]

theorem regularEnergy_tendsto :
    Tendsto regularEnergy atTop (𝓝 (Real.pi ^ 2 / 6)) := by
  have hzero : Tendsto (fun n : ℕ => (2 / (n : ℝ)) * (Real.pi ^ 2 / 6)) atTop (𝓝 0) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).mul_const (Real.pi ^ 2 / 6)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _))
  · filter_upwards [eventually_ge_atTop 2] with n hn
    simpa only [Real.norm_eq_abs] using regularEnergy_error hn
  · exact hzero

/-- Identification of the numerical regular energy with the actual kernel weights
at the frequencies divisible by `n`. The root-of-unity Fourier identity is separate. -/
theorem weight_multiple_eq_regularTerm {n : ℕ} (hn : 2 ≤ n) (q : ℕ) :
    weight n ((q + 1) * n) = regularTerm n q := by
  have hn0 : (n : ℝ) - 1 ≠ 0 := by
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  cases q with
  | zero =>
    simp only [zero_add, one_mul, weight_diagonal hn, regularTerm, Nat.cast_zero, zero_add, one_mul]
    exact (div_self (pow_ne_zero _ hn0)).symm
  | succ q =>
    rw [weight_of_gt hn (by nlinarith)]
    unfold regularTerm
    rw [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 1 ≤ (q + 1 + 1) * n by nlinarith)]
    push_cast
    ring

end

end Erdos1045.KernelWeights
