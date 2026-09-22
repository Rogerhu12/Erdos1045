import StructuralNote.HessianComparison
import StructuralNote.CommonDomainRadius

/-! All explicit geometric Hessian error coefficients vanish on the literal
logarithmic common domain. -/

namespace StructuralNote.HessianErrorLimits

open Filter Real CommonDomainRadius HessianComparison
open scoped Topology
noncomputable section

def chordError (n : ℕ) : ℝ := 300 * (logOrder n : ℝ) / n
def phaseError (n : ℕ) : ℝ := 4 * (logOrder n : ℝ) / n
def gradientBound (n : ℕ) : ℝ := 600 * (logOrder n : ℝ) * (1 + Real.log n)
def accelerationBound (n : ℕ) : ℝ := 1000000000 * (1 / n + 1 / Real.sqrt n)

theorem logOrder_div_tendsto :
    Tendsto (fun n : ℕ => (logOrder n : ℝ) / n) atTop (𝓝 0) := by
  have ht := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    tendsto_natCast_atTop_atTop).const_mul 4
  simp only [Function.comp_def, id_eq, mul_zero] at ht
  apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) _ ht
  filter_upwards [eventually_ge_atTop 2] with n hn
  simpa only [mul_div_assoc] using
    div_le_div_of_nonneg_right (logOrder_le hn) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)

theorem logOrder_log_div_power_tendsto {p : ℝ} (hp : 0 < p) :
    Tendsto (fun n : ℕ => (logOrder n : ℝ) * (1 + Real.log n) / (n : ℝ) ^ p)
      atTop (𝓝 0) := by
  have ht := (((isLittleO_log_rpow_rpow_atTop (2 : ℝ) hp).tendsto_div_nhds_zero).comp
    tendsto_natCast_atTop_atTop).const_mul 8
  simp only [Function.comp_def, Real.rpow_two, mul_zero] at ht
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  apply squeeze_zero' ?_ ?_ ht
  · filter_upwards [hlog] with n hn
    change 1 ≤ Real.log n at hn
    positivity
  · filter_upwards [hlog, eventually_ge_atTop 2] with n hl hn
    change 1 ≤ Real.log n at hl
    have hL := logOrder_le hn
    have hm := mul_le_mul_of_nonneg_right hL (show 0 ≤ 1 + Real.log n by linarith)
    have hnum : (logOrder n : ℝ) * (1 + Real.log n) ≤ 8 * Real.log n ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ Real.log n - 1 by linarith)
        (show 0 ≤ Real.log n by linarith)]
    simpa only [mul_div_assoc] using
      div_le_div_of_nonneg_right hnum (Real.rpow_nonneg (Nat.cast_nonneg n) p)

theorem chordError_tendsto : Tendsto chordError atTop (𝓝 0) := by
  change Tendsto (fun n => 300 * (logOrder n : ℝ) / n) atTop (𝓝 0)
  simpa only [mul_div_assoc, mul_zero] using logOrder_div_tendsto.const_mul 300

theorem phaseError_tendsto : Tendsto phaseError atTop (𝓝 0) := by
  change Tendsto (fun n => 4 * (logOrder n : ℝ) / n) atTop (𝓝 0)
  simpa only [mul_div_assoc, mul_zero] using logOrder_div_tendsto.const_mul 4

theorem gradient_div_tendsto :
    Tendsto (fun n => gradientBound n / (n : ℝ)) atTop (𝓝 0) := by
  simpa only [gradientBound, mul_div_assoc, mul_assoc, Real.rpow_one, mul_zero] using
    (logOrder_log_div_power_tendsto (p := 1) (by norm_num)).const_mul 600

theorem gradient_acceleration_tendsto :
    Tendsto (fun n => gradientBound n * accelerationBound n) atTop (𝓝 0) := by
  have h1 := logOrder_log_div_power_tendsto (p := 1) (by norm_num)
  have h2 := logOrder_log_div_power_tendsto (p := 1 / 2) (by norm_num)
  simp only [Real.rpow_one] at h1
  simp only [← Real.sqrt_eq_rpow] at h2
  convert (h1.add h2).const_mul 600000000000 using 1
  · funext n
    dsimp [gradientBound, accelerationBound]
    ring
  · norm_num

theorem errorCoefficient_tendsto (ε : ℝ) :
    Tendsto (fun n => errorCoefficient n (chordError n) ε
      (gradientBound n) (accelerationBound n) (phaseError n)) atTop (𝓝 (16 * ε + 2 * ε ^ 2)) := by
  have hq := (chordError_tendsto.const_mul 20).mul_const (24 + 2 * ε ^ 2)
  have ha := gradient_div_tendsto.add (phaseError_tendsto.const_mul 2)
  have h := (((hq.add_const (16 * ε)).add_const (2 * ε ^ 2)).add
    gradient_acceleration_tendsto).add (ha.const_mul 4)
  simpa only [errorCoefficient, mul_zero, zero_mul, zero_add, add_zero] using h

theorem eventual_error_small : ∀ᶠ n : ℕ in atTop,
    chordError n ≤ 1 / 2 ∧ errorCoefficient n (chordError n) (1 / 10000)
      (gradientBound n) (accelerationBound n) (phaseError n) ≤ 1 / 64 := by
  have hc := chordError_tendsto.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  have he := (errorCoefficient_tendsto (1 / 10000)).eventually
    (gt_mem_nhds (show (16 : ℝ) * (1 / 10000) + 2 * (1 / 10000) ^ 2 < 1 / 64 by norm_num))
  filter_upwards [hc, he] with n hn he
  exact ⟨hn.le, he.le⟩

theorem acceleration_bound {n A E : ℝ} (hA : 0 ≤ A) (hE : 0 ≤ E) :
    1000000000 * ((A + E) / n + Real.sqrt (A * E) / Real.sqrt n) ≤
      1000000000 * (1 / n + 1 / Real.sqrt n) * (E + A) := by
  have hs : Real.sqrt (A * E) ≤ A + E := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨add_nonneg hA hE, by nlinarith [sq_nonneg (A - E)]⟩
  have hd := div_le_div_of_nonneg_right hs (Real.sqrt_nonneg n)
  simp only [div_eq_mul_inv] at hd ⊢
  nlinarith only [hd]

end
end StructuralNote.HessianErrorLimits
