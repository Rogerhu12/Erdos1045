import StructuralNote.RewrittenSeriesIntegral
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! The convergent difference series is the elementary rational integral.
Finite geometric sums give a quantitative remainder, including the endpoint 1. -/

namespace StructuralNote.RewrittenDifferenceSeries

open Real Set Filter MeasureTheory RewrittenSeriesIntegral
open scoped BigOperators Topology Interval
noncomputable section

def differenceTerm (j : ℕ) : ℝ :=
  1 / (2 * (j : ℝ) + 1) - 1 / (2 * (j : ℝ) + 1 + 1 / 3)

def summand (j : ℕ) (y : ℝ) : ℝ := 3 * (y ^ (6 * j + 2) - y ^ (6 * j + 3))

theorem differenceTerm_nonneg (j : ℕ) : 0 ≤ differenceTerm j := by
  apply sub_nonneg.mpr
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

theorem density_geometric {y : ℝ} (hy : 0 ≤ y) :
    density y * (1 - y ^ 6) = 3 * y ^ 2 * (1 - y) := by
  unfold density
  have hd := (denominator_pos hy).ne'
  have hm' : 1 - y + y ^ 2 ≠ 0 := by nlinarith [quadratic_minus_pos y]
  field_simp
  ring_nf
  field_simp [hm']
  ring

theorem finite_geometric_sum {y : ℝ} (hy : 0 ≤ y) (P : ℕ) :
    ∑ j ∈ Finset.range P, summand j y = density y * (1 - y ^ (6 * P)) := by
  induction P with
  | zero => simp
  | succ P ih =>
    rw [Finset.sum_range_succ, ih]
    have h := congrArg (fun x : ℝ => y ^ (6 * P) * x) (density_geometric hy)
    rw [show 6 * (P + 1) = 6 * P + 6 by omega, pow_add]
    simp only [summand, pow_add] at *
    nlinarith [h]

theorem summand_integrable (j : ℕ) : IntervalIntegrable (summand j) volume 0 1 :=
  (by unfold summand; fun_prop : Continuous (summand j)).intervalIntegrable _ _

theorem integral_summand (j : ℕ) :
    (∫ y in (0 : ℝ)..1, summand j y) = differenceTerm j := by
  unfold summand
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub ((continuous_pow _).intervalIntegrable _ _)
      ((continuous_pow _).intervalIntegrable _ _),
    integral_pow, integral_pow]
  simp only [one_pow, zero_pow (by omega : 6 * j + 2 + 1 ≠ 0),
    zero_pow (by omega : 6 * j + 3 + 1 ≠ 0), sub_zero]
  unfold differenceTerm
  push_cast
  field_simp
  ring

theorem tail_integrable (P : ℕ) :
    IntervalIntegrable (fun y => density y * y ^ (6 * P)) volume 0 1 :=
  (density_continuousOn.mul (by fun_prop)).intervalIntegrable_of_Icc (by norm_num)

theorem finite_sum_integral (P : ℕ) :
    ∑ j ∈ Finset.range P, differenceTerm j =
      (∫ y in (0 : ℝ)..1, density y) - ∫ y in (0 : ℝ)..1, density y * y ^ (6 * P) := by
  simp_rw [← integral_summand]
  rw [← intervalIntegral.integral_finsetSum (fun j _ => summand_integrable j),
    ← intervalIntegral.integral_sub density_integrable (tail_integrable P)]
  apply intervalIntegral.integral_congr
  intro y hy
  dsimp only
  rw [finite_geometric_sum (by simpa using hy.1)]
  ring

theorem integral_tail_bound (P : ℕ) :
    0 ≤ (∫ y in (0 : ℝ)..1, density y * y ^ (6 * P)) ∧
      (∫ y in (0 : ℝ)..1, density y * y ^ (6 * P)) ≤ 3 / (6 * (P : ℝ) + 1) := by
  refine ⟨intervalIntegral.integral_nonneg (by norm_num) (fun y hy =>
    mul_nonneg (density_nonneg hy.1) (pow_nonneg hy.1 _)), ?_⟩
  have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    (tail_integrable P) ((by fun_prop : Continuous (fun y : ℝ => 3 * y ^ (6 * P))).intervalIntegrable _ _)
    (fun y hy => mul_le_mul_of_nonneg_right (density_le_three hy) (pow_nonneg hy.1 _))
  apply h.trans_eq
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp only [one_pow, zero_pow (by omega : 6 * P + 1 ≠ 0), sub_zero,
    Nat.cast_mul, Nat.cast_ofNat, mul_one_div]

theorem difference_partial_tendsto :
    Tendsto (fun P => ∑ j ∈ Finset.range P, differenceTerm j) atTop
      (𝓝 (∫ y in (0 : ℝ)..1, density y)) := by
  have ht : Tendsto (fun P : ℕ => 3 / (6 * (P : ℝ) + 1)) atTop (𝓝 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (3 : ℝ)).comp
      (tendsto_atTop_mono (fun P => by omega : ∀ P : ℕ, P ≤ 6 * P + 1) tendsto_id)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_one] using h
  have htail := squeeze_zero (fun P => (integral_tail_bound P).1)
    (fun P => (integral_tail_bound P).2) ht
  have h := (tendsto_const_nhds (x := ∫ y in (0 : ℝ)..1, density y)).sub htail
  simpa only [sub_zero, ← finite_sum_integral] using h

theorem differenceTerm_summable : Summable differenceTerm := by
  apply summable_of_sum_range_le differenceTerm_nonneg
  intro P
  rw [finite_sum_integral]
  exact sub_le_self _ (integral_tail_bound P).1

theorem difference_series_eq :
    ∑' j, differenceTerm j = Real.log 2 - (3 / 4) * Real.log 3 +
      Real.pi / (4 * Real.sqrt 3) := by
  rw [← integral_density]
  exact tendsto_nhds_unique differenceTerm_summable.hasSum.tendsto_sum_nat
    difference_partial_tendsto

end
end StructuralNote.RewrittenDifferenceSeries
