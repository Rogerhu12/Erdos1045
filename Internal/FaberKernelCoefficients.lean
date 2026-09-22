import Erdos1045.FaberAlgebra
import PositiveRealCoefficients
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! # Identifying the differentiated Faber kernel coefficients

The coefficient of degree k is the normalized Faber polynomial itself, not
that polynomial divided by k. The Laurent correction starts at m=1; b 0 is
ignored, exactly as in the original polynomial recurrence. This file proves
coefficient identities without asserting kernel positivity or map existence.
-/

namespace ExteriorReduction.FaberKernel

open Erdos1045.FaberAlgebra Polynomial
open scoped BigOperators Topology ENNReal
noncomputable section

def value (b : ℕ → ℂ) (x : ℂ) (n : ℕ) : ℂ := (normalizedFaber b n).eval x

@[simp] theorem value_zero (b : ℕ → ℂ) (x : ℂ) : value b x 0 = 1 := by
  simp [value]

theorem value_succ (b : ℕ → ℂ) (x : ℂ) (n : ℕ) :
    value b x (n + 1) = x * value b x n -
      ((∑ j ∈ Finset.range n, b (j + 1) * value b x (n - 1 - j)) + (n : ℂ) * b n) := by
  simp [value, normalizedFaber_succ, Polynomial.eval_finsetSum]

def denominatorCoefficients (b : ℕ → ℂ) (x : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => -x
  | n + 2 => b (n + 1)

def numeratorCoefficients (b : ℕ → ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => 0
  | n + 2 => -((n + 1 : ℕ) : ℂ) * b (n + 1)

def convolution (d a : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1), d j * a (n - j)

@[simp] theorem convolution_zero (d a : ℕ → ℂ) : convolution d a 0 = d 0 * a 0 := by
  simp [convolution]

theorem convolution_succ (b : ℕ → ℂ) (x : ℂ) (a : ℕ → ℂ) (n : ℕ) :
    convolution (denominatorCoefficients b x) a (n + 1) = a (n + 1) - x * a n +
      ∑ j ∈ Finset.range n, b (j + 1) * a (n - 1 - j) := by
  unfold convolution
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [denominatorCoefficients, Nat.sub_zero, Nat.add_sub_add_right]
  have heq : (∑ j ∈ Finset.range n, b (j + 1) * a (n - (j + 1))) =
      ∑ j ∈ Finset.range n, b (j + 1) * a (n - 1 - j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [show n - (j + 1) = n - 1 - j by omega]
  rw [heq]
  ring

theorem numerator_succ (b : ℕ → ℂ) (n : ℕ) :
    numeratorCoefficients b (n + 1) = -(n : ℂ) * b n := by
  cases n <;> simp [numeratorCoefficients]

/-- A multiplication equation with unit constant coefficient determines all
coefficients and recovers the existing Faber recurrence. -/
theorem convolution_identifies_faber (b : ℕ → ℂ) (x : ℂ) (a : ℕ → ℂ)
    (h : ∀ n, convolution (denominatorCoefficients b x) a n = numeratorCoefficients b n) :
    ∀ n, a n = value b x n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa [denominatorCoefficients, numeratorCoefficients] using h 0
    | succ n =>
      have hn := h (n + 1)
      rw [convolution_succ, numerator_succ] at hn
      rw [value_succ]
      have hsum : (∑ j ∈ Finset.range n, b (j + 1) * a (n - 1 - j)) =
          ∑ j ∈ Finset.range n, b (j + 1) * value b x (n - 1 - j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [ih (n - 1 - j) (by omega)]
      rw [ih n (by omega), hsum] at hn
      linear_combination hn

theorem faber_convolution (b : ℕ → ℂ) (x : ℂ) (n : ℕ) :
    convolution (denominatorCoefficients b x) (value b x) n = numeratorCoefficients b n := by
  cases n with
  | zero => simp [denominatorCoefficients, numeratorCoefficients]
  | succ n => rw [convolution_succ, numerator_succ, value_succ]; ring

def denominator (b : ℕ → ℂ) (x : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (denominatorCoefficients b x)

def numerator (b : ℕ → ℂ) : PowerSeries ℂ := PowerSeries.mk (numeratorCoefficients b)

def faberSeries (b : ℕ → ℂ) (x : ℂ) : PowerSeries ℂ := PowerSeries.mk (value b x)

theorem coeff_product (d a : ℕ → ℂ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk d * PowerSeries.mk a) = convolution d a n := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_mk, convolution]

/-- Exact identity in formal power series, with no convergence assumption. -/
theorem denominator_mul_faberSeries (b : ℕ → ℂ) (x : ℂ) :
    denominator b x * faberSeries b x = numerator b := by
  ext n
  change PowerSeries.coeff n (PowerSeries.mk _ * PowerSeries.mk _) = _
  rw [coeff_product]
  simpa [numerator] using faber_convolution b x n

/-- Any formal quotient kernel satisfying the actual multiplication identity
has the Faber polynomial values as coefficients. -/
theorem formal_kernel_coefficient (b : ℕ → ℂ) (x : ℂ) (A : PowerSeries ℂ)
    (h : denominator b x * A = numerator b) (n : ℕ) :
    PowerSeries.coeff n A = value b x n := by
  apply convolution_identifies_faber b x (fun n => PowerSeries.coeff n A) _ n
  intro k
  have hk := congrArg (PowerSeries.coeff k) h
  have heq : PowerSeries.mk (fun n => PowerSeries.coeff n A) = A := by ext n; simp
  rw [← heq] at hk
  simpa only [denominator, numerator, coeff_product, PowerSeries.coeff_mk] using hk

/-- Multiplication of actual convergent scalar power series gives the finite
Cauchy convolution. This is a local analytic statement, not an assumed
coefficient identity for the desired kernel. -/
theorem scalar_series_product {f g : ℂ → ℂ} {a d : ℕ → ℂ}
    (hf : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ a) 0)
    (hg : HasFPowerSeriesAt g (FormalMultilinearSeries.ofScalars ℂ d) 0) :
    HasFPowerSeriesAt (fun z => f z * g z)
      (FormalMultilinearSeries.ofScalars ℂ (convolution a d)) 0 := by
  rw [hasFPowerSeriesAt_iff]
  obtain ⟨r, hf⟩ := hf
  obtain ⟨s, hg⟩ := hg
  filter_upwards [Metric.eball_mem_nhds (0 : ℂ) hf.r_pos,
    Metric.eball_mem_nhds (0 : ℂ) hg.r_pos] with z hzr hzs
  have hfa : HasSum (fun n => a n * z ^ n) (f z) := by
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] using hf.hasSum hzr
  have hgd : HasSum (fun n => d n * z ^ n) (g z) := by
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] using hg.hasSum hzs
  have hna : Summable (fun n => ‖a n * z ^ n‖) := by
    have h := (FormalMultilinearSeries.ofScalars ℂ a).summable_norm_apply
      (x := z) (lt_of_lt_of_le hzr hf.r_le)
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using h
  have hnd : Summable (fun n => ‖d n * z ^ n‖) := by
    have h := (FormalMultilinearSeries.ofScalars ℂ d).summable_norm_apply
      (x := z) (lt_of_lt_of_le hzs hg.r_le)
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using h
  have hp := hasSum_sum_range_mul_of_summable_norm hna hnd
  rw [hfa.tsum_eq, hgd.tsum_eq] at hp
  have hc (n : ℕ) :
      (∑ j ∈ Finset.range (n + 1), (a j * z ^ j) * (d (n - j) * z ^ (n - j))) =
        z ^ n * convolution a d n := by
    unfold convolution
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    calc
      (a j * z ^ j) * (d (n - j) * z ^ (n - j)) =
          (a j * d (n - j)) * (z ^ j * z ^ (n - j)) := by ring
      _ = _ := by rw [← pow_add, Nat.add_sub_of_le hjn]; ring
  simpa only [hc, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, zero_add] using hp

/-- A genuine local analytic equation D*H=N identifies the Taylor coefficients
with Faber values. The denominator and numerator series are explicit. -/
theorem analytic_kernel_coefficient {D H N : ℂ → ℂ} (b : ℕ → ℂ) (x : ℂ)
    {a : ℕ → ℂ}
    (hD : HasFPowerSeriesAt D (FormalMultilinearSeries.ofScalars ℂ (denominatorCoefficients b x)) 0)
    (hH : HasFPowerSeriesAt H (FormalMultilinearSeries.ofScalars ℂ a) 0)
    (hN : HasFPowerSeriesAt N (FormalMultilinearSeries.ofScalars ℂ (numeratorCoefficients b)) 0)
    (heq : ∀ᶠ z in nhds (0 : ℂ), D z * H z = N z) (k : ℕ) : a k = value b x k := by
  have hs := (scalar_series_product hD hH).eq_formalMultilinearSeries_of_eventually hN heq
  apply convolution_identifies_faber b x a _ k
  intro n
  have hn := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) hs
  simpa only [FormalMultilinearSeries.coeff_ofScalars] using hn

theorem analytic_kernel_zero {D H N : ℂ → ℂ} (b : ℕ → ℂ) (x : ℂ) {a : ℕ → ℂ}
    (hD : HasFPowerSeriesAt D (FormalMultilinearSeries.ofScalars ℂ (denominatorCoefficients b x)) 0)
    (hH : HasFPowerSeriesAt H (FormalMultilinearSeries.ofScalars ℂ a) 0)
    (hN : HasFPowerSeriesAt N (FormalMultilinearSeries.ofScalars ℂ (numeratorCoefficients b)) 0)
    (heq : ∀ᶠ z in nhds (0 : ℂ), D z * H z = N z) : H 0 = 1 := by
  have hz : a 0 = H 0 := by
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, one_pow, smul_eq_mul, mul_one] using
      hH.coeff_zero (fun _ => 1)
  rw [← hz, analytic_kernel_coefficient b x hD hH hN heq 0, value_zero]

/-- After the analytic kernel and positivity have independently been verified,
the generic positive-real-part theorem bounds the actual Faber polynomials. -/
theorem faber_bound_of_positive_kernel {D H N : ℂ → ℂ} (b : ℕ → ℂ) (x : ℂ)
    {a : ℕ → ℂ} {R : ℝ≥0∞}
    (hD : HasFPowerSeriesAt D (FormalMultilinearSeries.ofScalars ℂ (denominatorCoefficients b x)) 0)
    (hH : HasFPowerSeriesOnBall H (FormalMultilinearSeries.ofScalars ℂ a) 0 R)
    (hN : HasFPowerSeriesAt N (FormalMultilinearSeries.ofScalars ℂ (numeratorCoefficients b)) 0)
    (heq : ∀ᶠ z in nhds (0 : ℂ), D z * H z = N z)
    (hhol : DifferentiableOn ℂ H (Metric.ball 0 1))
    (hpos : ∀ z ∈ Metric.ball (0 : ℂ) 1, 0 ≤ (H z).re)
    (k : ℕ) (hk : k ≠ 0) : ‖value b x k‖ ≤ 2 := by
  rw [← analytic_kernel_coefficient b x hD hH.hasFPowerSeriesAt hN heq k]
  exact PositiveReal.normalized_scalar_coefficient_bound hH hhol
    (analytic_kernel_zero b x hD hH.hasFPowerSeriesAt hN heq) hpos k hk

/-- No power-series witness for H is needed at the public interface: ordinary
holomorphicity produces it. Positivity remains an explicit property to prove
for the actual geometric kernel. -/
theorem faber_bound_of_positive_analytic_kernel {D H N : ℂ → ℂ}
    (b : ℕ → ℂ) (x : ℂ)
    (hD : HasFPowerSeriesAt D (FormalMultilinearSeries.ofScalars ℂ (denominatorCoefficients b x)) 0)
    (hN : HasFPowerSeriesAt N (FormalMultilinearSeries.ofScalars ℂ (numeratorCoefficients b)) 0)
    (heq : ∀ᶠ z in nhds (0 : ℂ), D z * H z = N z)
    (hhol : DifferentiableOn ℂ H (Metric.ball 0 1))
    (hpos : ∀ z ∈ Metric.ball (0 : ℂ) 1, 0 ≤ (H z).re)
    (k : ℕ) (hk : k ≠ 0) : ‖value b x k‖ ≤ 2 := by
  obtain ⟨p, hp⟩ := (hhol.analyticOnNhd Metric.isOpen_ball) 0 (by simp)
  have hscalar : HasFPowerSeriesAt H (FormalMultilinearSeries.ofScalars ℂ p.coeff) 0 := by
    rw [hasFPowerSeriesAt_iff] at hp ⊢
    simpa only [FormalMultilinearSeries.coeff_ofScalars] using hp
  obtain ⟨R, hR⟩ := hscalar
  exact faber_bound_of_positive_kernel b x hD hR hN heq hhol hpos k hk

/-- The ratio form used by the differentiated Faber generating kernel. -/
theorem faber_bound_of_positive_quotient {D N : ℂ → ℂ} (b : ℕ → ℂ) (x : ℂ)
    (hD : HasFPowerSeriesAt D (FormalMultilinearSeries.ofScalars ℂ (denominatorCoefficients b x)) 0)
    (hN : HasFPowerSeriesAt N (FormalMultilinearSeries.ofScalars ℂ (numeratorCoefficients b)) 0)
    (hhol : DifferentiableOn ℂ (fun z => N z / D z) (Metric.ball 0 1))
    (hpos : ∀ z ∈ Metric.ball (0 : ℂ) 1, 0 ≤ (N z / D z).re)
    (k : ℕ) (hk : k ≠ 0) : ‖value b x k‖ ≤ 2 := by
  have hzero : D 0 = 1 := by
    have h := hD.coeff_zero (fun _ => 1)
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, denominatorCoefficients] using h.symm
  have hne : D 0 ≠ 0 := by rw [hzero]; exact one_ne_zero
  have heq : ∀ᶠ z in nhds (0 : ℂ), D z * (N z / D z) = N z := by
    filter_upwards [hD.continuousAt.eventually_ne hne] with z hz
    field_simp
  exact faber_bound_of_positive_analytic_kernel b x hD hN heq hhol hpos k hk

end
end ExteriorReduction.FaberKernel
