import StructuralNote.FixedDualIntervalsMidpoint
import Mathlib.Analysis.Calculus.Taylor

/-! Explicit finite Taylor bounds for actual sine, cosine, and logarithm. -/

namespace StructuralNote.FixedDualTaylorBounds

open Real
open scoped BigOperators
noncomputable section

def sineCoefficient (k : ℕ) : ℝ := if k % 2 = 0 then 0 else (-1) ^ (k / 2)
def cosineCoefficient (k : ℕ) : ℝ := if k % 2 = 0 then (-1) ^ (k / 2) else 0

theorem iterated_sine_zero (k : ℕ) : iteratedDeriv k sin 0 = sineCoefficient k := by
  have hm : k % 2 < 2 := Nat.mod_lt k (by norm_num)
  by_cases he : k % 2 = 0
  · have hk : k = 2 * (k / 2) := by omega
    conv_lhs => rw [hk, iteratedDeriv_even_sin]
    simp [sineCoefficient, he]
  · have hk : k = 2 * (k / 2) + 1 := by omega
    conv_lhs => rw [hk, iteratedDeriv_odd_sin]
    simp [sineCoefficient, he]

theorem iterated_cosine_zero (k : ℕ) : iteratedDeriv k cos 0 = cosineCoefficient k := by
  have hm : k % 2 < 2 := Nat.mod_lt k (by norm_num)
  by_cases he : k % 2 = 0
  · have hk : k = 2 * (k / 2) := by omega
    conv_lhs => rw [hk, iteratedDeriv_even_cos]
    simp [cosineCoefficient, he]
  · have hk : k = 2 * (k / 2) + 1 := by omega
    conv_lhs => rw [hk, iteratedDeriv_odd_cos]
    simp [cosineCoefficient, he]

def sinePolynomial (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), sineCoefficient k * x ^ k / (k.factorial : ℝ)

def cosinePolynomial (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), cosineCoefficient k * x ^ k / (k.factorial : ℝ)

theorem taylor_sine_eq {x : ℝ} (hx : 0 < x) (n : ℕ) :
    taylorWithinEval sin n (Set.Icc 0 x) 0 x = sinePolynomial n x := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [iteratedDerivWithin_sin_Icc k hx ⟨le_rfl, hx.le⟩, iterated_sine_zero]
  simp only [sub_zero, smul_eq_mul]
  ring

theorem taylor_cosine_eq {x : ℝ} (hx : 0 < x) (n : ℕ) :
    taylorWithinEval cos n (Set.Icc 0 x) 0 x = cosinePolynomial n x := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [iteratedDerivWithin_cos_Icc k hx ⟨le_rfl, hx.le⟩, iterated_cosine_zero]
  simp only [sub_zero, smul_eq_mul]
  ring

theorem sine_taylor_bound {x : ℝ} (hx : 0 < x) (n : ℕ) :
    |sin x - sinePolynomial n x| ≤ x ^ (n + 1) / (n.factorial : ℝ) := by
  have h := taylor_mean_remainder_bound (f := sin) (a := 0) (b := x) (C := 1)
    (x := x) (n := n) hx.le contDiff_sin.contDiffOn ⟨hx.le, le_rfl⟩
    (fun y hy => by
      rw [iteratedDerivWithin_sin_Icc (n + 1) hx hy, Real.norm_eq_abs]
      exact abs_iteratedDeriv_sin_le_one _ _)
  simpa only [Real.norm_eq_abs, taylor_sine_eq hx, sub_zero, one_mul] using h

theorem cosine_taylor_bound {x : ℝ} (hx : 0 < x) (n : ℕ) :
    |cos x - cosinePolynomial n x| ≤ x ^ (n + 1) / (n.factorial : ℝ) := by
  have h := taylor_mean_remainder_bound (f := cos) (a := 0) (b := x) (C := 1)
    (x := x) (n := n) hx.le contDiff_cos.contDiffOn ⟨hx.le, le_rfl⟩
    (fun y hy => by
      rw [iteratedDerivWithin_cos_Icc (n + 1) hx hy, Real.norm_eq_abs]
      exact abs_iteratedDeriv_cos_le_one _ _)
  simpa only [Real.norm_eq_abs, taylor_cosine_eq hx, sub_zero, one_mul] using h

theorem sine_interval {x l u : ℝ} (hx : 0 < x) (n : ℕ)
    (hl : l ≤ sinePolynomial n x - x ^ (n + 1) / (n.factorial : ℝ))
    (hu : sinePolynomial n x + x ^ (n + 1) / (n.factorial : ℝ) ≤ u) :
    l ≤ sin x ∧ sin x ≤ u := by
  have h := abs_le.mp (sine_taylor_bound hx n)
  constructor <;> linarith [h.1, h.2]

theorem cosine_interval {x l u : ℝ} (hx : 0 < x) (n : ℕ)
    (hl : l ≤ cosinePolynomial n x - x ^ (n + 1) / (n.factorial : ℝ))
    (hu : cosinePolynomial n x + x ^ (n + 1) / (n.factorial : ℝ) ≤ u) :
    l ≤ cos x ∧ cos x ≤ u := by
  have h := abs_le.mp (cosine_taylor_bound hx n)
  constructor <;> linarith [h.1, h.2]

def logCoordinate (x : ℝ) : ℝ := (x - 1) / (x + 1)

def logPolynomial (n : ℕ) (x : ℝ) : ℝ :=
  2 * ∑ k ∈ Finset.range n, logCoordinate x ^ (2 * k + 1) / (2 * k + 1)

def logError (n : ℕ) (x : ℝ) : ℝ :=
  2 * |logCoordinate x| ^ (2 * n + 1) / (1 - logCoordinate x ^ 2)

theorem log_coordinate_bounds {x : ℝ} (hx : 0 < x) :
    |logCoordinate x| < 1 ∧ 0 < 1 - logCoordinate x ^ 2 := by
  have hd : 0 < x + 1 := by linarith
  have hz : |logCoordinate x| < 1 := by
    rw [abs_lt, logCoordinate]
    constructor
    · apply (lt_div_iff₀ hd).2
      linarith
    · apply (div_lt_iff₀ hd).2
      linarith
  exact ⟨hz, by nlinarith [(abs_lt.mp hz).1, (abs_lt.mp hz).2]⟩

theorem logarithm_taylor_bound {x : ℝ} (hx : 0 < x) (n : ℕ) :
    |log x - logPolynomial n x| ≤ logError n x := by
  have hz := (log_coordinate_bounds hx).1
  have he : (1 + logCoordinate x) / (1 - logCoordinate x) = x := by
    unfold logCoordinate
    field_simp
    ring
  have h := sum_range_sub_log_div_le hz n
  rw [he] at h
  have h2 := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)
  unfold logPolynomial logError
  rw [← abs_of_pos (by norm_num : (0 : ℝ) < 2), ← abs_mul] at h2
  convert h2 using 1 <;> try rfl
  · congr 1
    ring
  · ring

theorem logarithm_interval {x l u : ℝ} (hx : 0 < x) (n : ℕ)
    (hl : l ≤ logPolynomial n x - logError n x)
    (hu : logPolynomial n x + logError n x ≤ u) :
    l ≤ log x ∧ log x ≤ u := by
  have h := abs_le.mp (logarithm_taylor_bound hx n)
  constructor <;> linarith [h.1, h.2]

end
end StructuralNote.FixedDualTaylorBounds
