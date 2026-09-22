import StructuralNote.ExplicitPressureNumerical
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Numerical comparison rules for explicit threshold expressions. -/
namespace StructuralNote.ExplicitNumericalBounds
set_option maxHeartbeats 800000
open Erdos1045.ExplicitThreshold
noncomputable section

theorem majorant_le_pow10 {C : ℝ} {k : ℕ} (hC : |C| ≤ (10 : ℝ) ^ k) :
    majorant C ≤ 10 ^ (k + 1) := by
  have hc : ⌈|C|⌉₊ ≤ 10 ^ k := Nat.ceil_le.mpr (by exact_mod_cast hC)
  have hp : 1 ≤ (10 : ℕ) ^ k := Nat.one_le_pow k 10 (by decide)
  unfold majorant
  rw [pow_succ]
  omega

theorem inverse_le_pow10 {C ε : ℝ} {k : ℕ} (hC : C / ε ≤ (10 : ℝ) ^ k) :
    inverseThreshold C ε ≤ 10 ^ (k + 1) := by
  have hc : ⌈C / ε⌉₊ ≤ 10 ^ k := Nat.ceil_le.mpr (by exact_mod_cast hC)
  have hp : 1 ≤ (10 : ℕ) ^ k := Nat.one_le_pow k 10 (by decide)
  unfold inverseThreshold
  rw [pow_succ]
  omega

theorem inverseSqrt_le_pow10 {C ε : ℝ} {k : ℕ}
    (hC : (C / ε) ^ 2 ≤ (10 : ℝ) ^ k) :
    inverseSqrtThreshold C ε ≤ 10 ^ (k + 1) := by
  have hc : ⌈(C / ε) ^ 2⌉₊ ≤ 10 ^ k := Nat.ceil_le.mpr (by exact_mod_cast hC)
  have hp : 1 ≤ (10 : ℕ) ^ k := Nat.one_le_pow k 10 (by decide)
  unfold inverseSqrtThreshold
  conv_rhs => rw [pow_succ]
  omega

theorem decay_le_pow10 {C ε : ℝ} {a b : ℕ}
    (hC : |C| ≤ (10 : ℝ) ^ a) (hε : |1 / ε| ≤ (10 : ℝ) ^ b) :
    decayThreshold C ε ≤ 10 ^ (8 * (a + b + 23)) := by
  have ha := majorant_le_pow10 hC
  have hb := majorant_le_pow10 hε
  have hnum : (2 : ℕ) * 81 ^ 10 ≤ 10 ^ 21 := by norm_num
  have hprod : 2 * majorant C * 81 ^ 10 * majorant (1 / ε) ≤
      10 ^ (a + b + 23) := by
    calc
      _ = (2 * 81 ^ 10) * majorant C * majorant (1 / ε) := by ring
      _ ≤ 10 ^ 21 * 10 ^ (a + 1) * 10 ^ (b + 1) := by gcongr
      _ = 10 ^ (a + b + 23) := by rw [← pow_add, ← pow_add]; congr 1; omega
  have hp : 2 ≤ (10 : ℕ) ^ (8 * (a + b + 23)) := by
    calc
      2 ≤ 10 ^ 1 := by norm_num
      _ ≤ 10 ^ (8 * (a + b + 23)) := Nat.pow_le_pow_right (by decide) (by omega)
  unfold decayThreshold
  apply max_le hp
  have hh := Nat.pow_le_pow_left hprod 8
  rw [← pow_mul, Nat.mul_comm (a + b + 23) 8] at hh
  exact hh

theorem pow10_le_pow2 (k : ℕ) : (10 : ℕ) ^ k ≤ 2 ^ (4 * k) := by
  calc
    10 ^ k ≤ (2 ^ 4) ^ k := Nat.pow_le_pow_left (by norm_num) k
    _ = _ := by rw [← pow_mul]

theorem exp_le_two_pow {x : ℝ} {k : ℕ} (hx : x ≤ (k : ℝ)) :
    Real.exp x ≤ (2 : ℝ) ^ (2 * k) := by
  calc
    Real.exp x ≤ Real.exp (k : ℝ) := Real.exp_le_exp.mpr hx
    _ = (Real.exp 1) ^ k := by simp [← Real.exp_nat_mul]
    _ ≤ ((2 : ℝ) ^ 2) ^ k := by
      gcongr
      exact Real.exp_one_lt_three.le.trans (by norm_num)
    _ = _ := by rw [← pow_mul]

end
end StructuralNote.ExplicitNumericalBounds
