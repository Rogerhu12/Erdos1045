import StructuralNote.FixedDualClassificationKernelUniformConvergence
import EventualExact.SchurWeightLimit

/-! Explicit rates for the finite Schur kernel. All cutoffs are arithmetic
expressions in the requested tolerance and the distance from the singular set. -/

namespace StructuralNote.ExplicitKernelRate

open Real Finset Erdos1045.EventualExact
open FixedDualClassificationKernel FixedDualClassificationKernelUniformFold
open FixedDualClassificationKernelUniformSeries FixedDualClassificationKernelUniformConvergence
open FixedDualClassificationOddSpectrum
open scoped BigOperators
noncomputable section

/-- A deliberately coarse sinc estimate, sufficient for an explicit kernel rate. -/
theorem sinc_interval {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    1 - x ≤ sinc x ∧ sinc x ≤ 1 := by
  refine ⟨?_, sinc_le_one x⟩
  rcases hx.eq_or_lt with rfl | hx
  · simp
  rw [sinc_of_ne_zero hx.ne', le_div_iff₀ hx]
  have hcube : x ^ 3 / 6 ≤ x ^ 2 := by
    have := mul_le_mul_of_nonneg_left hxhalf (sq_nonneg x)
    nlinarith [sq_nonneg x]
  nlinarith [sin_ge_sub_cube hx.le]

/-- Stability of the quotient in the sinc formula for an active weight. -/
theorem sinc_quotient_error {q a b c x y z : ℝ}
    (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (ha : 1 - x ≤ a) (ha1 : a ≤ 1) (ha0 : 0 ≤ a)
    (hb : 1 - y ≤ b) (hb1 : b ≤ 1) (hbh : 1 / 2 ≤ b)
    (hc : 1 - z ≤ c) (hc1 : c ≤ 1) (hch : 1 / 2 ≤ c)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    |(1 - q) * a ^ 2 / (b * c) - 1| ≤ 4 * (q + 2 * x + y + z) := by
  have hb0 : 0 ≤ b := by linarith
  have hc0 : 0 ≤ c := by linarith
  have ha2 : a ^ 2 ≤ 1 := by nlinarith
  have hbc : 1 / 4 ≤ b * c := by nlinarith
  have hbc1 : b * c ≤ 1 := by nlinarith
  have hapos : 0 ≤ (1 - q) * a ^ 2 := mul_nonneg (by linarith) (sq_nonneg a)
  have haone : (1 - q) * a ^ 2 ≤ 1 := by
    have := mul_le_mul_of_nonneg_right (show 1 - q ≤ 1 by linarith) (sq_nonneg a)
    nlinarith
  have hqa : q * a ^ 2 ≤ q := by nlinarith [mul_nonneg hq (show 0 ≤ 1 - a ^ 2 by linarith)]
  have haa : 1 - a ^ 2 ≤ 2 * x := by nlinarith [sq_nonneg (1 - a)]
  have hbca : 1 - b * c ≤ y + z := by
    have := mul_nonneg (show 0 ≤ 1 - b by linarith) (show 0 ≤ 1 - c by linarith)
    nlinarith
  have hnum : |(1 - q) * a ^ 2 - b * c| ≤ q + 2 * x + y + z := by
    apply abs_le.mpr
    constructor <;> nlinarith
  have hden : 0 < b * c := by linarith
  rw [show (1 - q) * a ^ 2 / (b * c) - 1 =
      ((1 - q) * a ^ 2 - b * c) / (b * c) by field_simp,
    abs_div, abs_of_pos hden, div_le_iff₀ hden]
  have he : 0 ≤ q + 2 * x + y + z := by positivity
  have := mul_le_mul_of_nonneg_left hbc (show 0 ≤ 4 * (q + 2 * x + y + z) by positivity)
  nlinarith

/-- An explicit, uniform-in-frequency error on the lower spectral block. -/
theorem weight_error_le {n p : ℕ} (hpodd : Odd p) (hp3 : 3 ≤ p)
    (hsize : 8 * (p + 1) ≤ n) :
    |SchurWeights.weight n p - 1 / ((p : ℝ) + 1)| ≤ 36 / n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hs : 8 * ((p : ℝ) + 1) ≤ n := by exact_mod_cast hsize
  have hp1 : 0 < (p : ℝ) + 1 := by positivity
  let q : ℝ := ((p : ℝ) + 1) / n
  let x : ℝ := Real.pi / n
  let y : ℝ := ((p : ℝ) - 1) * Real.pi / n
  let z : ℝ := ((p : ℝ) + 1) * Real.pi / n
  have hq : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := by dsimp [q]; apply (div_le_iff₀ hn).2; nlinarith
  have hx : 0 ≤ x := by positivity
  have hy : 0 ≤ y := by
    dsimp [y]
    exact div_nonneg (mul_nonneg (by linarith) Real.pi_pos.le) hn.le
  have hz : 0 ≤ z := by positivity
  have hzh : z ≤ 1 / 2 := by
    dsimp [z]
    apply (div_le_iff₀ hn).2
    nlinarith [Real.pi_lt_four]
  have hxy : x ≤ z := by
    dsimp [x, z]
    exact div_le_div_of_nonneg_right (by nlinarith [Real.pi_pos]) hn.le
  have hyz : y ≤ z := by
    dsimp [y, z]
    exact div_le_div_of_nonneg_right (by nlinarith [Real.pi_pos]) hn.le
  have ha := sinc_interval hx (hxy.trans hzh)
  have hb := sinc_interval hy (hyz.trans hzh)
  have hc := sinc_interval hz hzh
  have he := sinc_quotient_error hq hq1 ha.1 ha.2 (by linarith)
    hb.1 hb.2 (by linarith) hc.1 hc.2 (by linarith) hx hy hz
  have hactive : SchurWeights.Active n p := ⟨hpodd, hp3, by omega⟩
  rw [SchurWeights.weight_eq_sinc hactive]
  have hid : (1 - ((p : ℝ) + 1) / n) / ((p : ℝ) + 1) * sinc (Real.pi / n) ^ 2 /
      (sinc (((p : ℝ) - 1) * Real.pi / n) * sinc (((p : ℝ) + 1) * Real.pi / n)) -
        1 / ((p : ℝ) + 1) =
      ((1 - q) * sinc x ^ 2 / (sinc y * sinc z) - 1) / ((p : ℝ) + 1) := by
    dsimp [q, x, y, z]
    ring
  rw [hid, abs_div, abs_of_pos hp1]
  calc
    _ ≤ (4 * (q + 2 * x + y + z)) / ((p : ℝ) + 1) :=
      div_le_div_of_nonneg_right he hp1.le
    _ = (4 + 8 * Real.pi) / n := by
      dsimp [q, x, y, z]
      field_simp
      ring
    _ ≤ 36 / n := div_le_div_of_nonneg_right (by nlinarith [Real.pi_lt_four]) hn.le

/-- The inactive first frequency also satisfies the same head error bound. -/
theorem odd_weight_error_le {n P k : ℕ} (hk : k < P) (hsize : 16 * (P + 1) ≤ n) :
    |SchurWeights.weight n (2 * k + 1) - 2 * kernelCoefficient (k : ℤ)| ≤ 36 / n := by
  by_cases hk0 : k = 0
  · subst k
    have hw : SchurWeights.weight n 1 = 0 :=
      SchurWeights.weight_eq_zero (by simp [SchurWeights.Active])
    simp [hw, kernelCoefficient, naturalKernelCoefficient]
    positivity
  · rw [coefficient_pos_formula (by omega)]
    have h := weight_error_le (p := 2 * k + 1) (n := n) ⟨k, by omega⟩ (by omega) (by omega)
    convert h using 1
    push_cast
    ring_nf

/-- A closed finite-head error estimate replacing fixed-head convergence. -/
theorem coefficientError_le {n P : ℕ} (hsize : 16 * (P + 1) ≤ n) :
    coefficientError n P ≤ 36 * P / n := by
  unfold coefficientError
  calc
    _ ≤ ∑ k ∈ range P, (36 / (n : ℝ)) :=
      sum_le_sum fun k hk => odd_weight_error_le (mem_range.mp hk) hsize
    _ = 36 * P / n := by simp; ring

/-- A concrete frequency cutoff for the two Abel tails. -/
def frequencyCutoff (η ε : ℝ) : ℕ := ⌈3 / (η * ε)⌉₊ + 1

/-- A concrete grid-size cutoff controlling both the finite head and the two tails. -/
def gridThreshold (η ε : ℝ) : ℕ :=
  max (16 * (frequencyCutoff η ε + 1))
    (⌈108 * (frequencyCutoff η ε : ℝ) / ε⌉₊ + 1)

theorem frequencyCutoff_tail {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    1 / (((frequencyCutoff η ε : ℝ) + 1) * η) < ε / 3 := by
  have hc : 3 / (η * ε) ≤ (⌈3 / (η * ε)⌉₊ : ℝ) := Nat.le_ceil _
  have hden : 0 < ((frequencyCutoff η ε : ℝ) + 1) * η := by
    positivity
  rw [div_lt_iff₀ hden, div_mul_eq_mul_div,
    lt_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
  unfold frequencyCutoff
  push_cast
  have hprod : 3 ≤ (⌈3 / (η * ε)⌉₊ : ℝ) * (η * ε) := by
    rw [div_le_iff₀ (mul_pos hη hε)] at hc
    exact hc
  nlinarith

theorem coefficientError_lt_third {η ε : ℝ} (hε : 0 < ε)
    {m : ℕ} (hm : gridThreshold η ε ≤ m) :
    coefficientError (2 * m) (frequencyCutoff η ε) < ε / 3 := by
  let P := frequencyCutoff η ε
  have hsize : 16 * (P + 1) ≤ 2 * m := by
    have h := (le_max_left (16 * (P + 1))
      (⌈108 * (P : ℝ) / ε⌉₊ + 1)).trans hm
    omega
  have hm_nat : ⌈108 * (P : ℝ) / ε⌉₊ + 1 ≤ m :=
    (le_max_right (16 * (P + 1)) (⌈108 * (P : ℝ) / ε⌉₊ + 1)).trans hm
  have hc : 108 * (P : ℝ) / ε ≤ (⌈108 * (P : ℝ) / ε⌉₊ : ℝ) := Nat.le_ceil _
  have hm_real : 108 * (P : ℝ) / ε < (m : ℝ) := by
    have hcast : (⌈108 * (P : ℝ) / ε⌉₊ : ℝ) < (m : ℝ) := by
      exact_mod_cast (show ⌈108 * (P : ℝ) / ε⌉₊ < m by omega)
    exact hc.trans_lt hcast
  have hm0 : (0 : ℝ) < m := by
    have hP : 0 < P := by dsimp [P, frequencyCutoff]; omega
    exact_mod_cast (show 0 < m by omega)
  have hrate : 36 * (P : ℝ) / ((2 * m : ℕ) : ℝ) < ε / 3 := by
    have h2m : (0 : ℝ) < ((2 * m : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < 2 * m by omega)
    rw [div_lt_iff₀ h2m]
    rw [div_lt_iff₀ hε] at hm_real
    push_cast
    nlinarith [show 0 ≤ (P : ℝ) by positivity]
  exact (coefficientError_le hsize).trans_lt hrate

/-- The finite grid kernel has a fully explicit arithmetic convergence threshold. -/
theorem explicit_uniform_grid_series_limit {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∀ m ≥ gridThreshold η ε, ∀ r : ℕ, ∀ t : ℝ,
      (2 * m : ℕ) * t = (r : ℝ) * (2 * Real.pi) → η ≤ |sin t| →
      |finiteKernel (2 * m) t - seriesLimit t| < ε := by
  intro m hm r t hgrid ht
  let P := frequencyCutoff η ε
  have hP : 0 < P := by dsimp [P, frequencyCutoff]; omega
  have hmP : P ≤ m / 2 := by
    have h := (le_max_left (16 * (P + 1))
      (⌈108 * (P : ℝ) / ε⌉₊ + 1)).trans hm
    omega
  have ht0 : sin t ≠ 0 := abs_pos.mp (hη.trans_le ht)
  have hden : 1 / (((P : ℝ) + 1) * |sin t|) ≤
      1 / (((P : ℝ) + 1) * η) :=
    one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left ht (by positivity))
  have htail : 1 / (((P : ℝ) + 1) * η) < ε / 3 := by
    exact frequencyCutoff_tail hη hε
  have hfin := grid_kernel_tail (m := m) (r := r) hP hmP hgrid ht0
  have hser := series_limit_tail_uniform hP hη ht
  have hhead := head_error_le (2 * m) P t
  have hcoeff : coefficientError (2 * m) P < ε / 3 := by
    exact coefficientError_lt_third hε hm
  have h1 := norm_sub_le_norm_sub_add_norm_sub (finiteKernel (2 * m) t)
    (∑ k ∈ range P, SchurWeights.weight (2 * m) (2 * k + 1) * cos ((2 * k + 1 : ℕ) * t))
    (seriesLimit t)
  have h2 := norm_sub_le_norm_sub_add_norm_sub
    (∑ k ∈ range P, SchurWeights.weight (2 * m) (2 * k + 1) * cos ((2 * k + 1 : ℕ) * t))
    (seriesPartial P t) (seriesLimit t)
  simp only [Real.norm_eq_abs] at h1 h2
  rw [abs_sub_comm (seriesPartial P t) (seriesLimit t)] at h2
  linarith

end
end StructuralNote.ExplicitKernelRate

