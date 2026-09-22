import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Tauto

/-!
# Algebraic estimates for paired Fourier modes

This file proves the numerical and complex quadratic-form part of the local
coercivity argument. It does not assert the Fourier representation of the
geometric Hessian, the trigonometric estimates for its coefficients, or the
Taylor remainder estimate. Those analytic statements remain separate tasks.

The size parameter is real in the elementary estimates; therefore the results
can later be specialized to natural polygon orders without changing constants.
-/

namespace Erdos1045.LocalCoercivity

noncomputable section

open Complex
open scoped BigOperators

section ScalarWeights

variable {n r : ℝ}

theorem size_pos (hn : 4 ≤ n) : 0 < n := by
  linarith

theorem size_sub_one_pos (hn : 4 ≤ n) : 0 < n - 1 := by
  linarith

theorem complementary_weight_pos (hn : 4 ≤ n)
    (hr : r ≤ (5 / 6 : ℝ) * (n - 1)) : 0 < n - 1 - r := by
  linarith

theorem complementary_weight_lower (hn : 4 ≤ n)
    (hr : r ≤ (5 / 6 : ℝ) * (n - 1)) :
    (9 * r + 2 * n) / 64 ≤ n - 1 - r := by
  linarith

theorem direct_weight_lower (hr : 0 ≤ r) : 9 * r / 64 ≤ r := by
  linarith

theorem complementary_weight_uniform (hn : 4 ≤ n)
    (hr : r ≤ (5 / 6 : ℝ) * (n - 1)) :
    n / 8 ≤ n - 1 - r := by
  linarith

theorem control_weight_pos (hn : 4 ≤ n) (hr : 0 ≤ r) :
    0 < 9 * r + 2 * n := by
  linarith

end ScalarWeights

section ComplexAlgebra

theorem parallelogram (x y : ℂ) :
    normSq (x + y) + normSq (x - y) = 2 * (normSq x + normSq y) := by
  rw [normSq_add, normSq_sub]
  ring

theorem sum_difference_zero_iff (x y : ℂ) :
    x + y = 0 ∧ x - y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · rintro ⟨hs, hd⟩
    have hx : x = 0 := by
      linear_combination (1 / 2 : ℂ) * hs + (1 / 2 : ℂ) * hd
    constructor
    · exact hx
    · simpa [hx] using hs
  · rintro ⟨rfl, rfl⟩
    simp

theorem normSq_sum_difference_zero_iff (x y : ℂ) :
    normSq (x + y) + normSq (x - y) = 0 ↔ x = 0 ∧ y = 0 := by
  rw [add_eq_zero_iff_of_nonneg (normSq_nonneg _) (normSq_nonneg _)]
  simp only [normSq_eq_zero, sum_difference_zero_iff]

theorem normSq_sum_le (x y : ℂ) :
    normSq (x + y) ≤ 2 * (normSq x + normSq y) := by
  have hp := parallelogram x y
  have hd := normSq_nonneg (x - y)
  linarith

theorem normSq_difference_le (x y : ℂ) :
    normSq (x - y) ≤ 2 * (normSq x + normSq y) := by
  have hp := parallelogram x y
  have hs := normSq_nonneg (x + y)
  linarith

/-- The paired-mode energy in sum and difference coordinates. -/
def blockEnergy (n r : ℝ) (x y : ℂ) : ℝ :=
  n / 4 * ((n - 1 - r) * normSq (x + y) + r * normSq (x - y))

/-- The explicit upper envelope used to compare with the geometric energies. -/
def controlEnergy (n r : ℝ) (x y : ℂ) : ℝ :=
  n / 4 * ((9 * r + 2 * n) * normSq (x + y) + 9 * r * normSq (x - y))

theorem blockEnergy_zero (n r : ℝ) : blockEnergy n r 0 0 = 0 := by
  simp [blockEnergy]

theorem controlEnergy_zero (n r : ℝ) : controlEnergy n r 0 0 = 0 := by
  simp [controlEnergy]

theorem blockEnergy_nonneg {n r : ℝ} (hn : 4 ≤ n) (hr : 0 ≤ r)
    (hupper : r ≤ (5 / 6 : ℝ) * (n - 1)) (x y : ℂ) :
    0 ≤ blockEnergy n r x y := by
  unfold blockEnergy
  have hn0 := (size_pos hn).le
  have hcomp := (complementary_weight_pos hn hupper).le
  exact mul_nonneg (div_nonneg hn0 (by norm_num))
    (add_nonneg (mul_nonneg hcomp (normSq_nonneg _))
      (mul_nonneg hr (normSq_nonneg _)))

theorem controlEnergy_nonneg {n r : ℝ} (hn : 0 ≤ n) (hr : 0 ≤ r)
    (x y : ℂ) : 0 ≤ controlEnergy n r x y := by
  have hs := normSq_nonneg (x + y)
  have hd := normSq_nonneg (x - y)
  unfold controlEnergy
  positivity

/-- The constant is independent of both the polygon order and the mode. -/
theorem blockEnergy_coercive {n r : ℝ} (hn : 4 ≤ n) (hr : 0 ≤ r)
    (hupper : r ≤ (5 / 6 : ℝ) * (n - 1)) (x y : ℂ) :
    controlEnergy n r x y / 64 ≤ blockEnergy n r x y := by
  have hs := mul_le_mul_of_nonneg_right
    (complementary_weight_lower hn hupper) (normSq_nonneg (x + y))
  have hd := mul_le_mul_of_nonneg_right
    (direct_weight_lower hr) (normSq_nonneg (x - y))
  have h := mul_le_mul_of_nonneg_left (add_le_add hs hd)
    (show 0 ≤ n / 4 by linarith)
  dsimp [controlEnergy, blockEnergy]
  nlinarith [h]

theorem blockEnergy_eq_zero_iff {n r : ℝ} (hn : 4 ≤ n) (hr : 0 < r)
    (hupper : r ≤ (5 / 6 : ℝ) * (n - 1)) (x y : ℂ) :
    blockEnergy n r x y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro hz
    have hn4 : 0 < n / 4 := by linarith
    have hc := complementary_weight_pos hn hupper
    have hs := normSq_nonneg (x + y)
    have hd := normSq_nonneg (x - y)
    have hz' : (n - 1 - r) * normSq (x + y) + r * normSq (x - y) = 0 := by
      exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hn4)
    have hsp : 0 ≤ (n - 1 - r) * normSq (x + y) := mul_nonneg hc.le hs
    have hdp : 0 ≤ r * normSq (x - y) := mul_nonneg hr.le hd
    have hsz : normSq (x + y) = 0 := by nlinarith
    have hdz : normSq (x - y) = 0 := by nlinarith
    exact (sum_difference_zero_iff x y).mp
      ⟨normSq_eq_zero.mp hsz, normSq_eq_zero.mp hdz⟩
  · rintro ⟨rfl, rfl⟩
    exact blockEnergy_zero n r

theorem blockEnergy_pos_iff {n r : ℝ} (hn : 4 ≤ n) (hr : 0 < r)
    (hupper : r ≤ (5 / 6 : ℝ) * (n - 1)) (x y : ℂ) :
    0 < blockEnergy n r x y ↔ x ≠ 0 ∨ y ≠ 0 := by
  rw [lt_iff_le_and_ne]
  have hnonneg := blockEnergy_nonneg hn hr.le hupper x y
  simp only [hnonneg, true_and]
  rw [ne_comm, ne_eq]
  rw [blockEnergy_eq_zero_iff hn hr hupper]
  tauto

/-- For a self-paired mode the two entries are related by complex conjugation. -/
theorem self_paired_energy (n r : ℝ) (x : ℂ) :
    blockEnergy n r x (star x) =
      n * ((n - 1 - r) * x.re ^ 2 + r * x.im ^ 2) := by
  simp [blockEnergy, normSq_apply]
  ring

theorem self_paired_zero_iff {n r : ℝ} (hn : 4 ≤ n) (hr : 0 < r)
    (hupper : r ≤ (5 / 6 : ℝ) * (n - 1)) (x : ℂ) :
    blockEnergy n r x (star x) = 0 ↔ x = 0 := by
  rw [blockEnergy_eq_zero_iff hn hr hupper]
  simp

end ComplexAlgebra

section WeightedComparison

/-- A weighted pair plus the common sum-coordinate term. For the paper's
paired modes the substitution is `x = s_k * b_k`, `y = s_l * conj b_l`;
the conjugation in the second entry is essential. The associated components
are `A = n / 2 * (a * normSq x + b * normSq y)` and
`B = n / 2 * normSq (x + y)`, so this definition is their `A + n * B`. -/
def weightedEnergy (n a b : ℝ) (x y : ℂ) : ℝ :=
  n / 2 * (a * normSq x + b * normSq y) + n ^ 2 / 2 * normSq (x + y)

theorem weightedEnergy_nonneg {n a b : ℝ} (hn : 0 ≤ n)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (x y : ℂ) :
    0 ≤ weightedEnergy n a b x y := by
  have hx := normSq_nonneg x
  have hy := normSq_nonneg y
  have hs := normSq_nonneg (x + y)
  unfold weightedEnergy
  positivity

theorem weightedEnergy_mono {n a b a' b' : ℝ} (hn : 0 ≤ n)
    (ha : a ≤ a') (hb : b ≤ b') (x y : ℂ) :
    weightedEnergy n a b x y ≤ weightedEnergy n a' b' x y := by
  unfold weightedEnergy
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_right ha (normSq_nonneg x))
        (mul_le_mul_of_nonneg_right hb (normSq_nonneg y)))
      (show 0 ≤ n / 2 by positivity)) le_rfl

theorem weightedEnergy_equal_weights (n r : ℝ) (x y : ℂ) :
    weightedEnergy n (9 * r) (9 * r) x y = controlEnergy n r x y := by
  have hp := parallelogram x y
  dsimp [weightedEnergy, controlEnergy]
  linear_combination -(9 * n * r / 4) * hp

theorem weightedEnergy_le_control {n r a b : ℝ} (hn : 0 ≤ n)
    (ha : a ≤ 9 * r) (hb : b ≤ 9 * r) (x y : ℂ) :
    weightedEnergy n a b x y ≤ controlEnergy n r x y := by
  rw [← weightedEnergy_equal_weights]
  exact weightedEnergy_mono hn ha hb x y

theorem weightedEnergy_le_control_of_three_nine {n r a b : ℝ}
    (hn : 0 ≤ n) (hr : 0 ≤ r) (ha : a ≤ 3 * r) (hb : b ≤ 9 * r)
    (x y : ℂ) : weightedEnergy n a b x y ≤ controlEnergy n r x y := by
  exact weightedEnergy_le_control hn (by linarith) hb x y

theorem weightedEnergy_coercive {n r a b : ℝ} (hn : 4 ≤ n) (hr : 0 ≤ r)
    (hupper : r ≤ (5 / 6 : ℝ) * (n - 1))
    (ha : a ≤ 3 * r) (hb : b ≤ 9 * r) (x y : ℂ) :
    weightedEnergy n a b x y / 64 ≤ blockEnergy n r x y := by
  calc
    weightedEnergy n a b x y / 64 ≤ controlEnergy n r x y / 64 := by
      exact div_le_div_of_nonneg_right
        (weightedEnergy_le_control_of_three_nine (size_pos hn).le hr ha hb x y)
        (by norm_num)
    _ ≤ blockEnergy n r x y := blockEnergy_coercive hn hr hupper x y

end WeightedComparison

section FiniteSums

variable {ι : Type*} (s : Finset ι) {n : ℝ}
variable (r : ι → ℝ) (x y : ι → ℂ)

theorem sum_blockEnergy_nonneg (hn : 4 ≤ n)
    (hr : ∀ i ∈ s, 0 ≤ r i)
    (hupper : ∀ i ∈ s, r i ≤ (5 / 6 : ℝ) * (n - 1)) :
    0 ≤ ∑ i ∈ s, blockEnergy n (r i) (x i) (y i) := by
  apply Finset.sum_nonneg
  intro i hi
  exact blockEnergy_nonneg hn (hr i hi) (hupper i hi) (x i) (y i)

theorem sum_blockEnergy_coercive (hn : 4 ≤ n)
    (hr : ∀ i ∈ s, 0 ≤ r i)
    (hupper : ∀ i ∈ s, r i ≤ (5 / 6 : ℝ) * (n - 1)) :
    (∑ i ∈ s, controlEnergy n (r i) (x i) (y i)) / 64 ≤
      ∑ i ∈ s, blockEnergy n (r i) (x i) (y i) := by
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i hi
  exact blockEnergy_coercive hn (hr i hi) (hupper i hi) (x i) (y i)

theorem sum_weightedEnergy_coercive (a b : ι → ℝ) (hn : 4 ≤ n)
    (hr : ∀ i ∈ s, 0 ≤ r i)
    (hupper : ∀ i ∈ s, r i ≤ (5 / 6 : ℝ) * (n - 1))
    (ha : ∀ i ∈ s, a i ≤ 3 * r i)
    (hb : ∀ i ∈ s, b i ≤ 9 * r i) :
    (∑ i ∈ s, weightedEnergy n (a i) (b i) (x i) (y i)) / 64 ≤
      ∑ i ∈ s, blockEnergy n (r i) (x i) (y i) := by
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i hi
  exact weightedEnergy_coercive hn (hr i hi) (hupper i hi)
    (ha i hi) (hb i hi) (x i) (y i)

theorem sum_blockEnergy_eq_zero_iff (hn : 4 ≤ n)
    (hr : ∀ i ∈ s, 0 < r i)
    (hupper : ∀ i ∈ s, r i ≤ (5 / 6 : ℝ) * (n - 1)) :
    (∑ i ∈ s, blockEnergy n (r i) (x i) (y i)) = 0 ↔
      ∀ i ∈ s, x i = 0 ∧ y i = 0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg]
  · constructor
    · intro h i hi
      exact (blockEnergy_eq_zero_iff hn (hr i hi) (hupper i hi) _ _).mp (h i hi)
    · intro h i hi
      exact (blockEnergy_eq_zero_iff hn (hr i hi) (hupper i hi) _ _).mpr (h i hi)
  · intro i hi
    exact blockEnergy_nonneg hn (hr i hi).le (hupper i hi) _ _

end FiniteSums

section NonlinearAbsorption

/-- The one-sided remainder estimate is sufficient for the local maximum step.
This is the form supplied directly by equation (6.4) of the manuscript. -/
theorem absorb_upper_remainder {A B n η Q Δ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hn : 0 ≤ n)
    (hη : η ≤ (1 / 1000 : ℝ))
    (hQ : (A + n * B) / 64 ≤ Q)
    (hΔ : Δ ≤ -Q + 4 * η * (A + n * B)) :
    Δ ≤ -(A + n * B) / 128 := by
  have hT : 0 ≤ A + n * B := add_nonneg hA (mul_nonneg hn hB)
  have hηT := mul_le_mul_of_nonneg_right hη hT
  nlinarith

/-- The Taylor remainder is an explicit hypothesis, not supplied by this file. -/
theorem absorb_remainder {A B n η Q R Δ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hn : 0 ≤ n)
    (hη : η ≤ (1 / 1000 : ℝ))
    (hQ : (A + n * B) / 64 ≤ Q)
    (hR : |R| ≤ 4 * η * (A + n * B))
    (hΔ : Δ ≤ -Q + R) :
    Δ ≤ -(A + n * B) / 128 := by
  have hT : 0 ≤ A + n * B := add_nonneg hA (mul_nonneg hn hB)
  have hηT := mul_le_mul_of_nonneg_right hη hT
  have hR' : R ≤ 4 * η * (A + n * B) := le_trans (le_abs_self R) hR
  nlinarith

theorem absorb_remainder_strict {A B n η Q R Δ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hn : 0 < n)
    (hne : A ≠ 0 ∨ B ≠ 0) (hη : η ≤ (1 / 1000 : ℝ))
    (hQ : (A + n * B) / 64 ≤ Q)
    (hR : |R| ≤ 4 * η * (A + n * B))
    (hΔ : Δ ≤ -Q + R) : Δ < 0 := by
  have hb := absorb_remainder hA hB hn.le hη hQ hR hΔ
  have hT : 0 < A + n * B := by
    rcases hne with hne | hne
    · have : 0 < A := lt_of_le_of_ne hA (Ne.symm hne)
      nlinarith
    · have : 0 < B := lt_of_le_of_ne hB (Ne.symm hne)
      nlinarith
  linarith

theorem equality_forces_zero_energy {A B n η Q R Δ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hn : 0 < n)
    (hη : η ≤ (1 / 1000 : ℝ))
    (hQ : (A + n * B) / 64 ≤ Q)
    (hR : |R| ≤ 4 * η * (A + n * B))
    (hΔ : Δ ≤ -Q + R) (heq : 0 ≤ Δ) : A = 0 ∧ B = 0 := by
  have hb := absorb_remainder hA hB hn.le hη hQ hR hΔ
  have hprod : 0 ≤ n * B := mul_nonneg hn.le hB
  have hAz : A = 0 := by linarith
  have hBz : B = 0 := by nlinarith
  exact ⟨hAz, hBz⟩

end NonlinearAbsorption

end

end Erdos1045.LocalCoercivity
