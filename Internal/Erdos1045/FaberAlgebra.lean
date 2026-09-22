import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Tactic

/-!
# Algebra for the differentiated Faber generating function

This file has two independent parts. The first constructs the normalized
polynomials from Laurent coefficients by a finite recurrence. The second proves
the exact rational remainder identity and estimates that replace logarithmic
expansion in the proposed proof. No conformal mapping theorem is assumed here.

The identification of the recurrence with analytic Faber polynomials, convergence
of the generating series, and Parseval's theorem for its boundary values are
separate obligations; this file does not claim those analytic conclusions.
-/

open scoped BigOperators
open Polynomial

namespace Erdos1045.FaberAlgebra

noncomputable section

/-! ## Finite polynomial construction -/

/-- For a normalized Laurent map `w + ∑ b m / w^m`, the Faber recurrence.
The argument `b 0` is immaterial. The final summand accounts for the numerator
of the differentiated generating function. -/
def normalizedFaber (b : ℕ → ℂ) : ℕ → ℂ[X]
  | 0 => 1
  | n + 1 =>
    X * normalizedFaber b n -
      ((∑ j ∈ Finset.range n,
          C (b (j + 1)) * normalizedFaber b (n - 1 - j)) + C ((n : ℂ) * b n))
termination_by n => n
decreasing_by all_goals omega

@[simp] theorem normalizedFaber_zero (b : ℕ → ℂ) :
    normalizedFaber b 0 = 1 := by
  rw [normalizedFaber]

theorem normalizedFaber_succ (b : ℕ → ℂ) (n : ℕ) :
    normalizedFaber b (n + 1) = X * normalizedFaber b n -
      ((∑ j ∈ Finset.range n,
        C (b (j + 1)) * normalizedFaber b (n - 1 - j)) + C ((n : ℂ) * b n)) := by
  rw [normalizedFaber]

@[simp] theorem normalizedFaber_one (b : ℕ → ℂ) :
    normalizedFaber b 1 = X := by
  simp [normalizedFaber_succ]

theorem normalizedFaber_two (b : ℕ → ℂ) :
    normalizedFaber b 2 = X ^ 2 - C (2 * b 1) := by
  simp [normalizedFaber_succ, pow_two, map_mul, map_ofNat]
  ring

theorem normalizedFaber_three (b : ℕ → ℂ) :
    normalizedFaber b 3 = X ^ 3 - C (3 * b 1) * X - C (3 * b 2) := by
  simp [normalizedFaber_succ, Finset.sum_range_succ, map_mul, map_ofNat]
  ring

/-- The recurrence only introduces lower degree terms. -/
theorem normalizedFaber_monic_natDegree (b : ℕ → ℂ) (n : ℕ) :
    (normalizedFaber b n).Monic ∧ (normalizedFaber b n).natDegree = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      have hn := ih n (Nat.lt_succ_self n)
      let tail : ℂ[X] :=
        (∑ j ∈ Finset.range n,
          C (b (j + 1)) * normalizedFaber b (n - 1 - j)) + C ((n : ℂ) * b n)
      have htail : tail.natDegree ≤ n := by
        apply natDegree_add_le_of_degree_le
        · apply natDegree_sum_le_of_forall_le
          intro j hj
          have hjn : n - 1 - j < n + 1 := by omega
          calc
            (C (b (j + 1)) * normalizedFaber b (n - 1 - j)).natDegree
                ≤ (normalizedFaber b (n - 1 - j)).natDegree := natDegree_C_mul_le _ _
            _ = n - 1 - j := (ih _ hjn).2
            _ ≤ n := by omega
        · simpa only [natDegree_C] using (Nat.zero_le n)
      have hmainMonic : (X * normalizedFaber b n).Monic := monic_X.mul hn.1
      have hmainDegree : (X * normalizedFaber b n).natDegree = n + 1 := by
        rw [natDegree_X_mul hn.1.ne_zero, hn.2]
      have hlt : tail.degree < (X * normalizedFaber b n).degree := by
        rw [degree_eq_natDegree hmainMonic.ne_zero, hmainDegree]
        exact lt_of_le_of_lt (degree_le_of_natDegree_le htail) (by exact_mod_cast Nat.lt_succ_self n)
      rw [normalizedFaber_succ]
      change (X * normalizedFaber b n - tail).Monic ∧
        (X * normalizedFaber b n - tail).natDegree = n + 1
      exact ⟨hmainMonic.sub_of_left hlt,
        (natDegree_eq_of_degree_eq (degree_sub_eq_left_of_degree_lt hlt)).trans hmainDegree⟩

theorem normalizedFaber_monic (b : ℕ → ℂ) (n : ℕ) :
    (normalizedFaber b n).Monic := (normalizedFaber_monic_natDegree b n).1

@[simp] theorem normalizedFaber_natDegree (b : ℕ → ℂ) (n : ℕ) :
    (normalizedFaber b n).natDegree = n := (normalizedFaber_monic_natDegree b n).2

theorem normalizedFaber_ne_zero (b : ℕ → ℂ) (n : ℕ) :
    normalizedFaber b n ≠ 0 := (normalizedFaber_monic b n).ne_zero

@[simp] theorem normalizedFaber_leadingCoeff (b : ℕ → ℂ) (n : ℕ) :
    (normalizedFaber b n).leadingCoeff = 1 := normalizedFaber_monic b n

@[simp] theorem normalizedFaber_coeff_self (b : ℕ → ℂ) (n : ℕ) :
    (normalizedFaber b n).coeff n = 1 := by
  have h := normalizedFaber_monic b n
  change (normalizedFaber b n).coeff (normalizedFaber b n).natDegree = 1 at h
  simpa only [normalizedFaber_natDegree] using h

theorem normalizedFaber_coeff_eq_zero (b : ℕ → ℂ) {n k : ℕ} (h : n < k) :
    (normalizedFaber b n).coeff k = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  simpa using h

/-- The disk model has zero Laurent correction, and produces ordinary powers. -/
theorem normalizedFaber_zero_coefficients (n : ℕ) :
    normalizedFaber (fun _ => 0) n = X ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [normalizedFaber_succ, ih, pow_succ, mul_comm]

/-! ## Exact rational remainder, without a complex logarithm -/

/-- The differentiated correction when `p = v q'(v)`. -/
def correction (q p : ℂ) : ℂ := p / (1 + q)

/-- The remainder after retaining the first order term `p`. -/
def remainder (q p : ℂ) : ℂ := correction q p - p

theorem correction_eq_linear_add_remainder (q p : ℂ) :
    correction q p = p + remainder q p := by
  simp [remainder]

theorem remainder_eq (q p : ℂ) (hq : 1 + q ≠ 0) :
    remainder q p = -(q * p) / (1 + q) := by
  dsimp [remainder, correction]
  field_simp
  ring

theorem remainder_eq_neg_mul_correction (q p : ℂ) (hq : 1 + q ≠ 0) :
    remainder q p = -q * correction q p := by
  rw [remainder_eq q p hq]
  dsimp [correction]
  ring

/-- Reverse triangle inequality in the exact form used for the denominator. -/
theorem one_sub_norm_le_norm_denominator (q : ℂ) :
    1 - ‖q‖ ≤ ‖1 + q‖ := by
  have h := norm_sub_le (1 + q) q
  norm_num at h
  linarith

theorem denominator_ne_zero {q : ℂ} (hq : ‖q‖ < 1) :
    1 + q ≠ 0 := by
  intro hz
  have h := one_sub_norm_le_norm_denominator q
  rw [hz, norm_zero] at h
  linarith

/-- A variable-radius estimate retains the dependence on the perturbation size. -/
theorem norm_correction_le {q p : ℂ} {ρ : ℝ}
    (hρ : ρ < 1) (hq : ‖q‖ ≤ ρ) :
    ‖correction q p‖ ≤ ‖p‖ / (1 - ρ) := by
  have hden : 1 - ρ ≤ ‖1 + q‖ := by
    have := one_sub_norm_le_norm_denominator q
    linarith
  dsimp [correction]
  rw [norm_div]
  exact div_le_div_of_nonneg_left (norm_nonneg p) (by linarith) hden

theorem norm_remainder_le {q p : ℂ} {ρ : ℝ}
    (hρ : ρ < 1) (hq : ‖q‖ ≤ ρ) :
    ‖remainder q p‖ ≤ ‖q‖ * (‖p‖ / (1 - ρ)) := by
  rw [remainder_eq_neg_mul_correction q p (denominator_ne_zero (hq.trans_lt hρ))]
  rw [norm_mul, norm_neg]
  exact mul_le_mul_of_nonneg_left (norm_correction_le hρ hq) (norm_nonneg q)

theorem norm_correction_le_two {q p : ℂ} (hq : ‖q‖ ≤ 1 / 2) :
    ‖correction q p‖ ≤ 2 * ‖p‖ := by
  have h := norm_correction_le (p := p) (by norm_num : (1 / 2 : ℝ) < 1) hq
  norm_num at h ⊢
  linarith

theorem norm_remainder_le_two {q p : ℂ} (hq : ‖q‖ ≤ 1 / 2) :
    ‖remainder q p‖ ≤ 2 * ‖q‖ * ‖p‖ := by
  have h := norm_remainder_le (p := p) (by norm_num : (1 / 2 : ℝ) < 1) hq
  norm_num at h
  nlinarith

theorem norm_remainder_sq_le {q p : ℂ} (hq : ‖q‖ ≤ 1 / 2) :
    ‖remainder q p‖ ^ 2 ≤ 4 * ‖q‖ ^ 2 * ‖p‖ ^ 2 := by
  have h := norm_remainder_le_two (p := p) hq
  have hnonneg : 0 ≤ 2 * ‖q‖ * ‖p‖ := by positivity
  calc
    ‖remainder q p‖ ^ 2 ≤ (2 * ‖q‖ * ‖p‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hnonneg).mpr h
    _ = 4 * ‖q‖ ^ 2 * ‖p‖ ^ 2 := by ring

theorem norm_correction_sq_le {q p : ℂ} (hq : ‖q‖ ≤ 1 / 2) :
    ‖correction q p‖ ^ 2 ≤ 4 * ‖p‖ ^ 2 := by
  have h := norm_correction_le_two (p := p) hq
  nlinarith [norm_nonneg (correction q p), norm_nonneg p]

/-! ## Finite energy bounds

These estimates work for arbitrary finite index sets and nonnegative weights.
They apply directly to finite sampled values. Passing from pointwise rational
remainders to Fourier coefficient energies still requires an integral estimate
and Parseval; coefficients do not obey the same pointwise quotient formula.
-/

theorem norm_remainder_sq_le_uniform {q p : ℂ} {η : ℝ}
    (hη : 0 ≤ η) (hqη : ‖q‖ ≤ η) (hq : ‖q‖ ≤ 1 / 2) :
    ‖remainder q p‖ ^ 2 ≤ 4 * η ^ 2 * ‖p‖ ^ 2 := by
  calc
    ‖remainder q p‖ ^ 2 ≤ 4 * ‖q‖ ^ 2 * ‖p‖ ^ 2 := norm_remainder_sq_le hq
    _ ≤ 4 * η ^ 2 * ‖p‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg q) hη).mpr hqη)
          (by norm_num)) (sq_nonneg _)

/-- A weighted finite form of the quadratic remainder estimate. -/
theorem sum_weight_mul_remainder_sq_le
    {ι : Type*} (s : Finset ι) (a : ι → ℝ) (q p : ι → ℂ) {η : ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i) (hη : 0 ≤ η)
    (hqη : ∀ i ∈ s, ‖q i‖ ≤ η) (hq : ∀ i ∈ s, ‖q i‖ ≤ 1 / 2) :
    (∑ i ∈ s, a i * ‖remainder (q i) (p i)‖ ^ 2) ≤
      4 * η ^ 2 * ∑ i ∈ s, a i * ‖p i‖ ^ 2 := by
  calc
    (∑ i ∈ s, a i * ‖remainder (q i) (p i)‖ ^ 2) ≤
        ∑ i ∈ s, a i * (4 * η ^ 2 * ‖p i‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (norm_remainder_sq_le_uniform hη (hqη i hi) (hq i hi)) (ha i hi)
    _ = 4 * η ^ 2 * ∑ i ∈ s, a i * ‖p i‖ ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- The unweighted remainder estimate applies to any finite matrix of entries. -/
theorem sum_remainder_sq_le
    {ι : Type*} (s : Finset ι) (q p : ι → ℂ) {η : ℝ}
    (hη : 0 ≤ η) (hqη : ∀ i ∈ s, ‖q i‖ ≤ η)
    (hq : ∀ i ∈ s, ‖q i‖ ≤ 1 / 2) :
    (∑ i ∈ s, ‖remainder (q i) (p i)‖ ^ 2) ≤
      4 * η ^ 2 * ∑ i ∈ s, ‖p i‖ ^ 2 := by
  simpa using sum_weight_mul_remainder_sq_le s (fun _ => 1) q p
    (by intros; norm_num) hη hqη hq

theorem sum_weight_mul_correction_sq_le
    {ι : Type*} (s : Finset ι) (a : ι → ℝ) (q p : ι → ℂ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hq : ∀ i ∈ s, ‖q i‖ ≤ 1 / 2) :
    (∑ i ∈ s, a i * ‖correction (q i) (p i)‖ ^ 2) ≤
      4 * ∑ i ∈ s, a i * ‖p i‖ ^ 2 := by
  calc
    (∑ i ∈ s, a i * ‖correction (q i) (p i)‖ ^ 2) ≤
        ∑ i ∈ s, a i * (4 * ‖p i‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (norm_correction_sq_le (hq i hi)) (ha i hi)
    _ = 4 * ∑ i ∈ s, a i * ‖p i‖ ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Square norms differ by a controlled first order term. -/
theorem abs_sq_norm_sub_sq_norm_le (z w : ℂ) :
    |‖z‖ ^ 2 - ‖w‖ ^ 2| ≤ ‖z - w‖ * (‖z‖ + ‖w‖) := by
  calc
    |‖z‖ ^ 2 - ‖w‖ ^ 2| = |‖z‖ - ‖w‖| * (‖z‖ + ‖w‖) := by
      rw [sq_sub_sq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖z‖ + ‖w‖)]
      ring
    _ ≤ ‖z - w‖ * (‖z‖ + ‖w‖) := by
      gcongr
      exact abs_norm_sub_norm_le z w

theorem correction_energy_error_le {q p : ℂ} (hq : ‖q‖ ≤ 1 / 2) :
    |‖correction q p‖ ^ 2 - ‖p‖ ^ 2| ≤ 6 * ‖q‖ * ‖p‖ ^ 2 := by
  have hr := norm_remainder_le_two (p := p) hq
  have hc := norm_correction_le_two (p := p) hq
  calc
    |‖correction q p‖ ^ 2 - ‖p‖ ^ 2| ≤
        ‖remainder q p‖ * (‖correction q p‖ + ‖p‖) :=
      abs_sq_norm_sub_sq_norm_le (correction q p) p
    _ ≤ (2 * ‖q‖ * ‖p‖) * (2 * ‖p‖ + ‖p‖) := by
      gcongr
    _ = 6 * ‖q‖ * ‖p‖ ^ 2 := by ring

end

end Erdos1045.FaberAlgebra
