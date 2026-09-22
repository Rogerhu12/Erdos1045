import EventualExact.FiniteFourierLift
import EventualExact.FiniteBoxMaximum

/-!
# Exact Schur blocks and the explicit mean-zero lift

Conjugation and midpoint phases are retained explicitly. The block identities
use the actual finite Schur weights. The spatial lift is defined by exact
discrete integration of the increment formula (4.4).
-/

noncomputable section

open scoped BigOperators

namespace Erdos1045.EventualExact.SchurLift

open Complex FourierMultiplier FiniteFourierLift

local notation "conj" => (starRingEnd ℂ)

def blockConstraint (n : ℕ) (x y : ℂ) : ℂ := (Complex.I * n / 2) * (x + conj y)

def blockValue (n p : ℕ) (x y : ℂ) : ℝ :=
  (n : ℝ) ^ 2 * SchurWeights.weight n p * (x * y).re

def blockGap (n p : ℕ) (x y : ℂ) : ℝ :=
  (n : ℝ) ^ 2 * SchurWeights.weight n p / 4 * Complex.normSq (x - conj y)

theorem blockGap_nonneg (n p : ℕ) (x y : ℂ) : 0 ≤ blockGap n p x y := by
  unfold blockGap
  exact mul_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) (SchurWeights.weight_nonneg _ _))
    (by norm_num)) (Complex.normSq_nonneg _)

/-- The actual two-mode completion of the square; self-paired blocks are halved. -/
theorem block_completedSquare (n p : ℕ) (x y : ℂ) :
    blockValue n p x y = SchurWeights.weight n p *
      Complex.normSq (blockConstraint n x y) - blockGap n p x y := by
  simp [blockValue, blockConstraint, blockGap, Complex.normSq_apply]
  ring

def blockLift (n : ℕ) (q : ℂ) : ℂ := -Complex.I * q / n

theorem blockLift_constraint {n : ℕ} (hn : 0 < n) (q : ℂ) :
    blockConstraint n (blockLift n q) (conj (blockLift n q)) = q := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [blockConstraint, conj_conj, blockLift]
  field_simp
  ring_nf
  simp

theorem blockLift_value {n : ℕ} (hn : 0 < n) (p : ℕ) (q : ℂ) :
    blockValue n p (blockLift n q) (conj (blockLift n q)) =
      SchurWeights.weight n p * Complex.normSq q := by
  rw [block_completedSquare, blockLift_constraint hn]
  simp [blockGap]

theorem block_value_le (n p : ℕ) (x y : ℂ) :
    blockValue n p x y ≤ SchurWeights.weight n p * Complex.normSq (blockConstraint n x y) := by
  rw [block_completedSquare]
  exact sub_le_self _ (blockGap_nonneg _ _ _ _)

theorem blockGap_eq_zero_iff {n p : ℕ} (hp : SchurWeights.Active n p) (x y : ℂ) :
    blockGap n p x y = 0 ↔ x = conj y := by
  have hn : (0 : ℝ) < n := (SchurWeights.active_bounds hp).1
  have hc : 0 < (n : ℝ) ^ 2 * SchurWeights.weight n p / 4 := by
    exact div_pos (mul_pos (sq_pos_of_pos hn) (SchurWeights.weight_pos hp)) (by norm_num)
  rw [blockGap, mul_eq_zero, or_iff_right hc.ne', Complex.normSq_eq_zero, sub_eq_zero]

theorem block_unique_maximizer {n p : ℕ} (hp : SchurWeights.Active n p)
    (x y q : ℂ) (hq : blockConstraint n x y = q) :
    blockValue n p x y = SchurWeights.weight n p * Complex.normSq q ↔
      x = blockLift n q ∧ y = conj (blockLift n q) := by
  have hn : 0 < n := by have := hp.2.2; omega
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  constructor
  · intro he
    have hz : blockGap n p x y = 0 := by
      rw [block_completedSquare, hq] at he
      linarith
    have hxy := (blockGap_eq_zero_iff hp x y).mp hz
    have hyx : y = conj x := by rw [hxy, conj_conj]
    have hx : x = blockLift n q := by
      rw [blockConstraint, ← hxy] at hq
      unfold blockLift
      rw [← hq]
      field_simp
      ring_nf
      simp
    exact ⟨hx, by rw [hyx, hx]⟩
  · rintro ⟨rfl, rfl⟩
    exact blockLift_value hn p q

theorem block_orthogonal_decomposition {n : ℕ} (hn : 0 < n)
    (p : ℕ) (q v w : ℂ) (hv : blockConstraint n v w = 0) :
    blockValue n p (blockLift n q + v) (conj (blockLift n q) + w) =
      SchurWeights.weight n p * Complex.normSq q + blockValue n p v w := by
  have he : blockConstraint n (blockLift n q + v) (conj (blockLift n q) + w) = q := by
    calc
      _ = blockConstraint n (blockLift n q) (conj (blockLift n q)) +
          blockConstraint n v w := by simp [blockConstraint]; ring
      _ = q := by rw [blockLift_constraint hn, hv, add_zero]
  rw [block_completedSquare, block_completedSquare n p v w, he, hv]
  simp [blockGap, map_add]
  ring

/-- The block value is the physical coefficient expression in (3.2), after
rescaling the two coefficients by their actual sine ratios. -/
theorem blockValue_physical {n p : ℕ} (hp : SchurWeights.Active n p) (b d : ℂ) :
    blockValue n p
      ((Real.sin (((p : ℝ) + 1) * Real.pi / n) / Real.sin (Real.pi / n) : ℝ) * b)
      ((Real.sin (((p : ℝ) - 1) * Real.pi / n) / Real.sin (Real.pi / n) : ℝ) * d) =
      (n : ℝ) * ((p : ℝ) - 1) * ((n : ℝ) - p - 1) * (b * d).re := by
  rcases SchurWeights.active_bounds hp with ⟨hn, hp0, hpn, _⟩
  have hsin (a : ℝ) (ha : 0 < a) (han : a < n) :
      Real.sin (a * Real.pi / n) ≠ 0 := by
    apply (Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_).ne'
    apply (div_lt_iff₀ hn).2
    nlinarith [Real.pi_pos]
  have hs0 := hsin 1 (by norm_num) (by linarith)
  simp only [one_mul] at hs0
  have hsminus := hsin ((p : ℝ) - 1) hp0 (by linarith)
  have hsplus := hsin ((p : ℝ) + 1) (by linarith) hpn
  simp only [blockValue, SchurWeights.weight, if_pos hp, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, sub_zero]
  generalize Real.sin (Real.pi / n) = sa at *
  generalize Real.sin (((p : ℝ) - 1) * Real.pi / n) = sm at *
  generalize Real.sin (((p : ℝ) + 1) * Real.pi / n) = sp at *
  field_simp

/-- Unit edge-midpoint direction, exp(i(2j+1)pi/n). -/
def frame (n : ℕ) (j : Fin n) : ℂ := LocalPhase.phase n 1 * character n 1 j

theorem frame_normSq (n : ℕ) (j : Fin n) : Complex.normSq (frame n j) = 1 := by
  have hc : ‖character n 1 j‖ = 1 := by
    simp [character, norm_pow, ClosedFourier.root_norm]
  rw [frame, Complex.normSq_mul, LocalPhase.phase_normSq, one_mul,
    Complex.normSq_eq_norm_sq, hc, one_pow]

def firstCoefficient {n : ℕ} (q : Fin n → ℝ) : ℂ :=
  (∑ j, (q j : ℂ) * conj (frame n j)) / n

theorem firstCoefficient_eq_midpoint {n : ℕ} (hn : 1 < n) (q : Fin n → ℝ) :
    firstCoefficient q = midpointCoefficient q ⟨1, hn⟩ := rfl

/-- Increment prescribed by (4.4), expressed in the real midpoint frame. -/
def increment {n : ℕ} (q : Fin n → ℝ) (j : Fin n) : ℂ :=
  frame n j * ((2 * Real.sin (Real.pi / n) / n : ℝ) * (q j : ℂ) +
    Complex.I * (4 * Real.sin (Real.pi / n) / n : ℝ) *
      ((firstCoefficient q * frame n j).im : ℂ))

theorem increment_polynomial {n : ℕ} (q : Fin n → ℝ) (j : Fin n) :
    increment q j = (2 * Real.sin (Real.pi / n) / n : ℝ) *
      (frame n j * (q j : ℂ) + firstCoefficient q * (frame n j) ^ 2 -
        conj (firstCoefficient q)) := by
  have hz := frame_normSq n j
  simp only [Complex.normSq_apply] at hz
  unfold increment
  rw [show (4 * Real.sin (Real.pi / n) / n : ℝ) =
    2 * (2 * Real.sin (Real.pi / n) / n) by ring]
  generalize (2 * Real.sin (Real.pi / n) / n : ℝ) = r
  apply Complex.ext <;>
    simp [pow_two] <;>
    nlinarith [congrArg (fun x : ℝ =>
      r * (firstCoefficient q).re * x) hz,
      congrArg (fun x : ℝ =>
        r * (firstCoefficient q).im * x) hz]

theorem sum_character {n : ℕ} (hn : 0 < n) (p : ℕ) :
    (∑ j : Fin n, character n p j) = if n ∣ p then (n : ℂ) else 0 := by
  rw [show (∑ j : Fin n, character n p j) =
      ∑ j ∈ Finset.range n, character n p j from
    Fin.sum_univ_eq_sum_range (fun j => character n p j) n]
  exact ClosedFourier.sum_pow hn p

theorem sum_frame_sq {n : ℕ} (hn : 3 ≤ n) : (∑ j : Fin n, (frame n j) ^ 2) = 0 := by
  have hc (j : Fin n) : (frame n j) ^ 2 =
      LocalPhase.phase n 1 ^ 2 * character n 2 j := by
    simp only [frame, mul_pow, character, ← pow_mul]
    congr 1
    congr 1
    omega
  simp_rw [hc]
  rw [← Finset.mul_sum, sum_character (by omega), if_neg, mul_zero]
  exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)

theorem sum_frame_mul {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) :
    (∑ j, frame n j * (q j : ℂ)) = (n : ℂ) * conj (firstCoefficient q) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [firstCoefficient, mul_comm, mul_div_cancel₀, hn0]

theorem increment_mean_zero {n : ℕ} (hn : 3 ≤ n) (q : Fin n → ℝ) :
    (∑ j, increment q j) = 0 := by
  simp_rw [increment_polynomial]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_frame_mul (by omega), ← Finset.mul_sum, sum_frame_sq hn]
  simp

def canonicalLift {n : ℕ} (q : Fin n → ℝ) : Fin n → ℂ := integral (increment q)

theorem canonicalLift_mean_zero {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) :
    (∑ j, canonicalLift q j) = 0 := integral_mean_zero hn _

theorem canonicalLift_difference {n : ℕ} (hn : 3 ≤ n) (q : Fin n → ℝ) :
    difference (by omega) (canonicalLift q) = increment q :=
  difference_integral (by omega) _ (increment_mean_zero hn q)

theorem canonicalLift_unique {n : ℕ} (hn : 3 ≤ n) (q : Fin n → ℝ)
    (c : Fin n → ℂ) (hc : ∑ j, c j = 0)
    (hd : difference (by omega) c = increment q) : c = canonicalLift q :=
  integral_unique (by omega) _ c hc hd

/-- The real constraint map in (4.1), using the actual neighboring difference. -/
def constraint {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) (j : Fin n) : ℝ :=
  (n : ℝ) / (2 * Real.sin (Real.pi / n)) * (conj (frame n j) * difference hn c j).re

theorem constraint_canonicalLift {n : ℕ} (hn : 3 ≤ n) (q : Fin n → ℝ) :
    constraint (by omega) (canonicalLift q) = q := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsin : 0 < Real.sin (Real.pi / n) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · apply (div_lt_iff₀ hnR).2
      have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [Real.pi_pos]
  funext j
  rw [constraint, canonicalLift_difference hn]
  have hz : conj (frame n j) * frame n j = 1 := by
    rw [mul_comm, Complex.mul_conj, frame_normSq]
    rfl
  simp only [increment, ← mul_assoc, hz, one_mul, Complex.add_re,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero, zero_add]
  field_simp

theorem root_difference_formula (n : ℕ) :
    LocalPhase.regularRoot n - 1 =
      (2 * Real.sin (Real.pi / n) : ℝ) * Complex.I * LocalPhase.phase n 1 := by
  unfold LocalPhase.regularRoot LocalPhase.phase
  simp only [Nat.cast_one, one_mul]
  rw [show (2 * Real.pi / n : ℝ) = 2 * (Real.pi / n) by ring]
  apply Complex.ext <;>
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, mul_zero, zero_mul, sub_zero, add_zero, zero_add,
      mul_one, Real.cos_two_mul, Real.sin_two_mul]
  · nlinarith [Real.sin_sq_add_cos_sq (Real.pi / n)]

theorem reference_difference {n : ℕ} (hn : 0 < n) (j : Fin n) :
    difference hn (fun j => character n 1 j) j =
      (2 * Real.sin (Real.pi / n) : ℝ) * Complex.I * frame n j := by
  change character n 1 ((j.val + 1) % n) - character n 1 j = _
  rw [character_mod hn, character_add]
  have he : character n 1 1 = LocalPhase.regularRoot n := by simp [character]
  rw [he, ← mul_sub_one, root_difference_formula]
  unfold frame
  ring

/-- Formula (4.4) uses actual neighboring chords, not a supplied derivative array. -/
theorem canonicalLift_ratio {n : ℕ} (hn : 3 ≤ n) (q : Fin n → ℝ) (j : Fin n) :
    difference (by omega) (canonicalLift q) j /
        difference (by omega) (fun j => character n 1 j) j =
      ((2 / n : ℝ) * (firstCoefficient q * frame n j).im : ℝ) -
        Complex.I / n * (q j : ℂ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : Real.sin (Real.pi / n) ≠ 0 := by
    apply (Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_).ne'
    apply (div_lt_iff₀ hnR).2
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.pi_pos]
  have hf : frame n j ≠ 0 := by
    intro h
    have hz := frame_normSq n j
    rw [h, Complex.normSq_zero] at hz
    norm_num at hz
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hnR.ne'
  have hs0 : (Real.sin (Real.pi / n) : ℂ) ≠ 0 := by exact_mod_cast hs
  rw [canonicalLift_difference hn, reference_difference, increment]
  generalize Real.sin (Real.pi / n) = sa at *
  push_cast
  field_simp
  ring_nf
  simp

theorem halfTurn_involutive {m : ℕ} (hm : 0 < m) :
    Function.Involutive (halfTurn hm) := by
  intro j
  apply Fin.ext
  change (((j.val + m) % (2 * m) + m) % (2 * m)) = j.val
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc,
    show m + m = 2 * m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]

theorem halfTurn_successor {m : ℕ} (hm : 0 < m) (j : Fin (2 * m)) :
    halfTurn hm (successor (by omega) j) = successor (by omega) (halfTurn hm j) := by
  apply Fin.ext
  change (((j.val + 1) % (2 * m) + m) % (2 * m)) =
    (((j.val + m) % (2 * m) + 1) % (2 * m))
  rw [Nat.mod_add_mod, Nat.mod_add_mod]
  congr 1
  omega

theorem frame_halfTurn {m : ℕ} (hm : 0 < m) (j : Fin (2 * m)) :
    frame (2 * m) (halfTurn hm j) = -frame (2 * m) j := by
  rw [frame, character_halfTurn hm (by decide : Odd 1), mul_neg]
  rfl

theorem increment_halfTurn {m : ℕ} (hm : 0 < m) (q : Fin (2 * m) → ℝ)
    (hq : FiniteBox.Antiperiodic hm q) (j : Fin (2 * m)) :
    increment q (halfTurn hm j) = increment q j := by
  simp [increment, frame_halfTurn hm, hq j]
  ring

/-- A real antiperiodic input lifts to an actual half-periodic center column. -/
theorem canonicalLift_halfTurn {m : ℕ} (hm : 2 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : FiniteBox.Antiperiodic (by omega) q) (j : Fin (2 * m)) :
    canonicalLift q (halfTurn (by omega) j) = canonicalLift q j := by
  have hmp : 0 < m := by omega
  have he : (fun j => canonicalLift q (halfTurn hmp j)) = canonicalLift q := by
    apply canonicalLift_unique (by omega)
    · have hs := Equiv.sum_comp
        (Equiv.ofBijective (halfTurn hmp) (halfTurn_involutive hmp).bijective)
        (canonicalLift q)
      exact hs.trans (canonicalLift_mean_zero (by omega) q)
    · funext k
      change canonicalLift q (halfTurn hmp (successor _ k)) -
        canonicalLift q (halfTurn hmp k) = increment q k
      rw [halfTurn_successor]
      change difference (by omega) (canonicalLift q) (halfTurn hmp k) = _
      rw [canonicalLift_difference (by omega), increment_halfTurn hmp q hq]
  exact congrFun he j

end Erdos1045.EventualExact.SchurLift
