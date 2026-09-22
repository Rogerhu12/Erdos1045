import EventualExact.BoxDefect
import EventualExact.SchurWeights
import Erdos1045.ClosedOrthogonality
import Mathlib.Algebra.Group.Fin.Basic

/-!
# The finite real Fourier multiplier

The real operator is an explicit sum of rank-one cosine and sine operators.
Its weights are the manuscript weights, including their exact finite support.
-/

noncomputable section

open scoped BigOperators

namespace Erdos1045.EventualExact.FourierMultiplier

open Complex

def character (n p j : ℕ) : ℂ := LocalPhase.regularRoot n ^ (j * p)

def cosine (n p : ℕ) (j : Fin n) : ℝ := (character n p j).re

def sine (n p : ℕ) (j : Fin n) : ℝ := (character n p j).im

/-- Unshifted Fourier coefficients with empirical-average normalization. -/
def coefficient {n : ℕ} (f : Fin n → ℂ) (p : Fin n) : ℂ :=
  (∑ j, f j * (starRingEnd ℂ) (character n p j)) / n

def realCoefficient {n : ℕ} (f : Fin n → ℝ) (p : Fin n) : ℂ :=
  coefficient (fun j => (f j : ℂ)) p

def synthesis {n : ℕ} (a : Fin n → ℂ) (j : Fin n) : ℂ :=
  ∑ p, a p * character n p j

def rankOne {n : ℕ} (b : Fin n → ℝ) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun f := fun j => finitePairing f b * b j
  map_add' f g := by
    funext j
    simp [finitePairing_add_left, add_mul]
  map_smul' a f := by
    funext j
    simp [finitePairing, ← Finset.mul_sum, mul_assoc]

/-- The exact finite real operator, with no abstract spectral assumptions. -/
def operator (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  ∑ p : Fin n, (SchurWeights.weight n p / n) •
    (rankOne (cosine n p) + rankOne (sine n p))

theorem operator_apply {n : ℕ} (f : Fin n → ℝ) (j : Fin n) :
    operator n f j = ∑ p : Fin n, (SchurWeights.weight n p / n) *
      (finitePairing f (cosine n p) * cosine n p j +
        finitePairing f (sine n p) * sine n p j) := by
  simp [operator, rankOne, LinearMap.sum_apply, Finset.sum_apply, mul_add]

theorem pairing_operator {n : ℕ} (f g : Fin n → ℝ) :
    finitePairing f (operator n g) =
      ∑ p : Fin n, (SchurWeights.weight n p / n) *
        (finitePairing f (cosine n p) * finitePairing g (cosine n p) +
          finitePairing f (sine n p) * finitePairing g (sine n p)) := by
  change (∑ j, f j * operator n g j) = _
  simp only [operator_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  calc
    _ = ∑ j, (((SchurWeights.weight n p / n) * finitePairing g (cosine n p)) *
        (f j * cosine n p j) +
      ((SchurWeights.weight n p / n) * finitePairing g (sine n p)) *
        (f j * sine n p j)) := by
      apply Finset.sum_congr rfl
      intros
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      change _ * finitePairing f (cosine n p) + _ * finitePairing f (sine n p) = _
      ring

theorem selfAdjoint (n : ℕ) : FiniteSelfAdjoint (operator n) := by
  intro f g
  simp only [pairing_operator]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem positiveSemidefinite (n : ℕ) : FinitePositiveSemidefinite (operator n) := by
  intro f
  rw [pairing_operator]
  apply Finset.sum_nonneg
  intro p _
  apply mul_nonneg (div_nonneg (SchurWeights.weight_nonneg n p) (Nat.cast_nonneg n))
  exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

theorem realCoefficient_re {n : ℕ} (f : Fin n → ℝ) (p : Fin n) :
    (realCoefficient f p).re = finitePairing f (cosine n p) / n := by
  change ((∑ j, (f j : ℂ) * (starRingEnd ℂ) (character n p j)) /
    ((n : ℝ) : ℂ)).re = _
  simp [finitePairing, cosine]

theorem realCoefficient_im {n : ℕ} (f : Fin n → ℝ) (p : Fin n) :
    (realCoefficient f p).im = -finitePairing f (sine n p) / n := by
  change ((∑ j, (f j : ℂ) * (starRingEnd ℂ) (character n p j)) /
    ((n : ℝ) : ℂ)).im = _
  simp [finitePairing, sine, Finset.sum_neg_distrib]

/-- Exact spectral energy with the normalization used for the finite box problem. -/
theorem spectral_energy {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) :
    normalizedBoxEnergy (operator n) f =
      (1 / 2 : ℝ) * ∑ p : Fin n,
        SchurWeights.weight n p * Complex.normSq (realCoefficient f p) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [normalizedBoxEnergy, boxEnergy, Fintype.card_fin, pairing_operator,
    Complex.normSq_apply, realCoefficient_re, realCoefficient_im]
  rw [Finset.sum_div, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  field_simp

theorem character_orthogonality {n : ℕ} (hn : 0 < n) (p q : Fin n) :
    (∑ j : Fin n, character n p j * (starRingEnd ℂ) (character n q j)) =
      if p = q then (n : ℂ) else 0 := by
  have h := ClosedFourier.sum_mul_conj hn p q
  rw [show (∑ j : Fin n, character n p j * (starRingEnd ℂ) (character n q j)) =
    ∑ j ∈ Finset.range n, character n p j * (starRingEnd ℂ) (character n q j) from
      Fin.sum_univ_eq_sum_range (fun j => character n p j *
        (starRingEnd ℂ) (character n q j)) n]
  simpa only [character, Nat.mod_eq_of_lt p.isLt,
    Nat.mod_eq_of_lt q.isLt, Fin.ext_iff] using h

/-- Synthesis followed by analysis is the identity, proved from roots of unity. -/
theorem coefficient_synthesis {n : ℕ} (hn : 0 < n) (a : Fin n → ℂ) (q : Fin n) :
    coefficient (synthesis a) q = a q := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [coefficient, synthesis, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, character_orthogonality hn]
  simp [hn0]

theorem weight_neg {n : ℕ} [NeZero n] (hn : Even n) (p : Fin n) :
    SchurWeights.weight n (-p).val = SchurWeights.weight n p.val := by
  by_cases hp : p = 0
  · subst p
    simp
  · rw [Fin.val_neg, if_neg hp]
    exact SchurWeights.weight_reflect hn p.isLt.le

theorem character_neg {n : ℕ} [NeZero n] (p : Fin n) (j : ℕ) :
    character n (-p).val j = (starRingEnd ℂ) (character n p.val j) := by
  by_cases hp : p = 0
  · subst p
    simp [character]
  · have hn : 0 < n := NeZero.pos n
    have hnorm : ‖character n p j‖ = 1 := by
      simp [character, norm_pow, ClosedFourier.root_norm]
    rw [← Complex.inv_eq_conj hnorm]
    apply eq_inv_of_mul_eq_one_left
    simp only [character, Fin.val_neg, if_neg hp]
    rw [← pow_add, ← Nat.mul_add, Nat.sub_add_cancel p.isLt.le,
      Nat.mul_comm j n, pow_mul, LocalDFT.regularRoot_pow hn, one_pow]

theorem realCoefficient_neg {n : ℕ} [NeZero n] (f : Fin n → ℝ) (p : Fin n) :
    realCoefficient f (-p) = (starRingEnd ℂ) (realCoefficient f p) := by
  simp [realCoefficient, coefficient, character_neg]

theorem synthesis_weighted_conj {n : ℕ} (hn : 0 < n) (heven : Even n)
    (f : Fin n → ℝ) (j : Fin n) :
    (starRingEnd ℂ) (synthesis (fun p =>
      (SchurWeights.weight n p : ℂ) * realCoefficient f p) j) =
    synthesis (fun p => (SchurWeights.weight n p : ℂ) * realCoefficient f p) j := by
  let : NeZero n := ⟨hn.ne'⟩
  unfold synthesis
  rw [map_sum]
  calc
    _ = ∑ p : Fin n, ((SchurWeights.weight n (-p).val : ℂ) *
        realCoefficient f (-p)) * character n (-p).val j := by
      apply Finset.sum_congr rfl
      intro p _
      simp only [weight_neg heven, realCoefficient_neg, character_neg, map_mul,
        Complex.conj_ofReal]
    _ = _ := Equiv.sum_comp (Equiv.neg (Fin n)) (fun p =>
      (SchurWeights.weight n p : ℂ) * realCoefficient f p * character n p j)

theorem operator_eq_synthesis_re {n : ℕ} (f : Fin n → ℝ) (j : Fin n) :
    operator n f j = (synthesis (fun p =>
      (SchurWeights.weight n p : ℂ) * realCoefficient f p) j).re := by
  rw [operator_apply]
  simp only [synthesis, Complex.re_sum, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, sub_zero,
    realCoefficient_re, realCoefficient_im]
  apply Finset.sum_congr rfl
  intro p _
  dsimp [cosine, sine]
  ring

/-- Even-grid reflection symmetry makes the complex synthesis exactly real. -/
theorem operator_eq_synthesis {n : ℕ} (hn : 0 < n) (heven : Even n)
    (f : Fin n → ℝ) (j : Fin n) :
    (operator n f j : ℂ) = synthesis (fun p =>
      (SchurWeights.weight n p : ℂ) * realCoefficient f p) j := by
  apply Complex.ext
  · exact operator_eq_synthesis_re f j
  · have hi := congrArg Complex.im (synthesis_weighted_conj hn heven f j)
    simp only [Complex.conj_im] at hi
    simp only [Complex.ofReal_im]
    linarith

/-- The constructed real operator really multiplies each Fourier coefficient
by the manuscript's exact finite weight. -/
theorem coefficient_operator {n : ℕ} (hn : 0 < n) (heven : Even n)
    (f : Fin n → ℝ) (p : Fin n) :
    realCoefficient (operator n f) p =
      (SchurWeights.weight n p : ℂ) * realCoefficient f p := by
  change coefficient (fun j => (operator n f j : ℂ)) p = _
  simp_rw [operator_eq_synthesis hn heven]
  exact coefficient_synthesis hn _ p

theorem character_eq_exp (n p j : ℕ) :
    character n p j = Complex.exp
      (((2 * Real.pi * p * j / n : ℝ) : ℂ) * Complex.I) := by
  unfold character LocalPhase.regularRoot
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem cosine_eq_cos (n p : ℕ) (j : Fin n) :
    cosine n p j = Real.cos (2 * Real.pi * p * j / n) := by
  rw [cosine, character_eq_exp, Complex.exp_ofReal_mul_I_re]

theorem sine_eq_sin (n p : ℕ) (j : Fin n) :
    sine n p j = Real.sin (2 * Real.pi * p * j / n) := by
  rw [sine, character_eq_exp, Complex.exp_ofReal_mul_I_im]

/-- The edge-midpoint convention in (4.1), including its frequency phase. -/
def midpointCoefficient {n : ℕ} (f : Fin n → ℝ) (p : Fin n) : ℂ :=
  (∑ j, (f j : ℂ) * (starRingEnd ℂ)
    (LocalPhase.phase n p * character n p j)) / n

theorem midpointCharacter_eq_exp (n p j : ℕ) :
    LocalPhase.phase n p * character n p j =
      Complex.exp ((((p : ℝ) * (2 * j + 1) * Real.pi / n : ℝ) : ℂ) *
        Complex.I) := by
  rw [LocalPhase.phase, character_eq_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem midpointCoefficient_eq {n : ℕ} (f : Fin n → ℝ) (p : Fin n) :
    midpointCoefficient f p =
      realCoefficient f p * (starRingEnd ℂ) (LocalPhase.phase n p) := by
  simp only [midpointCoefficient, realCoefficient, coefficient, map_mul]
  rw [div_mul_eq_mul_div, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intros
  ring

theorem midpointCoefficient_normSq {n : ℕ} (f : Fin n → ℝ) (p : Fin n) :
    Complex.normSq (midpointCoefficient f p) =
      Complex.normSq (realCoefficient f p) := by
  rw [midpointCoefficient_eq, Complex.normSq_mul, Complex.normSq_conj,
    LocalPhase.phase_normSq, mul_one]

theorem midpointCoefficient_operator {n : ℕ} (hn : 0 < n) (heven : Even n)
    (f : Fin n → ℝ) (p : Fin n) :
    midpointCoefficient (operator n f) p =
      (SchurWeights.weight n p : ℂ) * midpointCoefficient f p := by
  rw [midpointCoefficient_eq, coefficient_operator hn heven, midpointCoefficient_eq,
    mul_assoc]

/-- The energy identity in the exact midpoint convention of the manuscript. -/
theorem spectral_energy_midpoint {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) :
    normalizedBoxEnergy (operator n) f =
      (1 / 2 : ℝ) * ∑ p : Fin n,
        SchurWeights.weight n p * Complex.normSq (midpointCoefficient f p) := by
  simp_rw [midpointCoefficient_normSq]
  exact spectral_energy hn f

theorem character_mod {n : ℕ} (hn : 0 < n) (p j : ℕ) :
    character n p (j % n) = character n p j := by
  apply (ClosedFourier.root_pow_eq_iff hn _ _).2
  simp only [Nat.mul_mod, Nat.mod_mod]

theorem character_add (n p j k : ℕ) :
    character n p (j + k) = character n p j * character n p k := by
  unfold character
  rw [Nat.add_mul, pow_add]

theorem root_halfTurn {m : ℕ} (hm : 0 < m) :
    LocalPhase.regularRoot (2 * m) ^ m = -1 := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold LocalPhase.regularRoot
  rw [← Complex.exp_nat_mul]
  rw [show (m : ℂ) * (((2 * Real.pi / ((2 * m : ℕ) : ℝ) : ℝ) : ℂ) *
      Complex.I) = (Real.pi : ℂ) * Complex.I by push_cast; field_simp]
  exact Complex.exp_pi_mul_I

/-- The actual half-turn permutation on the even grid. -/
def halfTurn {m : ℕ} (hm : 0 < m) (j : Fin (2 * m)) : Fin (2 * m) :=
  ⟨(j.val + m) % (2 * m), Nat.mod_lt _ (by omega)⟩

theorem character_halfTurn {m p : ℕ} (hm : 0 < m) (hp : Odd p)
    (j : Fin (2 * m)) :
    character (2 * m) p (halfTurn hm j) = -character (2 * m) p j := by
  change character (2 * m) p ((j.val + m) % (2 * m)) = _
  rw [character_mod (by omega), character_add]
  have he : character (2 * m) p m = -1 := by
    rw [character, pow_mul, root_halfTurn hm, hp.neg_one_pow]
  rw [he, mul_neg_one]

theorem cosine_halfTurn {m p : ℕ} (hm : 0 < m) (hp : Odd p)
    (j : Fin (2 * m)) :
    cosine (2 * m) p (halfTurn hm j) = -cosine (2 * m) p j := by
  simp only [cosine, character_halfTurn hm hp, Complex.neg_re]

theorem sine_halfTurn {m p : ℕ} (hm : 0 < m) (hp : Odd p)
    (j : Fin (2 * m)) :
    sine (2 * m) p (halfTurn hm j) = -sine (2 * m) p j := by
  simp only [sine, character_halfTurn hm hp, Complex.neg_im]

/-- The entire range of the operator consists of real antiperiodic vectors. -/
theorem operator_antiperiodic {m : ℕ} (hm : 0 < m)
    (f : Fin (2 * m) → ℝ) (j : Fin (2 * m)) :
    operator (2 * m) f (halfTurn hm j) = -operator (2 * m) f j := by
  rw [operator_apply, operator_apply, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : SchurWeights.Active (2 * m) p
  · rw [cosine_halfTurn hm hp.1, sine_halfTurn hm hp.1]
    ring
  · simp [SchurWeights.weight_eq_zero hp]

end Erdos1045.EventualExact.FourierMultiplier
