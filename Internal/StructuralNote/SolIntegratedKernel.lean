import StructuralNote.DiscreteConvexBalance
import StructuralNote.FixedDualClassificationKernel
import EventualExact.FiniteBoxMaximum
import EventualExact.FiniteFourierLift

namespace StructuralNote.SolIntegratedKernel

open Real Finset Erdos1045.EventualExact
open FixedDualClassificationKernel DiscreteConvexBalance
open scoped BigOperators
noncomputable section

/-- The integrated finite kernel from (8.21).  Its integer argument is useful
for the discrete convexity calculation. -/
def S (n : ℕ) (r : ℤ) : ℝ :=
  (1 / 2) * ∑ p ∈ (Finset.univ.filter fun p : Fin n => SchurWeights.Active n p),
    SchurWeights.weight n p * (2 * FiniteBox.amplitude n / n) ^ 2 *
      Real.cos (2 * Real.pi * (p : ℕ) * (r : ℝ) / n) /
        Real.sin (Real.pi * (p : ℕ) / n) ^ 2

theorem active_sine_pos {n : ℕ} {p : Fin n} (hp : SchurWeights.Active n p) :
    0 < Real.sin (Real.pi * (p : ℕ) / n) := by
  rcases hp with ⟨_, hp3, hpn⟩
  have hn : 0 < n := by omega
  apply Real.sin_pos_of_pos_of_lt_pi
  · have : (0 : ℝ) < (p : ℕ) := by exact_mod_cast (show 0 < (p : ℕ) by omega)
    positivity
  · apply (div_lt_iff₀ (show (0 : ℝ) < n by positivity)).2
    have hpn : (p : ℕ) < n := p.isLt
    nlinarith [Real.pi_pos, (show ((p : ℕ) : ℝ) < n by exact_mod_cast hpn)]

theorem active_sine_ne_zero {n : ℕ} {p : Fin n} (hp : SchurWeights.Active n p) :
    Real.sin (Real.pi * (p : ℕ) / n) ^ 2 ≠ 0 :=
  pow_ne_zero 2 (active_sine_pos hp).ne'

theorem character_normSq (n p j : ℕ) :
    Complex.normSq (FourierMultiplier.character n p j) = 1 := by
  simp [FourierMultiplier.character, Complex.normSq_eq_norm_sq, norm_pow,
    Erdos1045.ClosedFourier.root_norm]

/-- Exact normalization of the discrete difference symbol. -/
theorem differenceSymbol_normSq {n : ℕ} (_hn : 0 < n) (p : Fin n) :
    Complex.normSq (FiniteFourierLift.differenceSymbol n p) =
      4 * Real.sin (Real.pi * (p : ℕ) / n) ^ 2 := by
  have hchar : Erdos1045.LocalPhase.regularRoot n ^ (p : ℕ) =
      FourierMultiplier.character n p 1 := by simp [FourierMultiplier.character]
  rw [FiniteFourierLift.differenceSymbol, hchar, FourierMultiplier.character_eq_exp]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, sub_zero, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  norm_num only [Nat.cast_one, mul_one] at ⊢
  rw [show 2 * Real.pi * (p : ℕ) / n =
      2 * (Real.pi * (p : ℕ) / n) by ring,
    Real.cos_two_mul, Real.sin_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi * (p : ℕ) / n)]

/-- The phase difference is formed in `ℝ`, so no natural-number subtraction
or truncation occurs. -/
theorem character_mul_conj_re {n : ℕ} (p : ℕ) (a b : Fin n) :
    (FourierMultiplier.character n p a *
      (starRingEnd ℂ) (FourierMultiplier.character n p b)).re =
      Real.cos (2 * Real.pi * p * ((a : ℝ) - (b : ℝ)) / n) := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  rw [show (FourierMultiplier.character n p a).re =
      FourierMultiplier.cosine n p a from rfl,
    show (FourierMultiplier.character n p b).re =
      FourierMultiplier.cosine n p b from rfl,
    show (FourierMultiplier.character n p a).im =
      FourierMultiplier.sine n p a from rfl,
    show (FourierMultiplier.character n p b).im =
      FourierMultiplier.sine n p b from rfl]
  rw [FourierMultiplier.cosine_eq_cos, FourierMultiplier.cosine_eq_cos,
    FourierMultiplier.sine_eq_sin, FourierMultiplier.sine_eq_sin]
  ring_nf
  rw [← Real.cos_sub]

theorem cosine_second_difference (x u : ℝ) :
    Real.cos (x + 2 * u) - 2 * Real.cos x + Real.cos (x - 2 * u) =
      -4 * Real.sin u ^ 2 * Real.cos x := by
  rw [Real.cos_add, Real.cos_sub, Real.cos_two_mul]
  have hu : Real.cos u ^ 2 - 1 = -Real.sin u ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq u]
  calc
    _ = 4 * Real.cos x * (Real.cos u ^ 2 - 1) := by ring
    _ = 4 * Real.cos x * (-Real.sin u ^ 2) := by rw [hu]
    _ = _ := by ring

theorem active_sum_eq_kernel (n : ℕ) (r : ℤ) :
    (1 / 2) * ∑ p ∈ (Finset.univ.filter fun p : Fin n => SchurWeights.Active n p),
        SchurWeights.weight n p * Real.cos (2 * Real.pi * (p : ℕ) * (r : ℝ) / n) =
      finiteKernel n (2 * Real.pi * (r : ℝ) / n) := by
  unfold finiteKernel
  congr 1
  have hsum : (∑ p : Fin n, SchurWeights.weight n p *
      Real.cos (p * (2 * Real.pi * (r : ℝ) / n))) =
      ∑ p ∈ (Finset.univ.filter fun p : Fin n => SchurWeights.Active n p),
        SchurWeights.weight n p * Real.cos (p * (2 * Real.pi * (r : ℝ) / n)) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p _ hp
    have hna : ¬ SchurWeights.Active n p := by simpa using hp
    simp [SchurWeights.weight_eq_zero hna]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro p _
  congr 2
  ring

theorem half_sum_second {I : Type*} [DecidableEq I] (s : Finset I) (a b c : I → ℝ) :
    (1 / 2) * (∑ i ∈ s, a i) - 2 * ((1 / 2) * (∑ i ∈ s, b i)) +
        (1 / 2) * (∑ i ∈ s, c i) =
      (1 / 2) * (∑ i ∈ s, (a i - 2 * b i + c i)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      simp only [Finset.sum_insert hx]
      linear_combination ih

theorem secondDifference_S (n : ℕ) (r : ℤ) :
    secondDifference (S n) r =
      -16 * FiniteBox.amplitude n ^ 2 / (n : ℝ) ^ 2 *
        finiteKernel n (2 * Real.pi * (r : ℝ) / n) := by
  by_cases hn : n = 0
  · subst n
    simp [S, secondDifference, finiteKernel]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp only [secondDifference, S]
  have hterm (p : Fin n) (hp : p ∈ Finset.univ.filter fun p : Fin n => SchurWeights.Active n p) :
      SchurWeights.weight n p * (2 * FiniteBox.amplitude n / n) ^ 2 *
            Real.cos (2 * Real.pi * (p : ℕ) * ((r + 1 : ℤ) : ℝ) / n) /
              Real.sin (Real.pi * (p : ℕ) / n) ^ 2 -
          2 * (SchurWeights.weight n p * (2 * FiniteBox.amplitude n / n) ^ 2 *
            Real.cos (2 * Real.pi * (p : ℕ) * (r : ℝ) / n) /
              Real.sin (Real.pi * (p : ℕ) / n) ^ 2) +
        SchurWeights.weight n p * (2 * FiniteBox.amplitude n / n) ^ 2 *
            Real.cos (2 * Real.pi * (p : ℕ) * ((r - 1 : ℤ) : ℝ) / n) /
              Real.sin (Real.pi * (p : ℕ) / n) ^ 2 =
        (-4 * (2 * FiniteBox.amplitude n / n) ^ 2) *
          (SchurWeights.weight n p *
            Real.cos (2 * Real.pi * (p : ℕ) * (r : ℝ) / n)) := by
    have hp' := (Finset.mem_filter.mp hp).2
    have hs := active_sine_ne_zero hp'
    have hc := cosine_second_difference
      (2 * Real.pi * (p : ℕ) * (r : ℝ) / n)
      (Real.pi * (p : ℕ) / n)
    have hplus : 2 * Real.pi * (p : ℕ) * ((r + 1 : ℤ) : ℝ) / n =
        2 * Real.pi * (p : ℕ) * (r : ℝ) / n +
          2 * (Real.pi * (p : ℕ) / n) := by push_cast; field_simp
    have hminus : 2 * Real.pi * (p : ℕ) * ((r - 1 : ℤ) : ℝ) / n =
        2 * Real.pi * (p : ℕ) * (r : ℝ) / n -
          2 * (Real.pi * (p : ℕ) / n) := by push_cast; field_simp
    rw [hplus, hminus]
    calc
      _ = (SchurWeights.weight n p * (2 * FiniteBox.amplitude n / n) ^ 2 /
          Real.sin (Real.pi * (p : ℕ) / n) ^ 2) *
          (Real.cos (2 * Real.pi * (p : ℕ) * (r : ℝ) / n +
              2 * (Real.pi * (p : ℕ) / n)) -
            2 * Real.cos (2 * Real.pi * (p : ℕ) * (r : ℝ) / n) +
            Real.cos (2 * Real.pi * (p : ℕ) * (r : ℝ) / n -
              2 * (Real.pi * (p : ℕ) / n))) := by ring
      _ = (SchurWeights.weight n p * (2 * FiniteBox.amplitude n / n) ^ 2 /
          Real.sin (Real.pi * (p : ℕ) / n) ^ 2) *
          (-4 * Real.sin (Real.pi * (p : ℕ) / n) ^ 2 *
            Real.cos (2 * Real.pi * (p : ℕ) * (r : ℝ) / n)) := by rw [hc]
      _ = (SchurWeights.weight n p * (2 * FiniteBox.amplitude n / n) ^ 2 *
          (-4 * Real.cos (2 * Real.pi * (p : ℕ) * (r : ℝ) / n))) *
            (Real.sin (Real.pi * (p : ℕ) / n) ^ 2 /
              Real.sin (Real.pi * (p : ℕ) / n) ^ 2) := by ring
      _ = _ := by rw [div_self hs]; ring
  rw [show (1 / 2 * (∑ p ∈ Finset.univ.filter (fun p : Fin n => SchurWeights.Active n p),
        SchurWeights.weight n p * (2 * FiniteBox.amplitude n / n) ^ 2 *
          Real.cos (2 * Real.pi * (p : ℕ) * ((r + 1 : ℤ) : ℝ) / n) /
            Real.sin (Real.pi * (p : ℕ) / n) ^ 2) -
      2 * (1 / 2 * (∑ p ∈ Finset.univ.filter (fun p : Fin n => SchurWeights.Active n p),
        SchurWeights.weight n p * (2 * FiniteBox.amplitude n / n) ^ 2 *
          Real.cos (2 * Real.pi * (p : ℕ) * (r : ℝ) / n) /
            Real.sin (Real.pi * (p : ℕ) / n) ^ 2)) +
      1 / 2 * (∑ p ∈ Finset.univ.filter (fun p : Fin n => SchurWeights.Active n p),
        SchurWeights.weight n p * (2 * FiniteBox.amplitude n / n) ^ 2 *
          Real.cos (2 * Real.pi * (p : ℕ) * ((r - 1 : ℤ) : ℝ) / n) /
            Real.sin (Real.pi * (p : ℕ) / n) ^ 2) =
      1 / 2 * (∑ p ∈ Finset.univ.filter (fun p : Fin n => SchurWeights.Active n p),
      (SchurWeights.weight n p * (2 * FiniteBox.amplitude n / n) ^ 2 *
            Real.cos (2 * Real.pi * (p : ℕ) * ((r + 1 : ℤ) : ℝ) / n) /
              Real.sin (Real.pi * (p : ℕ) / n) ^ 2 -
          2 * (SchurWeights.weight n p * (2 * FiniteBox.amplitude n / n) ^ 2 *
            Real.cos (2 * Real.pi * (p : ℕ) * (r : ℝ) / n) /
              Real.sin (Real.pi * (p : ℕ) / n) ^ 2) +
        SchurWeights.weight n p * (2 * FiniteBox.amplitude n / n) ^ 2 *
            Real.cos (2 * Real.pi * (p : ℕ) * ((r - 1 : ℤ) : ℝ) / n) /
              Real.sin (Real.pi * (p : ℕ) / n) ^ 2))) by
      exact half_sum_second _ _ _ _]
  rw [show (∑ p ∈ Finset.univ.filter (fun p : Fin n => SchurWeights.Active n p),
      (SchurWeights.weight n p * (2 * FiniteBox.amplitude n / n) ^ 2 *
            Real.cos (2 * Real.pi * (p : ℕ) * ((r + 1 : ℤ) : ℝ) / n) /
              Real.sin (Real.pi * (p : ℕ) / n) ^ 2 -
          2 * (SchurWeights.weight n p * (2 * FiniteBox.amplitude n / n) ^ 2 *
            Real.cos (2 * Real.pi * (p : ℕ) * (r : ℝ) / n) /
              Real.sin (Real.pi * (p : ℕ) / n) ^ 2) +
        SchurWeights.weight n p * (2 * FiniteBox.amplitude n / n) ^ 2 *
            Real.cos (2 * Real.pi * (p : ℕ) * ((r - 1 : ℤ) : ℝ) / n) /
              Real.sin (Real.pi * (p : ℕ) / n) ^ 2)) =
      ∑ p ∈ Finset.univ.filter (fun p : Fin n => SchurWeights.Active n p),
        (-4 * (2 * FiniteBox.amplitude n / n) ^ 2) *
          (SchurWeights.weight n p * Real.cos (2 * Real.pi * (p : ℕ) * (r : ℝ) / n)) by
      exact Finset.sum_congr rfl hterm]
  rw [← Finset.mul_sum]
  have hk := active_sum_eq_kernel n r
  have hk' : (∑ p ∈ Finset.univ.filter (fun p : Fin n => SchurWeights.Active n p),
      SchurWeights.weight n p * Real.cos (2 * Real.pi * (p : ℕ) * (r : ℝ) / n)) =
      2 * finiteKernel n (2 * Real.pi * (r : ℝ) / n) := by linarith
  rw [hk']
  field_simp
  ring

end
end StructuralNote.SolIntegratedKernel
