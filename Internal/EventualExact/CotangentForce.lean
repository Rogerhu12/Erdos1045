import EventualExact.ForceAlgebra

/-!
# The actual circle force

The identity below is equation (2.20) of the manuscript. The separation
hypothesis merely says that two distinct indices do not have angles equal
modulo a full turn; no critical-point or smallness hypothesis is used.
-/

namespace Erdos1045.EventualExact

open scoped BigOperators

noncomputable section

def circleCot (t : ℝ) : ℝ := Real.cos t / Real.sin t

theorem circleCot_neg (t : ℝ) : circleCot (-t) = -circleCot t := by
  simp only [circleCot, Real.cos_neg, Real.sin_neg, div_neg]

theorem circleCot_zero : circleCot 0 = 0 := by simp [circleCot]

/-- The scalar trigonometric identity behind the three-point cancellation. -/
theorem circleCot_add_identity {a b : ℝ}
    (ha : Real.sin a ≠ 0) (hb : Real.sin b ≠ 0)
    (hab : Real.sin (a + b) ≠ 0) :
    circleCot a * circleCot (a + b) - circleCot a * circleCot b +
      circleCot (a + b) * circleCot b = -1 := by
  unfold circleCot
  field_simp
  rw [Real.sin_add, Real.cos_add]
  ring

def circleInteraction {ι : Type*} (θ : ι → ℝ) (i j : ι) : ℝ :=
  circleCot ((θ i - θ j) / 2)

theorem circleInteraction_skew {ι : Type*} (θ : ι → ℝ) (i j : ι) :
    circleInteraction θ j i = -circleInteraction θ i j := by
  unfold circleInteraction
  rw [show (θ j - θ i) / 2 = -((θ i - θ j) / 2) by ring, circleCot_neg]

@[simp] theorem circleInteraction_self {ι : Type*} (θ : ι → ℝ) (i : ι) :
    circleInteraction θ i i = 0 := by simp [circleInteraction, circleCot_zero]

theorem circleInteraction_triple {ι : Type*} (θ : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → Real.sin ((θ i - θ j) / 2) ≠ 0)
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    circleInteraction θ i j * circleInteraction θ i k +
      circleInteraction θ j i * circleInteraction θ j k +
      circleInteraction θ k i * circleInteraction θ k j = -1 := by
  have hangle : (θ i - θ j) / 2 + (θ j - θ k) / 2 = (θ i - θ k) / 2 := by ring
  have ht := circleCot_add_identity (hsep i j hij) (hsep j k hjk)
    (by rw [hangle]; exact hsep i k hik)
  rw [hangle] at ht
  rw [circleInteraction_skew θ i j, circleInteraction_skew θ i k,
    circleInteraction_skew θ j k]
  simpa [circleInteraction, sub_eq_add_neg] using ht

section Finite

variable {ι : Type*} [Fintype ι]

def circleForce (θ : ι → ℝ) (i : ι) : ℝ :=
  (∑ j, circleInteraction θ i j) / Fintype.card ι

/-- The diagonal is omitted because the cosecant has a pole there. -/
def circleCosecantEnergy (θ : ι → ℝ) : ℝ := by
  classical
  exact ∑ i, ∑ j, if i = j then 0 else 1 / Real.sin ((θ i - θ j) / 2) ^ 2

omit [Fintype ι] in
theorem circleInteraction_sq {θ : ι → ℝ} {i j : ι}
    (h : Real.sin ((θ i - θ j) / 2) ≠ 0) :
    circleInteraction θ i j ^ 2 = 1 / Real.sin ((θ i - θ j) / 2) ^ 2 - 1 := by
  unfold circleInteraction circleCot
  rw [div_pow]
  apply (eq_sub_iff_add_eq).mpr
  apply (div_add_one (pow_ne_zero 2 h)).trans
  rw [Real.cos_sq_add_sin_sq]

theorem circleInteraction_square_sum (θ : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → Real.sin ((θ i - θ j) / 2) ≠ 0) :
    (∑ i, ∑ j, circleInteraction θ i j ^ 2) = circleCosecantEnergy θ -
      (Fintype.card ι : ℝ) * (Fintype.card ι - 1) := by
  classical
  have hpoint (i j : ι) : circleInteraction θ i j ^ 2 =
      (if i = j then 0 else 1 / Real.sin ((θ i - θ j) / 2) ^ 2) -
        (if i = j then 0 else 1) := by
    by_cases hij : i = j
    · subst j
      simp
    · simpa [hij] using circleInteraction_sq (hsep i j hij)
  simp_rw [hpoint, Finset.sum_sub_distrib]
  congr 1
  have hcomplement (i : ι) : (∑ j : ι, if i = j then (0 : ℝ) else 1) =
      Fintype.card ι - 1 := by
    have hp (j : ι) : (if i = j then (0 : ℝ) else 1) =
        1 - (if i = j then 1 else 0) := by split_ifs <;> norm_num
    simp_rw [hp, Finset.sum_sub_distrib]
    simp
  simp_rw [hcomplement]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Equation (2.20), stated for an arbitrary finite nonempty index type. -/
theorem circleForce_square_identity [Nonempty ι] (θ : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → Real.sin ((θ i - θ j) / 2) ≠ 0) :
    (Fintype.card ι : ℝ) ^ 2 * (∑ i, circleForce θ i ^ 2) =
      circleCosecantEnergy θ -
        (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) ^ 2 - 1) / 3 := by
  have h := finite_force_square_identity (circleInteraction θ)
    (circleInteraction_skew θ) (fun _ _ _ => circleInteraction_triple θ hsep)
  rw [circleInteraction_square_sum θ hsep] at h
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hnorm : (Fintype.card ι : ℝ) ^ 2 * (∑ i, circleForce θ i ^ 2) =
      ∑ i, (∑ j, circleInteraction θ i j) ^ 2 := by
    simp only [circleForce, div_pow, ← Finset.sum_div]
    field_simp
  rw [hnorm, h]
  ring

/-- The equally spaced value is a lower bound for the actual cosecant energy. -/
theorem circleCosecantEnergy_lower [Nonempty ι] (θ : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → Real.sin ((θ i - θ j) / 2) ≠ 0) :
    (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) ^ 2 - 1) / 3 ≤
      circleCosecantEnergy θ := by
  have h := circleForce_square_identity θ hsep
  have hnonneg : 0 ≤ (Fintype.card ι : ℝ) ^ 2 * (∑ i, circleForce θ i ^ 2) :=
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  linarith

/-- Equality in the energy bound is exactly the vanishing of every circle force. -/
theorem circleCosecantEnergy_eq_iff [Nonempty ι] (θ : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → Real.sin ((θ i - θ j) / 2) ≠ 0) :
    circleCosecantEnergy θ =
      (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) ^ 2 - 1) / 3 ↔
        ∀ i, circleForce θ i = 0 := by
  have h := circleForce_square_identity θ hsep
  constructor
  · intro heq
    rw [heq, sub_self] at h
    have hn : (Fintype.card ι : ℝ) ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 (by exact_mod_cast Fintype.card_ne_zero)
    have hz := (mul_eq_zero.mp h).resolve_left hn
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) => sq_nonneg (circleForce θ i))).mp hz
    intro i
    exact sq_eq_zero_iff.mp (hi i (Finset.mem_univ i))
  · intro hz
    simp only [hz, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero, mul_zero] at h
    linarith

end Finite

/-- The manuscript's formula with its explicit polygon order `n`. -/
theorem circleForce_square_identity_fin {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ)
    (hsep : ∀ i j, i ≠ j → Real.sin ((θ i - θ j) / 2) ≠ 0) :
    (n : ℝ) ^ 2 * (∑ i, circleForce θ i ^ 2) =
      circleCosecantEnergy θ - (n : ℝ) * ((n : ℝ) ^ 2 - 1) / 3 := by
  let : NeZero n := ⟨by omega⟩
  simpa only [Fintype.card_fin] using circleForce_square_identity θ hsep

end

end Erdos1045.EventualExact
