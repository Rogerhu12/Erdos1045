import EventualExact.FiniteMultiplier

/-! Exact inversion and mean-zero discrete integration on a finite complex grid. -/

noncomputable section

open scoped BigOperators

namespace Erdos1045.EventualExact.FiniteFourierLift

open Complex FourierMultiplier

theorem synthesis_coefficient {n : ℕ} (hn : 0 < n) (f : Fin n → ℂ) (j : Fin n) :
    synthesis (coefficient f) j = f j := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [synthesis, coefficient, div_mul_eq_mul_div, Finset.sum_mul,
    ← Finset.sum_div]
  rw [Finset.sum_comm]
  have ht (k : Fin n) :
      (∑ p : Fin n, f k * (starRingEnd ℂ) (character n p k) * character n p j) =
        f k * (if j = k then (n : ℂ) else 0) := by
    have he := character_orthogonality hn j k
    have hc (p k : Fin n) : character n p k = character n k p := by
      unfold character
      rw [Nat.mul_comm]
    simp_rw [hc]
    rw [← he, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros
    ring
  simp_rw [ht]
  simp [hn0]

theorem coefficient_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (coefficient (n := n)) := by
  intro f g h
  funext j
  rw [← synthesis_coefficient hn f j, h, synthesis_coefficient hn]

theorem coefficient_zero {n : ℕ} [NeZero n] (f : Fin n → ℂ) :
    coefficient f 0 = (∑ j, f j) / n := by
  simp [coefficient, character]

theorem sum_synthesis {n : ℕ} (hn : 0 < n) (a : Fin n → ℂ) :
    (∑ j, synthesis a j) = (n : ℂ) * a ⟨0, hn⟩ := by
  let : NeZero n := ⟨hn.ne'⟩
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have h := coefficient_synthesis hn a 0
  rw [coefficient_zero] at h
  have hz : (0 : Fin n) = ⟨0, hn⟩ := rfl
  rw [hz] at h
  exact (div_eq_iff hn0).mp h |>.trans (mul_comm _ _)

def successor {n : ℕ} (hn : 0 < n) (j : Fin n) : Fin n :=
  ⟨(j.val + 1) % n, Nat.mod_lt _ hn⟩

def difference {n : ℕ} (hn : 0 < n) (f : Fin n → ℂ) (j : Fin n) : ℂ :=
  f (successor hn j) - f j

def differenceSymbol (n p : ℕ) : ℂ := LocalPhase.regularRoot n ^ p - 1

theorem character_successor {n : ℕ} (hn : 0 < n) (p : Fin n) (j : Fin n) :
    character n p (successor hn j) = character n p j * LocalPhase.regularRoot n ^ p.val := by
  change character n p ((j.val + 1) % n) = _
  rw [character_mod hn, character_add]
  simp [character]

theorem difference_synthesis {n : ℕ} (hn : 0 < n) (a : Fin n → ℂ) (j : Fin n) :
    difference hn (synthesis a) j = synthesis (fun p => a p * differenceSymbol n p) j := by
  simp only [difference, synthesis, character_successor hn, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  unfold differenceSymbol
  ring

theorem coefficient_difference {n : ℕ} (hn : 0 < n) (f : Fin n → ℂ) (p : Fin n) :
    coefficient (difference hn f) p = coefficient f p * differenceSymbol n p := by
  have hf : f = synthesis (coefficient f) := by
    funext j
    exact (synthesis_coefficient hn f j).symm
  have hd : difference hn f = synthesis (fun p => coefficient f p * differenceSymbol n p) := by
    conv_lhs => rw [hf]
    funext j
    exact difference_synthesis hn _ j
  rw [hd, coefficient_synthesis hn]

theorem differenceSymbol_ne_zero {n : ℕ} (hn : 0 < n) (p : Fin n) (hp : p.val ≠ 0) :
    differenceSymbol n p ≠ 0 := by
  exact sub_ne_zero.mpr (LocalDFT.regularRoot_power_ne_one hn (by omega) p.isLt)

/-- The zero frequency is fixed at zero, removing precisely the additive constant. -/
def integralCoefficients {n : ℕ} (d : Fin n → ℂ) (p : Fin n) : ℂ :=
  if p.val = 0 then 0 else coefficient d p / differenceSymbol n p

def integral {n : ℕ} (d : Fin n → ℂ) : Fin n → ℂ := synthesis (integralCoefficients d)

theorem integral_mean_zero {n : ℕ} (hn : 0 < n) (d : Fin n → ℂ) :
    (∑ j, integral d j) = 0 := by
  rw [integral, sum_synthesis hn]
  simp [integralCoefficients]

theorem difference_integral {n : ℕ} (hn : 0 < n) (d : Fin n → ℂ)
    (hd : ∑ j, d j = 0) : difference hn (integral d) = d := by
  have he : (fun p : Fin n => integralCoefficients d p * differenceSymbol n p) =
      coefficient d := by
    funext p
    by_cases hp : p.val = 0
    · have hp0 : p = ⟨0, hn⟩ := Fin.ext hp
      subst p
      simp [integralCoefficients, coefficient, character, hd]
    · simp [integralCoefficients, hp, differenceSymbol_ne_zero hn p hp]
  funext j
  change difference hn (synthesis (integralCoefficients d)) j = d j
  rw [difference_synthesis, he, synthesis_coefficient hn]

theorem integral_unique {n : ℕ} (hn : 0 < n) (d f : Fin n → ℂ)
    (hmean : ∑ j, f j = 0) (hd : difference hn f = d) : f = integral d := by
  apply coefficient_injective hn
  funext p
  rw [integral, coefficient_synthesis hn]
  have hcoef : coefficient d p = coefficient f p * differenceSymbol n p := by
    rw [← hd, coefficient_difference hn]
  by_cases hp : p.val = 0
  · have hp0 : p = ⟨0, hn⟩ := Fin.ext hp
    subst p
    simp [integralCoefficients, coefficient, character, hmean]
  · rw [integralCoefficients, if_neg hp, hcoef,
      mul_div_cancel_right₀ _ (differenceSymbol_ne_zero hn p hp)]

end Erdos1045.EventualExact.FiniteFourierLift
