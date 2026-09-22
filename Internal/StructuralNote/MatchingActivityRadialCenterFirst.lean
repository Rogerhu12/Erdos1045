import StructuralNote.MatchingActivityRadialEnergy
import StructuralNote.GeometricRelativeRemainder

/-! Antipodal cancellation in the first center derivative, with a coarse
quadratic-energy error adequate for radial monotonicity. -/

namespace StructuralNote.MatchingActivityRadialCenterFirst

open Erdos1045 Erdos1045.EventualExact Complex Configuration
open GeometricRelativeRemainder
open scoped BigOperators
noncomputable section

theorem paired_ratio (ρ τ : ℂ) (hp : 1 + ρ ≠ 0) (hm : 1 - ρ ≠ 0) :
    (τ / (1 + ρ) + (-τ) / (1 - ρ)) / 2 = -(ρ * τ) - ρ ^ 3 * τ / (1 - ρ ^ 2) := by
  have hd : 1 - ρ ^ 2 ≠ 0 := by
    rw [show 1 - ρ ^ 2 = (1 + ρ) * (1 - ρ) by ring]
    exact mul_ne_zero hp hm
  field_simp
  ring

theorem cubic_error_bound {r : ℝ} (_hr : 0 ≤ r) (hs : r ≤ 1 / 2) {ρ τ : ℂ}
    (hρ : ‖ρ‖ ≤ r) : ‖ρ ^ 3 * τ / (1 - ρ ^ 2)‖ ≤ 2 * r ^ 2 * (‖ρ‖ * ‖τ‖) := by
  have hd := RelativeLogRemainder.denominator_lower (hρ.trans hs)
  have hdp : 0 < ‖1 - ρ ^ 2‖ := by linarith
  have hsq : ‖ρ‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hρ 2
  rw [norm_div, norm_mul, norm_pow]
  apply (div_le_iff₀ hdp).2
  have hm := mul_le_mul_of_nonneg_right hsq (mul_nonneg (norm_nonneg ρ) (norm_nonneg τ))
  have hh := mul_le_mul_of_nonneg_left hd (show 0 ≤ r ^ 2 * (‖ρ‖ * ‖τ‖) by positivity)
  nlinarith [show 0 ≤ r ^ 2 * (‖ρ‖ * ‖τ‖) by positivity]

theorem antipodal_first_error {ι : Type*} [Fintype ι] (e : Equiv.Perm ι) (ρ τ : ι → ℂ)
    (hρanti : ∀ i, ρ (e i) = -ρ i) (hτanti : ∀ i, τ (e i) = -τ i)
    {r : ℝ} (hr : 0 ≤ r) (hs : r ≤ 1 / 2) (hρ : ∀ i, ‖ρ i‖ ≤ r) :
    |(∑ i, (τ i / (1 + ρ i)).re) + (∑ i, (ρ i * τ i).re)| ≤
      2 * r ^ 2 * (Real.sqrt (∑ i, ‖ρ i‖ ^ 2) * Real.sqrt (∑ i, ‖τ i‖ ^ 2)) := by
  have hsmall (i : ι) : ‖ρ i‖ < 1 := (hρ i).trans_lt (hs.trans_lt (by norm_num))
  have hp (i : ι) := AntipodalLog.one_add_ne_zero (hsmall i)
  have hm (i : ι) : 1 - ρ i ≠ 0 := by
    simpa only [sub_eq_add_neg] using AntipodalLog.one_add_ne_zero (show ‖-ρ i‖ < 1 by simpa only [norm_neg] using hsmall i)
  have hid (i : ι) : ((τ i / (1 + ρ i)).re + (τ (e i) / (1 + ρ (e i))).re) / 2 +
      (ρ i * τ i).re = -(ρ i ^ 3 * τ i / (1 - ρ i ^ 2)).re := by
    have he := congrArg Complex.re (paired_ratio (ρ i) (τ i) (hp i) (hm i))
    simp only [add_re, div_ofNat_re, neg_re, sub_re] at he
    rw [hρanti, hτanti, ← sub_eq_add_neg]
    linarith only [he]
  have he := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hid i)
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.sum_div] at he
  have hperm : (∑ i, (τ (e i) / (1 + ρ (e i))).re) = ∑ i, (τ i / (1 + ρ i)).re :=
    Equiv.sum_comp e (fun i => (τ i / (1 + ρ i)).re)
  rw [hperm] at he
  have he' : (∑ i, (τ i / (1 + ρ i)).re) + (∑ i, (ρ i * τ i).re) =
      -(∑ i, (ρ i ^ 3 * τ i / (1 - ρ i ^ 2)).re) := by linarith only [he]
  rw [he', abs_neg]
  calc
    _ ≤ ∑ i, |(ρ i ^ 3 * τ i / (1 - ρ i ^ 2)).re| :=
      Finset.abs_sum_le_sum_abs (fun i : ι => (ρ i ^ 3 * τ i / (1 - ρ i ^ 2)).re) Finset.univ
    _ ≤ ∑ i, 2 * r ^ 2 * (‖ρ i‖ * ‖τ i‖) := Finset.sum_le_sum (fun i _ =>
      (abs_re_le_norm _).trans (cubic_error_bound hr hs (hρ i)))
    _ = 2 * r ^ 2 * ∑ i, ‖ρ i‖ * ‖τ i‖ := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => ‖ρ i‖) (fun i => ‖τ i‖)) (by positivity)

def centerFirst {n : ℕ} (D C U : Points n) : ℝ :=
  ∑ p : Fin n × Fin n, ((U p.1 - U p.2) / (configuration D C p.1 - configuration D C p.2)).re

theorem centerFirst_eq_quotients {n : ℕ} (D C U : Points n) (hD : Function.Injective D) :
    centerFirst D C U = ∑ p : Fin n × Fin n, (quotient U D p / (1 + quotient C D p)).re := by
  apply Finset.sum_congr rfl
  rintro ⟨i,j⟩ _
  by_cases hij : i = j
  · subst j
    simp [quotient]
  · rw [chord_factorization D C i j (hD.ne hij), div_mul_eq_div_div]
    rfl

/-- The linear center derivative equals its polarized quadratic form, up to
an error quadratic in the maximum center chord ratio. -/
theorem centerFirst_error {n : ℕ} (e : Equiv.Perm (Fin n)) (D C U : Points n)
    (hD : Function.Injective D) (hDa : ∀ j, D (e j) = -D j)
    (hC : ∀ j, C (e j) = C j) (hU : ∀ j, U (e j) = U j)
    {r : ℝ} (hr : 0 ≤ r) (hs : r ≤ 1 / 2) (hsmall : ∀ p, ‖quotient C D p‖ ≤ r) :
    |centerFirst D C U + ∑ p : Fin n × Fin n, (quotient C D p * quotient U D p).re| ≤
      2 * r ^ 2 * (Real.sqrt (∑ p : Fin n × Fin n, ‖quotient C D p‖ ^ 2) *
        Real.sqrt (∑ p : Fin n × Fin n, ‖quotient U D p‖ ^ 2)) := by
  rw [centerFirst_eq_quotients D C U hD]
  exact antipodal_first_error (Equiv.prodCongr e e) (quotient C D) (quotient U D)
    (quotient_antipodal e D C hDa hC) (quotient_antipodal e D U hDa hU) hr hs hsmall

end
end StructuralNote.MatchingActivityRadialCenterFirst
