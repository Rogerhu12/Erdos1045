import StructuralNote.RelativeLogRemainder
import Erdos1045.LocalConfiguration

/-! The relative remainder bound for the actual distance-product objective on
two configurations with a common antipodal component, as required in §9.5. -/

noncomputable section
open scoped BigOperators

namespace StructuralNote.GeometricRelativeRemainder

open Erdos1045 Erdos1045.Configuration Erdos1045.EventualExact
open RelativeLogRemainder

def quotient {n : ℕ} (C D : Points n) (p : Fin n × Fin n) : ℂ :=
  (C p.1 - C p.2) / (D p.1 - D p.2)

def configuration {n : ℕ} (D C : Points n) : Points n := fun i => D i + C i

def gain {n : ℕ} (D C : Points n) : ℝ :=
  Real.log (discriminant (configuration D C)) - Real.log (discriminant D)

def quadratic {n : ℕ} (D C : Points n) : ℝ :=
  -(∑ p : Fin n × Fin n, (quotient C D p ^ 2).re) / 2

def objectiveRemainder {n : ℕ} (D C : Points n) : ℝ := gain D C - quadratic D C

theorem chord_factorization {n : ℕ} (D C : Points n) (i j : Fin n)
    (hij : D i ≠ D j) :
    configuration D C i - configuration D C j =
      (D i - D j) * (1 + quotient C D (i, j)) := by
  unfold configuration quotient
  field_simp [sub_ne_zero.mpr hij]
  ring

theorem configuration_injective {n : ℕ} (D C : Points n) (hD : Function.Injective D)
    (hsmall : ∀ p, ‖quotient C D p‖ < 1) : Function.Injective (configuration D C) := by
  intro i j he
  by_contra hij
  have hd := hD.ne hij
  have hz := mul_ne_zero (sub_ne_zero.mpr hd) (AntipodalLog.one_add_ne_zero (hsmall (i, j)))
  rw [← chord_factorization D C i j hd, he, sub_self] at hz
  exact hz rfl

theorem logarithmic_chord_gain {n : ℕ} (D C : Points n) (hD : Function.Injective D)
    (hsmall : ∀ p, ‖quotient C D p‖ < 1) (i j : Fin n) :
    Real.log ‖configuration D C i - configuration D C j‖ - Real.log ‖D i - D j‖ =
      Real.log ‖1 + quotient C D (i, j)‖ := by
  by_cases hij : i = j
  · subst j
    simp [quotient]
  · have hd := hD.ne hij
    rw [chord_factorization D C i j hd, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hd))
        (norm_ne_zero_iff.mpr (AntipodalLog.one_add_ne_zero (hsmall (i, j))))]
    ring

theorem gain_eq_sum {n : ℕ} (D C : Points n) (hD : Function.Injective D)
    (hsmall : ∀ p, ‖quotient C D p‖ < 1) :
    gain D C = ∑ p : Fin n × Fin n, Real.log ‖1 + quotient C D p‖ := by
  rw [gain, LocalConfiguration.logDiscriminant_eq_sum _ (configuration_injective D C hD hsmall),
    LocalConfiguration.logDiscriminant_eq_sum D hD, Fintype.sum_prod_type]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun j _ => logarithmic_chord_gain D C hD hsmall i j)

theorem objectiveRemainder_eq {n : ℕ} (D C : Points n) (hD : Function.Injective D)
    (hsmall : ∀ p, ‖quotient C D p‖ < 1) :
    objectiveRemainder D C = pairedRemainder (quotient C D) := by
  rw [objectiveRemainder, gain_eq_sum D C hD hsmall]
  unfold quadratic pairedRemainder
  ring

theorem quotient_antipodal {n : ℕ} (e : Equiv.Perm (Fin n)) (D C : Points n)
    (hD : ∀ i, D (e i) = -D i) (hC : ∀ i, C (e i) = C i) (p : Fin n × Fin n) :
    quotient C D ((Equiv.prodCongr e e) p) = -quotient C D p := by
  change (C (e p.1) - C (e p.2)) / (D (e p.1) - D (e p.2)) = _
  rw [hC, hC, hD, hD, show -D p.1 - -D p.2 = -(D p.1 - D p.2) by ring, div_neg]
  rfl

theorem quotient_difference {n : ℕ} (D C C' : Points n) (p : Fin n × Fin n) :
    quotient C D p - quotient C' D p = quotient (fun i => C i - C' i) D p := by
  unfold quotient
  rw [← sub_div]
  congr 1
  ring

/-- The genuine log-product remainder difference, including injectivity of the
two perturbed configurations as a consequence of the small chord quotients. -/
theorem actual_remainder_difference {n : ℕ} (e : Equiv.Perm (Fin n))
    (D C C' : Points n) (hD : Function.Injective D)
    (hDanti : ∀ i, D (e i) = -D i)
    (hC : ∀ i, C (e i) = C i) (hC' : ∀ i, C' (e i) = C' i)
    {r : ℝ} (hr : 0 ≤ r) (hrsmall : r ≤ 1 / 2)
    (hsmall : ∀ p, ‖quotient C D p‖ ≤ r) (hsmall' : ∀ p, ‖quotient C' D p‖ ≤ r) :
    |objectiveRemainder D C - objectiveRemainder D C'| ≤
      (3 / 2 : ℝ) * r ^ 3 * ∑ p : Fin n × Fin n, ‖quotient (fun i => C i - C' i) D p‖ := by
  have hs : ∀ p, ‖quotient C D p‖ < 1 :=
    fun p => lt_of_le_of_lt ((hsmall p).trans hrsmall) (by norm_num)
  have hs' : ∀ p, ‖quotient C' D p‖ < 1 :=
    fun p => lt_of_le_of_lt ((hsmall' p).trans hrsmall) (by norm_num)
  rw [objectiveRemainder_eq D C hD hs, objectiveRemainder_eq D C' hD hs']
  have hh := paired_remainder_difference (Equiv.prodCongr e e) hr hrsmall
    (quotient C D) (quotient C' D)
    (quotient_antipodal e D C hDanti hC) (quotient_antipodal e D C' hDanti hC') hsmall hsmall'
  simpa only [quotient_difference] using hh

end StructuralNote.GeometricRelativeRemainder
