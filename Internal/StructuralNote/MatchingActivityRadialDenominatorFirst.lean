import StructuralNote.MatchingActivityRadialSchurFirst
import StructuralNote.GeometricDenominatorEnergy

/-! Replacement of the antipodal denominator in the first center derivative,
using a coarse uniform relative chord error. -/

namespace StructuralNote.MatchingActivityRadialDenominatorFirst

open Erdos1045 Erdos1045.EventualExact Complex Configuration
open GeometricRelativeRemainder SchurSpectrum SignedPressureAngular AngularFirstEnergy
open MatchingActivityRadialSchurFirst GeometricDenominatorEnergy
open scoped BigOperators
noncomputable section

theorem quotient_denominator_factor {n : ℕ} (D w C : Points n) (hw : Function.Injective w)
    (p : Fin n × Fin n) :
    quotient C D p = quotient C w p / (1 + quotient (D - w) w p) := by
  by_cases hp : p.1 = p.2
  · simp [quotient, hp]
  have he : D p.1 - D p.2 = (w p.1 - w p.2) * (1 + quotient (D - w) w p) := by
    unfold quotient
    simp only [Pi.sub_apply]
    field_simp [sub_ne_zero.mpr (hw.ne hp)]
    ring
  unfold quotient
  rw [he, div_mul_eq_div_div]
  rfl

theorem bilinear_denominator_identity {n : ℕ} (D w C U : Points n) (hw : Function.Injective w)
    (p : Fin n × Fin n) :
    quotient C D p * quotient U D p - quotient C w p * quotient U w p =
      (quotient C w p * quotient U w p) * RelativeDenominator.factor (quotient (D - w) w p) := by
  rw [quotient_denominator_factor D w C hw, quotient_denominator_factor D w U hw]
  unfold RelativeDenominator.factor
  rw [div_mul_div_comm, ← pow_two]
  ring

theorem quadraticFirst_denominator_error {n : ℕ} (hn : 4 ≤ n) (D C U : Points n)
    {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : δ ≤ 1 / 2)
    (hD : ∀ p, ‖quotient (D - root n) (root n) p‖ ≤ δ) :
    |quadraticFirst D C U - quadraticFirst (root n) C U| ≤
      20 * δ * Real.sqrt (pairEnergy (by omega) C) * Real.sqrt (pairEnergy (by omega) U) := by
  have hw : Function.Injective (root n) := HessianAngularReference.root_injective hn
  have he : quadraticFirst D C U - quadraticFirst (root n) C U =
      -(∑ p : Fin n × Fin n, ((quotient C (root n) p * quotient U (root n) p) *
        RelativeDenominator.factor (quotient (D - root n) (root n) p)).re) := by
    simp only [quadraticFirst]
    rw [show -(∑ p : Fin n × Fin n, (quotient C D p * quotient U D p).re) -
        -(∑ p : Fin n × Fin n, (quotient C (root n) p * quotient U (root n) p).re) =
        -(∑ p : Fin n × Fin n, (quotient C D p * quotient U D p -
          quotient C (root n) p * quotient U (root n) p).re) by
      simp only [sub_re, Finset.sum_sub_distrib]
      ring]
    simp_rw [bilinear_denominator_identity D (root n) C U hw]
  rw [he, abs_neg]
  have hp (p : Fin n × Fin n) :
      |((quotient C (root n) p * quotient U (root n) p) *
        RelativeDenominator.factor (quotient (D - root n) (root n) p)).re| ≤
        10 * δ * (‖quotient C (root n) p‖ * ‖quotient U (root n) p‖) := by
    apply (abs_re_le_norm _).trans
    rw [norm_mul, norm_mul]
    have hf := (RelativeDenominator.factor_bound ((hD p).trans hsmall)).trans (mul_le_mul_of_nonneg_left (hD p) (by norm_num : (0 : ℝ) ≤ 10))
    exact (mul_le_mul_of_nonneg_left hf (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (by ring)
  have hs := (Finset.abs_sum_le_sum_abs (fun p : Fin n × Fin n => ((quotient C (root n) p * quotient U (root n) p) *
        RelativeDenominator.factor (quotient (D - root n) (root n) p)).re) Finset.univ).trans (Finset.sum_le_sum (fun p _ => hp p))
  rw [← Finset.mul_sum] at hs
  have hb := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun p => ‖quotient C (root n) p‖) (fun p => ‖quotient U (root n) p‖)
  have henergy (c : Points n) : (∑ p : Fin n × Fin n, ‖quotient c (root n) p‖ ^ 2) = 2 * pairEnergy (by omega) c := by
    rw [pairEnergy_eq_quotient_sum]
    ring
  have hall := hs.trans (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 10 * δ))
  rw [henergy, henergy, sqrt_double_product] at hall
  exact hall.trans_eq (by ring)

end
end StructuralNote.MatchingActivityRadialDenominatorFirst
