import StructuralNote.RelativeDenominator
import StructuralNote.AngularFirstEnergy
import StructuralNote.HessianAngularReference

/-! The shared-denominator correction for actual point configurations, with
the diagonal handled exactly and the bound expressed in chord energies. -/

namespace StructuralNote.GeometricDenominatorEnergy

open Erdos1045 Erdos1045.EventualExact Complex SchurSpectrum
open GeometricRelativeRemainder RelativeDenominator AngularFirstEnergy SignedPressureAngular
open scoped BigOperators
noncomputable section

theorem correction_identity {n : ℕ} (D C w : Fin n → ℂ) (hw : Function.Injective w) :
    quadratic D C - quadratic w C =
      quadraticCorrection (quotient C w) (quotient (D - w) w) := by
  have hp (p : Fin n × Fin n) :
      correction (quotient C w p) (quotient (D - w) w p) =
        quotient C D p ^ 2 - quotient C w p ^ 2 := by
    by_cases hij : p.1 = p.2
    · simp only [quotient, hij, sub_self, zero_div, correction, zero_pow (by norm_num : 2 ≠ 0), sub_self]
    · have he : quotient (D - w) w p =
          ((D p.1 - D p.2) - (w p.1 - w p.2)) / (w p.1 - w p.2) := by
        unfold quotient
        simp only [Pi.sub_apply]
        ring
      rw [he]
      exact correction_actual (C p.1 - C p.2) (D p.1 - D p.2) (w p.1 - w p.2)
        (sub_ne_zero.mpr (hw.ne hij))
  simp only [quadratic, quadraticCorrection, hp, sub_re, Finset.sum_sub_distrib]
  ring

theorem sqrt_double_product (A B : ℝ) :
    Real.sqrt (2 * A) * Real.sqrt (2 * B) = 2 * Real.sqrt A * Real.sqrt B := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ = (Real.sqrt 2 * Real.sqrt 2) * (Real.sqrt A * Real.sqrt B) := by ring
    _ = _ := by rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring

theorem correction_difference_energy {n : ℕ} (hn : 4 ≤ n) (D C C' : Fin n → ℂ)
    {r : ℝ} (hr : 0 ≤ r)
    (hC : ∀ p, ‖quotient C (root n) p‖ ≤ r)
    (hC' : ∀ p, ‖quotient C' (root n) p‖ ≤ r)
    (hD : ∀ p, ‖quotient (D - root n) (root n) p‖ ≤ 1 / 2) :
    |(quadratic D C - quadratic (root n) C) -
      (quadratic D C' - quadratic (root n) C')| ≤
      20 * r * Real.sqrt (pairEnergy (by omega) (C - C')) *
        Real.sqrt (pairEnergy (by omega) (D - root n)) := by
  have hw : Function.Injective (root n) := HessianAngularReference.root_injective hn
  rw [correction_identity D C _ hw, correction_identity D C' _ hw]
  have hh := quadratic_correction_difference hr (quotient C (root n))
    (quotient C' (root n)) (quotient (D - root n) (root n)) hC hC' hD
  have he (c : Fin n → ℂ) : (∑ p : Fin n × Fin n, ‖quotient c (root n) p‖ ^ 2) =
      2 * pairEnergy (by omega) c := by
    rw [pairEnergy_eq_quotient_sum]
    ring
  have hq : (fun p => quotient C (root n) p - quotient C' (root n) p) =
      quotient (C - C') (root n) := by
    funext p
    exact quotient_difference (root n) C C' p
  simp_rw [congrFun hq] at hh
  rw [he, he] at hh
  have hs := sqrt_double_product (pairEnergy (by omega) (C - C'))
    (pairEnergy (by omega) (D - root n))
  calc
    _ ≤ _ := hh
    _ = 10 * r * (Real.sqrt (2 * pairEnergy (by omega) (C - C')) *
        Real.sqrt (2 * pairEnergy (by omega) (D - root n))) := by ring
    _ = _ := by rw [hs]; ring

end
end StructuralNote.GeometricDenominatorEnergy
