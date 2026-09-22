import StructuralNote.FixedSchurObjective
import StructuralNote.FixedSchurRemainderScalar
import StructuralNote.ActualObjectiveLoss

/-! The scalar analytic remainder is the actual objective remainder, including
the correction from the angular denominators to the regular denominators. -/

namespace StructuralNote.FixedSchurRemainderIdentity

open Erdos1045 Erdos1045.EventualExact Complex
open GeometricRelativeRemainder FixedSchurRemainderScalar
open CommonFiberGeometry FixedSchurObjective
open scoped BigOperators

noncomputable section

theorem quotient_change_background {n : ℕ} (D C w : Fin n → ℂ)
    (hw : Function.Injective w) (p : Fin n × Fin n) :
    quotient C D p = quotient C w p / (1 + quotient (D - w) w p) := by
  by_cases hij : p.1 = p.2
  · simp [quotient, hij]
  have hne := sub_ne_zero.mpr (hw.ne hij)
  have he : 1 + quotient (D - w) w p =
      (D p.1 - D p.2) / (w p.1 - w p.2) := by
    unfold quotient
    simp only [Pi.sub_apply]
    field_simp
    ring
  rw [he]
  exact (div_div_div_cancel_right₀ hne (C p.1 - C p.2)
    (D p.1 - D p.2)).symm

theorem gain_sub_quadratic_eq_sum {n : ℕ} (e : Equiv.Perm (Fin n))
    (D C w : Fin n → ℂ) (hD : Function.Injective D) (hw : Function.Injective w)
    (hDanti : ∀ i, D (e i) = -D i) (hC : ∀ i, C (e i) = C i)
    (hsmall : ∀ p, ‖quotient C D p‖ < 1) :
    gain D C - quadratic w C =
      (∑ p : Fin n × Fin n, (R (quotient C w p) (quotient (D - w) w p)).re) / 2 := by
  rw [gain_eq_sum D C hD hsmall,
    AntipodalLog.sum_antipodal_log (Equiv.prodCongr e e) (quotient C D)
      (quotient_antipodal e D C hDanti hC) hsmall]
  simp only [R, Complex.add_re, Complex.log_re, Finset.sum_add_distrib]
  simp_rw [← div_pow, ← quotient_change_background D C w hw]
  unfold quadratic
  ring

theorem newRemainder_eq_sum {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (C : Fin (2 * m) → ℂ)
    (hθ : SchurSpectrum.HalfPeriodic hm (fun j => (θ j : ℂ)))
    (hC : SchurSpectrum.HalfPeriodic hm C)
    (hD : Function.Injective (diameterVector θ))
    (hw : Function.Injective (SignedPressureAngular.root (2 * m)))
    (hsmall : ∀ p, ‖quotient C (diameterVector θ) p‖ < 1) :
    newRemainder (by omega) θ C =
      (∑ p : Fin (2 * m) × Fin (2 * m),
        (R (quotient C (SignedPressureAngular.root (2 * m)) p)
          (quotient (diameterVector θ - SignedPressureAngular.root (2 * m))
            (SignedPressureAngular.root (2 * m)) p)).re) / 2 := by
  let e := Equiv.ofBijective (FourierMultiplier.halfTurn hm)
    (SchurLift.halfTurn_involutive hm).bijective
  rw [newRemainder_eq_gain_sub_pairPotential,
    ← ActualObjectiveLoss.quadratic_eq_pairPotential (by omega) C]
  exact gain_sub_quadratic_eq_sum e _ C _ hD hw
    (diameterVector_halfTurn hm θ hθ) hC hsmall

end
end StructuralNote.FixedSchurRemainderIdentity
