import StructuralNote.FixedSchurRemainderIdentity
import StructuralNote.FixedSchurRemainderEnergy
import StructuralNote.GeometricDenominatorEnergy

/-! A relative energy estimate for the actual remainder, retaining the shared
angular displacement in an L2 factor. -/

namespace StructuralNote.FixedSchurRemainderGeometry

open Complex Erdos1045 Erdos1045.EventualExact
open SchurSpectrum CommonFiberGeometry GeometricRelativeRemainder SignedPressureAngular
open FixedSchurRemainderScalar FixedSchurRemainderIdentity FixedSchurRemainderEnergy
open FixedSchurObjective AngularFirstEnergy
open scoped BigOperators

noncomputable section

theorem actual_remainder_difference_energy {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (C C' : Fin (2 * m) → ℂ)
    (hθ : HalfPeriodic (by omega) (fun j => (θ j : ℂ)))
    (hC : HalfPeriodic (by omega) C) (hC' : HalfPeriodic (by omega) C')
    (hD : Function.Injective (diameterVector θ))
    (hsmall : ∀ p, ‖quotient C (diameterVector θ) p‖ < 1)
    (hsmall' : ∀ p, ‖quotient C' (diameterVector θ) p‖ < 1)
    {U : ℝ} (hU : 0 ≤ U) (hUquarter : U ≤ 1 / 4)
    (hu : ∀ p, ‖quotient C (root (2 * m)) p‖ ≤ U)
    (hv : ∀ p, ‖quotient C' (root (2 * m)) p‖ ≤ U)
    (hx : ∀ p, ‖quotient (diameterVector θ - root (2 * m)) (root (2 * m)) p‖ ≤ 1 / 4) :
    |newRemainder (by omega) θ C - newRemainder (by omega) θ C'| ≤
      32 * (U * Real.sqrt (pairEnergy (by omega) (diameterVector θ - root (2 * m))) +
        U ^ 2 * (Real.sqrt (pairEnergy (by omega) C) + Real.sqrt (pairEnergy (by omega) C'))) *
        Real.sqrt (pairEnergy (by omega) (C - C')) := by
  have hw := HessianAngularReference.root_injective (show 4 ≤ 2 * m by omega)
  rw [newRemainder_eq_sum (by omega) θ C hθ hC hD hw hsmall,
    newRemainder_eq_sum (by omega) θ C' hθ hC' hD hw hsmall',
    ← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), ← Finset.sum_sub_distrib]
  let u := quotient C (root (2 * m))
  let v := quotient C' (root (2 * m))
  let x := quotient (diameterVector θ - root (2 * m)) (root (2 * m))
  have hs := sum_norm_R_difference_le u v x hU hUquarter hu hv hx
  have hre : |∑ p, ((R (u p) (x p)).re - (R (v p) (x p)).re)| ≤
      ∑ p, ‖R (u p) (x p) - R (v p) (x p)‖ := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact Finset.sum_le_sum (fun p _ => by
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm (R (u p) (x p) - R (v p) (x p)))
  have he (c : Fin (2 * m) → ℂ) :
      (∑ p, ‖quotient c (root (2 * m)) p‖ ^ 2) = 2 * pairEnergy (by omega) c := by
    rw [pairEnergy_eq_quotient_sum]
    ring
  have hdiff (p : Fin (2 * m) × Fin (2 * m)) :
      u p - v p = quotient (C - C') (root (2 * m)) p :=
    quotient_difference _ C C' p
  dsimp only [u, v, x] at hs
  simp_rw [show ∀ p, quotient C (root (2 * m)) p - quotient C' (root (2 * m)) p =
      quotient (C - C') (root (2 * m)) p from hdiff] at hs
  rw [he, he, he, he] at hs
  have hbound := div_le_div_of_nonneg_right (hre.trans hs) (by norm_num : (0 : ℝ) ≤ 2)
  apply hbound.trans_eq
  simp only [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have htwo : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  calc
    _ = 16 * (Real.sqrt 2 * Real.sqrt 2) *
        (U * Real.sqrt (pairEnergy (by omega) (diameterVector θ - root (2 * m))) +
          U ^ 2 * (Real.sqrt (pairEnergy (by omega) C) + Real.sqrt (pairEnergy (by omega) C'))) *
          Real.sqrt (pairEnergy (by omega) (C - C')) := by ring
    _ = _ := by rw [htwo]; ring

end
end StructuralNote.FixedSchurRemainderGeometry
