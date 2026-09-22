import StructuralNote.AngularFirstEnergy

/-! The genuine log-discriminant derivative, with no derivative estimate as input. -/

noncomputable section
open scoped BigOperators

namespace StructuralNote.ActualAngularFirst

open Erdos1045 Erdos1045.EventualExact Complex
open Configuration AngularObjectiveCurvature GeometricRelativeRemainder
open AngularAntipodalFirst AngularFirstEnergy SignedPressureAngular
open SchurSpectrum DiscreteEnergy FourierMultiplier

theorem root_injective {n : ℕ} (hn : 0 < n) : Function.Injective (root n) := by
  intro i j he
  exact Fin.ext ((ClosedFourier.regularRoot_primitive hn).pow_inj i.isLt j.isLt he)

theorem root_halfTurn {m : ℕ} (hm : 0 < m) (j : Fin (2 * m)) :
    root (2 * m) (halfTurn hm j) = -root (2 * m) j := by
  simpa only [character, mul_one, root] using character_halfTurn hm (by decide : Odd 1) j

/-- The first angular derivative is quadratic in the center perturbation after
the antipodal terms are paired. The quartic quantity is the actual chord sum. -/
theorem angularFirst_halfPeriodic_bound {m : ℕ} (hm : 0 < m)
    (c : Fin (2 * m) → ℂ) (θ : Fin (2 * m) → ℝ)
    (hc : HalfPeriodic hm c) (hθ : ∀ j, θ (halfTurn hm j) = θ j)
    (hsmall : ∀ p, ‖quotient c (root (2 * m)) p‖ ≤ 1 / 2) :
    |angularFirst θ (configuration (root (2 * m)) c) 0| ≤
      8 * Real.sqrt (AntipodalLog.fourthEnergy (2 * m) (periodize (by omega) c) +
        ‖c‖ ^ 2 * pairEnergy (by omega) c) * Real.sqrt (realEnergy (by omega) θ) := by
  let e := Equiv.ofBijective (halfTurn hm) (SchurLift.halfTurn_involutive hm).bijective
  have h := angularFirst_antipodal e (root (2 * m)) c θ (root_injective (by omega))
    (root_halfTurn hm) hc hθ (fun p => (hsmall p).trans_lt (by norm_num))
  rw [angularFirst_eq_vertex_sum (root (2 * m)), regular_vertex_sum_zero (by omega), sub_zero] at h
  rw [h]
  exact angular_error_sum_bound (by omega) c θ hsmall

theorem actual_derivative_bound {m : ℕ} (hm : 0 < m)
    (c : Fin (2 * m) → ℂ) (θ : Fin (2 * m) → ℝ)
    (hc : HalfPeriodic hm c) (hθ : ∀ j, θ (halfTurn hm j) = θ j)
    (hsmall : ∀ p, ‖quotient c (root (2 * m)) p‖ ≤ 1 / 2) :
    HasDerivAt (angularLogDiscriminant θ (configuration (root (2 * m)) c))
        (angularFirst θ (configuration (root (2 * m)) c) 0) 0 ∧
      |deriv (angularLogDiscriminant θ (configuration (root (2 * m)) c)) 0| ≤
        8 * Real.sqrt (AntipodalLog.fourthEnergy (2 * m) (periodize (by omega) c) +
          ‖c‖ ^ 2 * pairEnergy (by omega) c) * Real.sqrt (realEnergy (by omega) θ) := by
  have hinj := configuration_injective (root (2 * m)) c (root_injective (by omega))
    (fun p => (hsmall p).trans_lt (by norm_num))
  have hd := angularLogDiscriminant_hasDerivAt θ (configuration (root (2 * m)) c) 0
    (by simpa only [angularOrbit, zero_mul, ofReal_zero, exp_zero, one_mul] using hinj)
  refine ⟨hd, ?_⟩
  rw [hd.deriv]
  exact angularFirst_halfPeriodic_bound hm c θ hc hθ hsmall

end StructuralNote.ActualAngularFirst
