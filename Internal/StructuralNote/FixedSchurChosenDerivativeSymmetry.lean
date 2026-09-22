import StructuralNote.FixedSchurChosenFirstBounds
import StructuralNote.FixedSchurLiftStability

/-! Antiperiodicity of the actual first and second chosen-coordinate derivatives,
and the resulting physical center-velocity energy estimate. -/

namespace StructuralNote.FixedSchurChosenDerivativeSymmetry

open Complex Filter Erdos1045.EventualExact
open FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum SchurLiftBounds
open CommonDomainClosure CommonFiberCanonicalPaths CommonFiberCanonical
open CommonFiberCanonicalDirections FixedSchurChart FixedSchurChosenPath
open FixedSchurChosenLinearization FixedSchurChosenFirstBounds
open scoped BigOperators Topology

noncomputable section

theorem eventual_chosen_derivatives_antiperiodic : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      FiniteBox.Antiperiodic (by omega) (chosenFirstDerivative (by omega) s θ η v h) ∧
      FiniteBox.Antiperiodic (by omega) (chosenSecondDerivative (by omega) s θ η v h) := by
  filter_upwards [eventual_coordinate_properties] with m hprops
  intro hm s θ η v h hdom hdir
  have hn := affine_domain_near_zero (show 0 < m by omega) (θ, v) (η, h) hdom hdir
  have hq : ∀ᶠ t in 𝓝 (0 : ℝ),
      FiniteBox.Antiperiodic (by omega) (chosenQPath (by omega) s θ η v h t) := by
    filter_upwards [hn] with t ht
    exact (hprops hm s _ _ ht).antiperiodic
  have he (j : Fin (2 * m)) :
      (fun t : ℝ => chosenQPath (by omega) s θ η v h t (halfTurn (by omega) j)) =ᶠ[𝓝 0]
        (fun t => -chosenQPath (by omega) s θ η v h t j) := by
    filter_upwards [hq] with t ht
    exact ht j
  constructor
  · intro j
    simpa only [chosenFirstDerivative, chosenQFirstPath, deriv.fun_neg'] using (he j).deriv_eq
  · intro j
    change deriv (deriv (fun t : ℝ =>
      chosenQPath (by omega) s θ η v h t (halfTurn (by omega) j))) 0 =
        -deriv (deriv (fun t : ℝ => chosenQPath (by omega) s θ η v h t j)) 0
    simpa only [deriv.fun_neg'] using (he j).deriv.deriv_eq

theorem eventual_center_velocity_energy : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      pairEnergy (by omega)
        (canonicalLift (chosenFirstDerivative (by omega) s θ η v h) + h) ≤
          5120002 * (pairEnergy (by omega) (fun j => (η j : ℂ)) + pairEnergy (by omega) h) := by
  filter_upwards [eventual_chosen_derivatives_antiperiodic, eventual_chosen_first_coarse]
    with m hsym hbound
  intro hm s θ η v h hdom hdir
  have hlift := canonicalLift_pairEnergy_le hm _ (hsym hm s θ η v h hdom hdir).1
  have hq := (hbound hm s θ η v h hdom hdir).1
  have hn : (1 : ℝ) ≤ 2 * m := by exact_mod_cast (show 1 ≤ 2 * m by omega)
  have hE := pairEnergy_nonneg (show 0 < 2 * m by omega) (fun j => (η j : ℂ))
  have hA := pairEnergy_nonneg (show 0 < 2 * m by omega) h
  have hq' := hq.trans (div_le_self (by positivity) hn)
  have hadd := QuadraticStability.pairEnergy_add_le (show 0 < 2 * m by omega)
    (canonicalLift (chosenFirstDerivative (by omega) s θ η v h)) h
  linarith only [hlift, hq', hadd, hE]

end
end StructuralNote.FixedSchurChosenDerivativeSymmetry
