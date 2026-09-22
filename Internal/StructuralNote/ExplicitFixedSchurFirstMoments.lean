import StructuralNote.ExplicitFixedSchurHessianGeometry
import StructuralNote.ExplicitCanonicalEntryObjectivePaths
/-! First moments and center velocity at the explicit fixed-Schur order. -/
namespace StructuralNote.ExplicitFixedSchurFirstMoments
open Filter Complex Erdos1045.EventualExact FiniteBox SchurSpectrum SchurLiftBounds
open CommonDomainClosure CommonDomainRadius CommonFiberCanonicalDirections
open FixedSchurFirstSource FixedSchurFirstDerivativeBounds FixedSchurFirstSourceSup
open FixedSchurDerivativeScales FixedSchurChosenLinearization
open scoped BigOperators Topology
open Complex Filter Erdos1045.EventualExact
open FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum SchurLiftBounds
open CommonDomainClosure CommonFiberCanonicalPaths CommonFiberCanonical
open CommonFiberCanonicalDirections FixedSchurChart FixedSchurChosenPath
open FixedSchurChosenLinearization FixedSchurChosenFirstBounds
noncomputable section
theorem chosen_first_l2 {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      Real.sqrt (meanSquare (chosenFirstDerivative (by omega) s θ η v h)) ≤ 2000 *
        (Real.sqrt (pairEnergy (by omega) (fun j => (η j : ℂ))) / Real.sqrt (2 * m : ℝ) +
          (logOrder (2 * m) : ℝ) * Real.sqrt (1 + Real.log (2 * m : ℝ)) *
            Real.sqrt (pairEnergy (by omega) h) / ((2 * m : ℝ) * Real.sqrt (2 * m : ℝ))) := by
  have hlin := ExplicitCanonicalEntryObjectivePaths.chosen_normalLinearizations hN
  have hbound := ExplicitFixedSchurCoefficients.first_solution_l2 hN
  clear hN
  intro hm s θ η v h hdom hdir
  exact hbound hm s θ η v h hdom hdir.2.1 _
    (hlin hm s θ η v h hdom hdir).1

theorem chosen_first_sup_sq {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      ‖chosenFirstDerivative (by omega) s θ η v h‖ ^ 2 ≤
        200000 * pairEnergy (by omega) (fun j => (η j : ℂ)) +
        96 * betaBudget (2 * m) ^ 2 * pairEnergy (by omega) h / (2 * m : ℝ) ^ 2 := by
  have hlin := ExplicitCanonicalEntryObjectivePaths.chosen_normalLinearizations hN
  have hbound := ExplicitFixedSchurCoefficients.first_solution_sup_sq hN
  clear hN
  intro hm s θ η v h hdom hdir
  exact hbound hm s θ η v h hdom hdir.2.1 _
    (hlin hm s θ η v h hdom hdir).1

theorem chosen_first_coarse {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      meanSquare (chosenFirstDerivative (by omega) s θ η v h) ≤ 80000 *
        (pairEnergy (by omega) (fun j => (η j : ℂ)) + pairEnergy (by omega) h) / (2 * m : ℝ) ∧
      ‖chosenFirstDerivative (by omega) s θ η v h‖ ^ 2 ≤ 200000 *
        (pairEnergy (by omega) (fun j => (η j : ℂ)) + pairEnergy (by omega) h) := by
  have hlin := ExplicitCanonicalEntryObjectivePaths.chosen_normalLinearizations hN
  have hbound := ExplicitFixedSchurCoefficients.first_solution_coarse hN
  clear hN
  intro hm s θ η v h hdom hdir
  exact hbound hm s θ η v h hdom hdir.2.1 _
    (hlin hm s θ η v h hdom hdir).1

theorem center_velocity_energy {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) : ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      pairEnergy (by omega)
        (canonicalLift (chosenFirstDerivative (by omega) s θ η v h) + h) ≤
          5120002 * (pairEnergy (by omega) (fun j => (η j : ℂ)) + pairEnergy (by omega) h) := by
  have hsym := ExplicitFixedSchurHessianGeometry.chosen_derivatives_antiperiodic hN
  have hbound := chosen_first_coarse hN
  clear hN
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
end StructuralNote.ExplicitFixedSchurFirstMoments
