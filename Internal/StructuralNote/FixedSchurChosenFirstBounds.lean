import StructuralNote.FixedSchurChosenLinearization
import StructuralNote.FixedSchurDerivativeScales

/-! Quantitative bounds for the true derivative of the chosen fixed-Schur
chart. In particular the sharp L2 estimate is Lemma 9.3, equation (9.16). -/

namespace StructuralNote.FixedSchurChosenFirstBounds

open Filter Complex Erdos1045.EventualExact FiniteBox SchurSpectrum SchurLiftBounds
open CommonDomainClosure CommonDomainRadius CommonFiberCanonicalDirections
open FixedSchurFirstSource FixedSchurFirstDerivativeBounds FixedSchurFirstSourceSup
open FixedSchurDerivativeScales FixedSchurChosenLinearization
open scoped BigOperators Topology

noncomputable section

theorem eventual_chosen_first_l2 :
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      Real.sqrt (meanSquare (chosenFirstDerivative (by omega) s θ η v h)) ≤ 2000 *
        (Real.sqrt (pairEnergy (by omega) (fun j => (η j : ℂ))) / Real.sqrt (2 * m : ℝ) +
          (logOrder (2 * m) : ℝ) * Real.sqrt (1 + Real.log (2 * m : ℝ)) *
            Real.sqrt (pairEnergy (by omega) h) / ((2 * m : ℝ) * Real.sqrt (2 * m : ℝ))) := by
  filter_upwards [eventual_chosen_normalLinearizations, eventual_first_solution_l2]
    with m hlin hbound
  intro hm s θ η v h hdom hdir
  exact hbound hm s θ η v h hdom hdir.2.1 _
    (hlin hm s θ η v h hdom hdir).1

theorem eventual_chosen_first_sup_sq :
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      ‖chosenFirstDerivative (by omega) s θ η v h‖ ^ 2 ≤
        200000 * pairEnergy (by omega) (fun j => (η j : ℂ)) +
        96 * betaBudget (2 * m) ^ 2 * pairEnergy (by omega) h / (2 * m : ℝ) ^ 2 := by
  filter_upwards [eventual_chosen_normalLinearizations, eventual_first_solution_sup_sq]
    with m hlin hbound
  intro hm s θ η v h hdom hdir
  exact hbound hm s θ η v h hdom hdir.2.1 _
    (hlin hm s θ η v h hdom hdir).1

theorem eventual_chosen_first_coarse :
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      meanSquare (chosenFirstDerivative (by omega) s θ η v h) ≤ 80000 *
        (pairEnergy (by omega) (fun j => (η j : ℂ)) + pairEnergy (by omega) h) / (2 * m : ℝ) ∧
      ‖chosenFirstDerivative (by omega) s θ η v h‖ ^ 2 ≤ 200000 *
        (pairEnergy (by omega) (fun j => (η j : ℂ)) + pairEnergy (by omega) h) := by
  filter_upwards [eventual_chosen_normalLinearizations, eventual_first_solution_coarse]
    with m hlin hbound
  intro hm s θ η v h hdom hdir
  exact hbound hm s θ η v h hdom hdir.2.1 _
    (hlin hm s θ η v h hdom hdir).1

end
end StructuralNote.FixedSchurChosenFirstBounds
