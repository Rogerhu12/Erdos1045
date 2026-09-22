import StructuralNote.FixedSchurHessianEstimate
import StructuralNote.FixedSchurChosenSecondL2
import StructuralNote.FixedSchurObjectivePaths
import StructuralNote.HessianEnergyPositive

/-! Uniform strict curvature of the actual fixed-Schur objective. -/

namespace StructuralNote.FixedSchurStrictCurvature

open Complex Filter Erdos1045.EventualExact SchurSpectrum
open CommonDomainClosure CommonFiberCanonicalDirections CommonFiberCanonicalPaths
open FixedSchurChosenLinearization FixedSchurChosenSecondBounds
open FixedSchurConfigurationDerivatives FixedSchurHessianEstimate FixedSchurObjectivePaths
open FixedSchurEquationSmooth FixedSchurChart LogDiscriminantSecondDerivative
open scoped BigOperators Topology

noncomputable section

theorem eventual_actual_hessian_estimate : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      let E := pairEnergy (by omega) (fun j => (η j : ℂ))
      let K := E + pairEnergy (by omega) h
      let H := second (configuration (by omega) s θ v) (velocityPath (by omega) s θ η v h 0)
        (acceleration (by omega) s θ η v h)
      |H - (2 * pairPotential (by omega) h - 2 * E)| ≤
        304000000000 / Real.sqrt (2 * m : ℝ) * K ∧ H ≤ -K / 64 := by
  filter_upwards [eventual_hessian_error_of_second_moment,
    eventual_negative_hessian_of_second_moment, eventual_chosen_second_coarse]
    with m herr hneg hsecond
  intro hm s θ η v h hdom hdir
  have hq := hsecond hm s θ η v h hdom hdir
  exact ⟨herr hm s θ η v h hdom hdir hq, hneg hm s θ η v h hdom hdir hq⟩

theorem eventual_affine_strict_curvature : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega)) (x d : SchurParameters m) (t : ℝ),
      affinePath x d t ∈ FixedSchurChartSmooth.domain (by omega) →
      Admissible (by omega) d → d ≠ 0 →
      deriv (deriv (fun r => objective (by omega) s (affinePath x d r))) t < 0 := by
  filter_upwards [eventual_actual_hessian_estimate, eventual_affine_deriv2_eq] with m hbound heq
  intro hm s x d t hx hd hne
  rw [heq hm s x d t hx hd]
  have hb := (hbound hm s (affinePath x d t).1 d.1 (affinePath x d t).2 d.2 hx hd).2
  have hsplit : d.1 ≠ 0 ∨ d.2 ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hne (Prod.ext hh.1 hh.2)
  have hp := HessianEnergyPositive.total_energy_pos (show 2 ≤ 2 * m by omega)
    d.1 d.2 hd.2.1 hd.2.2.2.1 hsplit
  exact hb.trans_lt (by linarith only [hp])

end
end StructuralNote.FixedSchurStrictCurvature
