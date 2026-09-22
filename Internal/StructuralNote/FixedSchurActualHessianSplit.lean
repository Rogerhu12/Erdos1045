import StructuralNote.FixedSchurPotentialDerivatives
import StructuralNote.FixedSchurQuadraticDerivatives
import StructuralNote.FixedSchurCircularCurvature
import StructuralNote.FixedSchurChosenRemainderSecond
import StructuralNote.FixedSchurObjectiveSmooth

/-! Exact decomposition of the genuine second derivative of the chosen objective.
No estimate of the second normal derivative is assumed here. -/

namespace StructuralNote.FixedSchurActualHessianSplit

open Complex Filter Erdos1045 Erdos1045.EventualExact SchurSpectrum FourierMultiplier
open CommonDomainClosure CommonFiberCanonicalDirections FixedSchurChosenPath
open FixedSchurConfigurationDerivatives FixedSchurChosenLinearization
open FixedSchurPotentialDerivatives FixedSchurQuadraticDerivatives
open FixedSchurCircularCurvature FixedSchurChosenRemainderSecond
open FixedSchurGeometricRemainderHessian FixedSchurObjectiveSmooth
open FixedSchurChart FixedSchurChartQuotients FixedSchurChartGeometry
open LogDiscriminantSecondDerivative FixedSchurObjective
open CommonFiberGeometry
open scoped BigOperators Topology

noncomputable section

theorem second_sum_four {f g h k : ℝ → ℝ} {f₂ g₂ h₂ k₂ t : ℝ}
    (hf : HasDerivAt (deriv f) f₂ t) (hg : HasDerivAt (deriv g) g₂ t)
    (hh : HasDerivAt (deriv h) h₂ t) (hk : HasDerivAt (deriv k) k₂ t)
    (hd : ∀ᶠ r in 𝓝 t, DifferentiableAt ℝ f r ∧ DifferentiableAt ℝ g r ∧
      DifferentiableAt ℝ h r ∧ DifferentiableAt ℝ k r) :
    HasDerivAt (deriv (fun r => f r + g r + h r + k r)) (f₂ + g₂ + h₂ + k₂) t := by
  apply (((hf.add hg).add hh).add hk).congr_of_eventuallyEq
  filter_upwards [hd] with r hr
  change deriv (f + g + h + k) r = _
  rw [deriv_add ((hr.1.add hr.2.1).add hr.2.2.1) hr.2.2.2,
    deriv_add (hr.1.add hr.2.1) hr.2.2.1, deriv_add hr.1 hr.2.1]
  rfl

def circularValue {m : ℕ} (θ η : Fin (2 * m) → ℝ) : ℝ :=
  second (diameterVector θ) (fun j => I * diameterVector θ j * (η j : ℂ))
    (angularAcceleration θ η)

def normalValue {m : ℕ} (hm : 0 < m) (s : FiniteBox.SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ) : ℝ :=
  quadraticSecond (coordinate hm s θ v) (chosenFirstDerivative hm s θ η v h)
    (chosenSecondDerivative hm s θ η v h)

def remainderValue {m : ℕ} (hm : 0 < m) (s : FiniteBox.SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ) : ℝ :=
  analyticSecond (centerPath hm s θ η v h 0) (angularErrorPath θ η v h 0)
    (centerVelocityPath hm s θ η v h 0) (angularVelocityPath θ η v h 0)
    (SchurLift.canonicalLift (chosenSecondDerivative hm s θ η v h))
    (angularAcceleration θ η)

theorem eventual_actual_hessian_split : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      second (configuration (by omega) s θ v) (velocityPath (by omega) s θ η v h 0)
        (acceleration (by omega) s θ η v h) =
      circularValue θ η + normalValue (by omega) s θ η v h +
        2 * pairPotential (by omega) h + remainderValue (by omega) s θ η v h := by
  filter_upwards [eventual_chosen_path_jets, eventual_quotient_properties,
    eventual_coordinate_properties, eventual_geometric_properties,
    eventual_chosen_quadratic_second, eventual_actual_remainder_second,
    eventual_actual_log_second_derivative] with m hjets hquot hcoord hgeo hquad hrem hlog
  intro hm s θ η v h hdom hdir
  let Z : ℝ → ℝ := fun t => F (configurationPath (by omega) s θ η v h t)
  let D : ℝ → ℝ := fun t => F (diameterVector (chosenParameterPath θ η v h t).1)
  let V : ℝ → ℝ := fun t => normalizedBoxEnergy (operator (2 * m))
    (chosenQPath (by omega) s θ η v h t)
  let P : ℝ → ℝ := fun t => pairPotential (by omega) (chosenParameterPath θ η v h t).2
  let R : ℝ → ℝ := fun t => newRemainder (by omega)
    (chosenParameterPath θ η v h t).1 (centerPath (by omega) s θ η v h t)
  have hn := affine_domain_near_zero (show 0 < m by omega) (θ, v) (η, h) hdom hdir
  have hj := hjets hm s θ η v h hdom hdir
  have hq := Filter.eventually_all.mpr (fun j => (hj j).1)
  have hsplit : Z =ᶠ[𝓝 0] (fun t => D t + V t + P t + R t) := by
    filter_upwards [hn] with t ht
    have he := exact_split hm (chosenParameterPath θ η v h t).1
      (chosenQPath (by omega) s θ η v h t) (chosenParameterPath θ η v h t).2
      (hcoord hm s _ _ ht).antiperiodic ht.2.2.1.1 ht.2.2.1.2.2
    change Z t - D t = V t + P t + R t at he
    linarith only [he]
  have hdiff : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ D t ∧
      DifferentiableAt ℝ V t ∧ DifferentiableAt ℝ P t ∧ DifferentiableAt ℝ R t := by
    filter_upwards [hn, hq] with t ht hqt
    have hZd := hasDerivAt_pi.mpr (configurationPath_hasDerivAt (by omega) s θ η v h t hqt)
    have hDd : DifferentiableAt ℝ (fun r => diameterVector (chosenParameterPath θ η v h r).1) t := by
      have hd (j : Fin (2 * m)) :=
        (angularErrorPath_hasDerivAt θ η v h t j).add_const (SignedPressureAngular.root (2 * m) j)
      have he : (fun r j => angularErrorPath θ η v h r j + SignedPressureAngular.root (2 * m) j) =
          (fun r => diameterVector (chosenParameterPath θ η v h r).1) := by
        funext r j
        simp only [angularErrorPath, Pi.sub_apply, sub_add_cancel]
      have hd' := hasDerivAt_pi.mpr hd
      rw [he] at hd'
      exact hd'.differentiableAt
    have hDF : DifferentiableAt ℝ D t := by
      have hF := (F_contDiffAt_of_injective (hquot hm s _ _ ht).1).differentiableAt (by simp)
      have hc := hF.comp t hDd
      exact hc
    have hZF : DifferentiableAt ℝ Z t := by
      have hF := (F_contDiffAt_of_injective (hgeo hm s _ _ ht).injective).differentiableAt (by simp)
      have hc := hF.comp t hZd.differentiableAt
      exact hc
    have hPC := (potential_hasDerivAt (show 0 < 2 * m by omega)
      (centerPath_hasDerivAt (by omega) s θ η v h t hqt)).differentiableAt
    refine ⟨hDF, (energy_hasDerivAt hqt).differentiableAt,
      (potential_hasDerivAt (by omega) (parameter_center_hasDerivAt θ η v h · t)).differentiableAt, ?_⟩
    exact (hZF.sub hDF).sub hPC
  have hd : HasDerivAt (deriv D) (circularValue θ η) 0 :=
    circular_log_second θ η v h (hquot hm s θ v hdom).1
  have hv : HasDerivAt (deriv V) (normalValue (by omega) s θ η v h) 0 :=
    hquad hm s θ η v h hdom hdir
  have hp : HasDerivAt (deriv P) (2 * pairPotential (by omega) h) 0 :=
    affine_potential_second (by omega) θ η v h
  have hr : HasDerivAt (deriv R) (remainderValue (by omega) s θ η v h) 0 :=
    hrem hm s θ η v h hdom hdir
  have hs := (second_sum_four hd hv hp hr hdiff).congr_of_eventuallyEq hsplit.deriv
  exact (hlog hm s θ η v h hdom hdir).unique hs

end
end StructuralNote.FixedSchurActualHessianSplit
