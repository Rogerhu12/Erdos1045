import StructuralNote.FixedSchurConfigurationDerivatives
import StructuralNote.FixedSchurGeometricRemainderHessian
import StructuralNote.FixedSchurChartRemainder

/-! The actual nonlinear remainder on the chosen branch has the geometric
second derivative, including both center and angular accelerations. -/

namespace StructuralNote.FixedSchurChosenRemainderSecond

open Complex Filter Erdos1045.EventualExact FourierMultiplier SchurLift
open CommonDomainClosure CommonFiberGeometry CommonFiberCanonicalPaths
open CommonFiberCanonical CommonFiberCanonicalDirections FixedSchurChart
open FixedSchurChosenPath FixedSchurChosenLinearization FixedSchurConfigurationDerivatives
open FixedSchurGeometricRemainderHessian FixedSchurChartQuotients FixedSchurChartRemainder
open FixedSchurObjective GeometricRelativeRemainder SignedPressureAngular
open scoped BigOperators Topology

noncomputable section

def centerPath {m : ℕ} (hm : 0 < m) (s : FiniteBox.SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ) (t : ℝ) :
    Fin (2 * m) → ℂ :=
  FixedSchurLinear.center (chosenQPath hm s θ η v h t) (chosenParameterPath θ η v h t).2

def angularErrorPath {m : ℕ} (θ η : Fin (2 * m) → ℝ)
    (v h : Fin (2 * m) → ℂ) (t : ℝ) : Fin (2 * m) → ℂ :=
  diameterVector (chosenParameterPath θ η v h t).1 - root (2 * m)

def angularVelocityPath {m : ℕ} (θ η : Fin (2 * m) → ℝ)
    (v h : Fin (2 * m) → ℂ) (t : ℝ) (j : Fin (2 * m)) : ℂ :=
  I * diameterVector (chosenParameterPath θ η v h t).1 j * (η j : ℂ)

def angularAcceleration {m : ℕ} (θ η : Fin (2 * m) → ℝ)
    (j : Fin (2 * m)) : ℂ := -diameterVector θ j * (η j : ℂ) ^ 2

theorem centerPath_hasDerivAt {m : ℕ} (hm : 0 < m) (s : FiniteBox.SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ) (t : ℝ)
    (hq : ∀ j, HasDerivAt (fun r => chosenQPath hm s θ η v h r j)
      (chosenQFirstPath hm s θ η v h j t) t) (j : Fin (2 * m)) :
    HasDerivAt (fun r => centerPath hm s θ η v h r j)
      (centerVelocityPath hm s θ η v h t j) t :=
  (canonicalLift_hasDerivAt hq j).add (parameter_center_hasDerivAt θ η v h j t)

theorem angularErrorPath_hasDerivAt {m : ℕ} (θ η : Fin (2 * m) → ℝ)
    (v h : Fin (2 * m) → ℂ) (t : ℝ) (j : Fin (2 * m)) :
    HasDerivAt (fun r => angularErrorPath θ η v h r j)
      (angularVelocityPath θ η v h t j) t := by
  have hd₀ := (LensIncrementDerivatives.unit_path_hasDerivAt
    (parameter_angle_hasDerivAt θ η v h j t)).const_mul (character (2 * m) 1 j)
  have hd := hd₀.sub_const (root (2 * m) j)
  apply hd.congr_deriv
  unfold angularVelocityPath diameterVector
  ring

theorem centerVelocityPath_hasDerivAt {m : ℕ} (hm : 0 < m) (s : FiniteBox.SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (hq : ∀ j, HasDerivAt (chosenQFirstPath hm s θ η v h j)
      (chosenQSecond hm s θ η v h j) 0) (j : Fin (2 * m)) :
    HasDerivAt (fun r => centerVelocityPath hm s θ η v h r j)
      (canonicalLift (chosenSecondDerivative hm s θ η v h) j) 0 :=
  (canonicalLift_hasDerivAt hq j).add_const (h j)

theorem angularVelocityPath_hasDerivAt {m : ℕ} (θ η : Fin (2 * m) → ℝ)
    (v h : Fin (2 * m) → ℂ) (j : Fin (2 * m)) :
    HasDerivAt (fun r => angularVelocityPath θ η v h r j) (angularAcceleration θ η j) 0 := by
  have hd₀ := ((LensIncrementDerivatives.unit_path_hasDerivAt
    (parameter_angle_hasDerivAt θ η v h j 0)).const_mul (character (2 * m) 1 j)).const_mul I
  have hd := hd₀.mul_const (η j : ℂ)
  apply hd.congr_deriv
  simp only [chosenParameterPath, affinePath, zero_smul, add_zero]
  unfold angularAcceleration diameterVector
  ring_nf
  simp only [I_sq]
  ring

theorem eventual_actual_remainder_second : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      HasDerivAt (deriv (fun t => newRemainder (by omega)
        (chosenParameterPath θ η v h t).1 (centerPath (by omega) s θ η v h t)))
        (analyticSecond (centerPath (by omega) s θ η v h 0) (angularErrorPath θ η v h 0)
          (centerVelocityPath (by omega) s θ η v h 0) (angularVelocityPath θ η v h 0)
          (canonicalLift (chosenSecondDerivative (by omega) s θ η v h))
          (angularAcceleration θ η)) 0 := by
  filter_upwards [eventual_chosen_path_jets, eventual_quotient_properties,
    eventual_remainder_identity] with m hjets hquot hid
  intro hm s θ η v h hdom hdir
  have hj := hjets hm s θ η v h hdom hdir
  have hq := Filter.eventually_all.mpr (fun j => (hj j).1)
  have hn := affine_domain_near_zero (show 0 < m by omega) (θ, v) (η, h) hdom hdir
  have hfirst : ∀ᶠ t in 𝓝 (0 : ℝ),
      (∀ j, HasDerivAt (fun r => centerPath (by omega) s θ η v h r j)
        (centerVelocityPath (by omega) s θ η v h t j) t) ∧
      (∀ j, HasDerivAt (fun r => angularErrorPath θ η v h r j)
        (angularVelocityPath θ η v h t j) t) ∧
      (∀ p, ‖quotient (centerPath (by omega) s θ η v h t) (root (2 * m)) p‖ ≤ 1 / 4) ∧
      (∀ p, ‖quotient (angularErrorPath θ η v h t) (root (2 * m)) p‖ ≤ 1 / 4) := by
    filter_upwards [hq, hn] with t ht htdom
    have hb := hquot hm s _ _ htdom
    exact ⟨centerPath_hasDerivAt (by omega) s θ η v h t ht,
      angularErrorPath_hasDerivAt θ η v h t, hb.2.1, hb.2.2.1⟩
  have hd := analytic_second_derivative hfirst
    (centerVelocityPath_hasDerivAt (by omega) s θ η v h (fun j => (hj j).2.2.1))
    (angularVelocityPath_hasDerivAt θ η v h)
  have he : (fun t : ℝ => newRemainder (by omega)
      (chosenParameterPath θ η v h t).1 (centerPath (by omega) s θ η v h t)) =ᶠ[𝓝 0]
      (fun t => analyticRemainder (centerPath (by omega) s θ η v h t)
        (angularErrorPath θ η v h t)) := by
    filter_upwards [hn] with t ht
    simpa only [centerPath, chosenQPath, chosenParameterPath, analyticRemainder,
      angularErrorPath, Complex.re_sum] using hid hm s _ _ ht
  exact hd.congr_of_eventuallyEq he.deriv

end
end StructuralNote.FixedSchurChosenRemainderSecond
