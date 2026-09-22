import StructuralNote.FixedSchurChosenLinearization
import StructuralNote.ClosedSourceIntegration
import StructuralNote.LogDiscriminantSecondDerivative

/-! True configuration derivatives in fixed-Schur coordinates. The center
acceleration is the canonical lift of q'', with no missing frame term. -/

namespace StructuralNote.FixedSchurConfigurationDerivatives

open Complex Filter Erdos1045 Erdos1045.EventualExact
open FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open CommonDomainClosure CommonFiberGeometry CommonFiberCanonicalPaths
open CommonFiberCanonicalDirections CommonFiberCanonical
open FixedSchurLinear FixedSchurEdgeGeometry FixedSchurChart FixedSchurChartGeometry
open FixedSchurChosenPath FixedSchurChosenLinearization ClosedSourceIntegration
open LogDiscriminantSecondDerivative
open scoped BigOperators Topology

noncomputable section

theorem firstCoefficient_hasDerivAt {n : ℕ} {q : ℝ → Fin n → ℝ}
    {q' : Fin n → ℝ} {x : ℝ}
    (hq : ∀ j, HasDerivAt (fun s => q s j) (q' j) x) :
    HasDerivAt (fun s => firstCoefficient (q s)) (firstCoefficient q') x := by
  exact (HasDerivAt.fun_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
    (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x (hq j)).mul_const
      ((starRingEnd ℂ) (frame n j)))).div_const (n : ℂ)

theorem canonicalLift_hasDerivAt {n : ℕ} {q : ℝ → Fin n → ℝ}
    {q' : Fin n → ℝ} {x : ℝ}
    (hq : ∀ j, HasDerivAt (fun s => q s j) (q' j) x) (j : Fin n) :
    HasDerivAt (fun s => canonicalLift (q s) j) (canonicalLift q' j) x := by
  have hi (k : Fin n) : HasDerivAt
      (fun s => SchurLift.increment (q s) k) (SchurLift.increment q' k) x := by
    have hc := (firstCoefficient_hasDerivAt hq).mul_const (frame n k)
    have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hc
    have ht := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x him
    have hreal := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x (hq k)
    have hs := ((hreal.const_mul ((2 * Real.sin (Real.pi / n) / n : ℝ) : ℂ)).add
      (ht.const_mul (I * ((4 * Real.sin (Real.pi / n) / n : ℝ) : ℂ)))).const_mul
        (frame n k)
    simpa only [SchurLift.increment, Pi.add_apply, Function.comp_apply,
      Complex.ofRealCLM_apply, Complex.imCLM_apply] using hs
  exact integral_hasDerivAt hi j

def configurationPath {m : ℕ} (hm : 0 < m) (s : FiniteBox.SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ) (t : ℝ) :
    Fin (2 * m) → ℂ :=
  FixedSchurChart.configuration hm s (chosenParameterPath θ η v h t).1
    (chosenParameterPath θ η v h t).2

def centerVelocityPath {m : ℕ} (hm : 0 < m) (s : FiniteBox.SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ) (t : ℝ) :
    Fin (2 * m) → ℂ :=
  canonicalLift (fun j => chosenQFirstPath hm s θ η v h j t) + h

def velocityPath {m : ℕ} (hm : 0 < m) (s : FiniteBox.SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ) (t : ℝ)
    (j : Fin (2 * m)) : ℂ :=
  I * diameterVector (chosenParameterPath θ η v h t).1 j * (η j : ℂ) +
    centerVelocityPath hm s θ η v h t j

def acceleration {m : ℕ} (hm : 0 < m) (s : FiniteBox.SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (j : Fin (2 * m)) : ℂ :=
  -diameterVector θ j * (η j : ℂ) ^ 2 +
    canonicalLift (chosenSecondDerivative hm s θ η v h) j

theorem parameter_angle_hasDerivAt {m : ℕ}
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ) (j : Fin (2 * m))
    (t : ℝ) : HasDerivAt (fun r => (chosenParameterPath θ η v h r).1 j) (η j) t := by
  simpa [chosenParameterPath, affinePath] using
    ((hasDerivAt_id t).mul_const (η j)).const_add (θ j)

theorem parameter_center_hasDerivAt {m : ℕ}
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ) (j : Fin (2 * m))
    (t : ℝ) : HasDerivAt (fun r => (chosenParameterPath θ η v h r).2 j) (h j) t := by
  simpa [chosenParameterPath, affinePath] using
    ((hasDerivAt_id t).smul_const (h j)).const_add (v j)

theorem configurationPath_hasDerivAt {m : ℕ} (hm : 0 < m)
    (s : FiniteBox.SignPattern hm) (θ η : Fin (2 * m) → ℝ)
    (v h : Fin (2 * m) → ℂ) (t : ℝ)
    (hq : ∀ j, HasDerivAt (fun r => chosenQPath hm s θ η v h r j)
      (chosenQFirstPath hm s θ η v h j t) t) (j : Fin (2 * m)) :
    HasDerivAt (fun r => configurationPath hm s θ η v h r j)
      (velocityPath hm s θ η v h t j) t := by
  have hd := (LensIncrementDerivatives.unit_path_hasDerivAt
    (parameter_angle_hasDerivAt θ η v h j t)).const_mul (character (2 * m) 1 j)
  have hc := (canonicalLift_hasDerivAt hq j).add (parameter_center_hasDerivAt θ η v h j t)
  apply (hd.add hc).congr_deriv
  unfold velocityPath centerVelocityPath diameterVector
  simp only [Pi.add_apply]
  ring

theorem velocityPath_hasDerivAt {m : ℕ} (hm : 0 < m)
    (s : FiniteBox.SignPattern hm) (θ η : Fin (2 * m) → ℝ)
    (v h : Fin (2 * m) → ℂ)
    (hq : ∀ j, HasDerivAt (chosenQFirstPath hm s θ η v h j)
      (chosenQSecond hm s θ η v h j) 0) (j : Fin (2 * m)) :
    HasDerivAt (fun r => velocityPath hm s θ η v h r j)
      (acceleration hm s θ η v h j) 0 := by
  have hd₀ := ((LensIncrementDerivatives.unit_path_hasDerivAt
    (parameter_angle_hasDerivAt θ η v h j 0)).const_mul (character (2 * m) 1 j)).const_mul I
  have hd := hd₀.mul_const (η j : ℂ)
  have hc := (canonicalLift_hasDerivAt hq j).add_const (h j)
  apply (hd.add hc).congr_deriv
  simp only [chosenParameterPath, affinePath, zero_smul, add_zero]
  unfold acceleration diameterVector chosenSecondDerivative
  ring_nf
  simp only [I_sq]
  ring

theorem eventual_actual_log_second_derivative : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      HasDerivAt (deriv (fun t => Real.log (Configuration.discriminant
        (configurationPath (by omega) s θ η v h t))))
        (second (FixedSchurChart.configuration (by omega) s θ v)
          (velocityPath (by omega) s θ η v h 0)
          (acceleration (by omega) s θ η v h)) 0 := by
  filter_upwards [eventual_chosen_path_jets, eventual_geometric_properties]
    with m hjets hgeo
  intro hm s θ η v h hdom hdir
  have hj := hjets hm s θ η v h hdom hdir
  have hq : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ j,
      HasDerivAt (fun r => chosenQPath (by omega) s θ η v h r j)
        (chosenQFirstPath (by omega) s θ η v h j t) t :=
    Filter.eventually_all.mpr (fun j => (hj j).1)
  have hz : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ j,
      HasDerivAt (fun r => configurationPath (by omega) s θ η v h r j)
        (velocityPath (by omega) s θ η v h t j) t := by
    filter_upwards [hq] with t ht
    exact configurationPath_hasDerivAt (by omega) s θ η v h t ht
  have hv := velocityPath_hasDerivAt (by omega) s θ η v h (fun j => (hj j).2.2.1)
  have hi : Function.Injective (configurationPath (by omega) s θ η v h 0) := by
    simpa only [configurationPath, chosenParameterPath, affinePath, zero_smul, add_zero]
      using (hgeo hm s θ v hdom).injective
  simpa only [configurationPath, chosenParameterPath, affinePath, zero_smul, add_zero]
    using log_second_derivative hz hv hi

end
end StructuralNote.FixedSchurConfigurationDerivatives
