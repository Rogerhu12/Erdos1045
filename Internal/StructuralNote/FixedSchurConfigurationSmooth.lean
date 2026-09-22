import StructuralNote.FixedSchurEquationSmooth

/-! Global analytic smoothness of the actual fixed-Schur configuration family. -/

namespace StructuralNote.FixedSchurConfigurationSmooth

open Complex
open Erdos1045 Erdos1045.EventualExact
open FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum LensClosure
open CommonFiberGeometry EdgeCoordinates FixedSchurLinear FixedSchurEdgeGeometry
open StructuralNote.FixedSchurEquationSmooth
open scoped BigOperators Topology ContDiff
noncomputable section

abbrev ConfigurationDomain (m : ℕ) :=
  SchurParameters m × SchurState m

def configurationFamily {m : ℕ} (_hm : 0 < m) :
    ConfigurationDomain m → (Fin (2 * m) → ℂ) :=
  fun u => vertex u.1.1 (center u.2 u.1.2)

private theorem integral_contDiff_omega (n : ℕ) :
    ContDiff ℝ ω (@FiniteFourierLift.integral n) := by
  unfold FiniteFourierLift.integral integralCoefficients FourierMultiplier.synthesis
    FourierMultiplier.coefficient
  apply contDiff_pi.mpr
  intro j
  apply ContDiff.sum
  intro p _
  by_cases hp : p.val = 0
  · simp only [if_pos hp, zero_mul]
    exact contDiff_const
  · simp only [if_neg hp]
    fun_prop

private theorem firstCoefficient_contDiff_omega {m : ℕ} :
    ContDiff ℝ ω (fun u : ConfigurationDomain m => firstCoefficient u.2) := by
  unfold firstCoefficient frame
  have hcast : ContDiff ℝ ω (Complex.ofReal : ℝ → ℂ) := Complex.ofRealCLM.contDiff
  fun_prop

private theorem increment_contDiff_omega {m : ℕ} :
    ContDiff ℝ ω (fun u : ConfigurationDomain m =>
      SchurLift.increment u.2) := by
  apply contDiff_pi.mpr
  intro j
  have hf := firstCoefficient_contDiff_omega (m := m)
  have hp : ContDiff ℝ ω (fun u : ConfigurationDomain m =>
      firstCoefficient u.2 * frame (2 * m) j) := by
    exact hf.mul contDiff_const
  have hi : ContDiff ℝ ω (fun u : ConfigurationDomain m =>
      (firstCoefficient u.2 * frame (2 * m) j).im) := by
    simpa only [Function.comp_def, Complex.imCLM_apply] using
      Complex.imCLM.contDiff.comp hp
  have hcast : ContDiff ℝ ω (Complex.ofReal : ℝ → ℂ) := Complex.ofRealCLM.contDiff
  unfold SchurLift.increment
  fun_prop

private theorem canonicalLift_contDiff_omega {m : ℕ} :
    ContDiff ℝ ω (fun u : ConfigurationDomain m => canonicalLift u.2) := by
  have hi := integral_contDiff_omega (2 * m)
  have hinc := increment_contDiff_omega (m := m)
  simpa only [SchurLift.canonicalLift, Function.comp_def] using hi.comp hinc

private theorem center_contDiff_omega {m : ℕ} :
    ContDiff ℝ ω (fun u : ConfigurationDomain m =>
      center u.2 u.1.2) := by
  have hc := canonicalLift_contDiff_omega (m := m)
  have hv : ContDiff ℝ ω (fun u : ConfigurationDomain m => u.1.2) := by
    fun_prop
  simpa only [FixedSchurLinear.center, Pi.add_apply] using hc.add hv

private theorem diameter_contDiff_omega {m : ℕ} (j : Fin (2 * m)) :
    ContDiff ℝ ω (fun u : ConfigurationDomain m => diameterVector u.1.1 j) := by
  unfold diameterVector LensClosure.unit
  have hcast : ContDiff ℝ ω (Complex.ofReal : ℝ → ℂ) := Complex.ofRealCLM.contDiff
  fun_prop

theorem configurationFamily_contDiff {m : ℕ} (hm : 0 < m) :
    ContDiff ℝ ω (configurationFamily hm) := by
  apply contDiff_pi.mpr
  intro j
  have hd := diameter_contDiff_omega (m := m) j
  have hc := center_contDiff_omega (m := m)
  have hev : ContDiff ℝ ω
      (fun C : (Fin (2 * m) → ℂ) => C j) := contDiff_apply ℝ ℂ j
  have hcj := hev.comp hc
  change ContDiff ℝ ω (fun u : ConfigurationDomain m =>
    diameterVector u.1.1 j + center u.2 u.1.2 j)
  exact hd.add hcj

end
end StructuralNote.FixedSchurConfigurationSmooth
