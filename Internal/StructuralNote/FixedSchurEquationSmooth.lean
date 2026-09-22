import StructuralNote.FixedSchurEquations
import StructuralNote.FixedSchurScalarSmooth

/-! Smoothness of the actual fixed-Schur equation on its open radicand domain. -/

namespace StructuralNote.FixedSchurEquationSmooth

open Erdos1045 Erdos1045.EventualExact Complex
open FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum LensClosure
open EdgeCoordinates FixedSchurData FixedSchurContraction FixedSchurEquations
open FixedSchurScalarRoot FixedSchurScalarSmooth
open CommonFiberGeometry
open scoped BigOperators Topology ContDiff
noncomputable section

abbrev SchurParameters (m : ℕ) :=
  (Fin (2 * m) → ℝ) × (Fin (2 * m) → ℂ)

abbrev SchurState (m : ℕ) := Fin (2 * m) → ℝ

def equationFamily {m : ℕ} (hm : 0 < m) (σ : Fin (2 * m) → ℝ) :
    SchurParameters m × SchurState m → SchurState m :=
  fun u => equationMap hm u.1.1 u.1.2 σ u.2

def residualFamily {m : ℕ} (hm : 0 < m) (σ : Fin (2 * m) → ℝ) :
    SchurParameters m × SchurState m → SchurState m :=
  fun u => u.2 - equationFamily hm σ u

private theorem X_contDiffAt {m : ℕ} (hm : 0 < m) {k : ℕ∞ω}
    (u : SchurParameters m × SchurState m) (j : Fin (2 * m)) :
    ContDiffAt ℝ k (fun z : SchurParameters m × SchurState m =>
      X (by omega) z.1.1 j) u := by
  change ContDiffAt ℝ k (fun z : SchurParameters m × SchurState m =>
    Complex.re (chordField (by omega) z.1.1 j)) u
  have hch : ContDiff ℝ ω (fun z : SchurParameters m × SchurState m =>
      chordField (by omega) z.1.1 j) := by
    unfold chordField CommonFiberGeometry.diameterVector LensClosure.unit
    have hcast : ContDiff ℝ ω (Complex.ofReal : ℝ → ℂ) := Complex.ofRealCLM.contDiff
    fun_prop
  have hr := Complex.reCLM.contDiff.contDiffAt.comp u hch.contDiffAt
  simpa only [Function.comp_def, Complex.reCLM_apply] using
    hr.of_le (show k ≤ ω from le_top)

private theorem Y_contDiffAt {m : ℕ} (hm : 0 < m) {k : ℕ∞ω}
    (u : SchurParameters m × SchurState m) (j : Fin (2 * m)) :
    ContDiffAt ℝ k (fun z : SchurParameters m × SchurState m =>
      Y (by omega) z.1.1 j) u := by
  change ContDiffAt ℝ k (fun z : SchurParameters m × SchurState m =>
    Complex.im (chordField (by omega) z.1.1 j)) u
  have hch : ContDiff ℝ ω (fun z : SchurParameters m × SchurState m =>
      chordField (by omega) z.1.1 j) := by
    unfold chordField CommonFiberGeometry.diameterVector LensClosure.unit
    have hcast : ContDiff ℝ ω (Complex.ofReal : ℝ → ℂ) := Complex.ofRealCLM.contDiff
    fun_prop
  have hi := Complex.imCLM.contDiff.contDiffAt.comp u hch.contDiffAt
  simpa only [Function.comp_def, Complex.imCLM_apply] using
    hi.of_le (show k ≤ ω from le_top)

private theorem tangent_contDiffAt {m : ℕ} (hm : 0 < m) {k : ℕ∞ω}
    (u : SchurParameters m × SchurState m) (j : Fin (2 * m)) :
    ContDiffAt ℝ k (fun z : SchurParameters m × SchurState m =>
      EdgeCoordinates.tangent (by omega) z.1.2 j) u := by
  unfold EdgeCoordinates.tangent
  have he : ContDiff ℝ ω (fun z : SchurParameters m × SchurState m =>
      edgeRatio (by omega) z.1.2 j) := by
    unfold edgeRatio LocalDFT.pairRatio periodize
    fun_prop
  have hr := Complex.reCLM.contDiff.contDiffAt.comp u he.contDiffAt
  have hr' := hr.of_le (show k ≤ ω from le_top)
  change ContDiffAt ℝ k (fun z : SchurParameters m × SchurState m =>
    ((2 * m : ℕ) : ℝ) • (edgeRatio (by omega) z.1.2 j).re) u
  simpa only [Function.comp_def, Complex.reCLM_apply, Nat.cast_mul, Nat.cast_ofNat] using
    hr'.const_smul (2 * m : ℝ)

private theorem J_contDiffAt {m : ℕ} (_hm : 0 < m) {k : ℕ∞ω}
    (u : SchurParameters m × SchurState m) (j : Fin (2 * m)) :
    ContDiffAt ℝ k (fun z : SchurParameters m × SchurState m =>
      J z.2 j) u := by
  change ContDiffAt ℝ k (fun z : SchurParameters m × SchurState m =>
    2 * (firstCoefficient z.2 * frame (2 * m) j).im) u
  have hf : ContDiff ℝ ω (fun z : SchurParameters m × SchurState m =>
      firstCoefficient z.2) := by
    unfold firstCoefficient frame
    have hcast : ContDiff ℝ ω (Complex.ofReal : ℝ → ℂ) := Complex.ofRealCLM.contDiff
    fun_prop
  have hp : ContDiff ℝ ω (fun z : SchurParameters m × SchurState m =>
      firstCoefficient z.2 * frame (2 * m) j) := by
    exact hf.mul contDiff_const
  have hi := Complex.imCLM.contDiff.contDiffAt.comp u hp.contDiffAt
  have hi' := hi.of_le (show k ≤ ω from le_top)
  change ContDiffAt ℝ k (fun z : SchurParameters m × SchurState m =>
    (2 : ℝ) • (firstCoefficient z.2 * frame (2 * m) j).im) u
  simpa only [Function.comp_def, Complex.imCLM_apply] using hi'.const_smul 2

theorem equationFamily_contDiffAt {m : ℕ} (hm : 0 < m)
    (σ : Fin (2 * m) → ℝ) {k : ℕ∞ω}
    (u : SchurParameters m × SchurState m)
    (hrad : ∀ j, 0 < 4 -
      (Y (by omega) u.1.1 j + σ j * epsilon (2 * m) *
        (tangent (by omega) u.1.2 j + J u.2 j)) ^ 2) :
    ContDiffAt ℝ k (equationFamily hm σ) u := by
  apply contDiffAt_pi.mpr
  intro j
  have hX := X_contDiffAt hm (k := k) u j
  have hY := Y_contDiffAt hm (k := k) u j
  have ht := tangent_contDiffAt hm (k := k) u j
  have hJ := J_contDiffAt hm (k := k) u j
  have hp : ContDiffAt ℝ k
      (fun z : SchurParameters m × SchurState m =>
        tangent (by omega) z.1.2 j + J z.2 j) u := by
    exact ht.add hJ
  change ContDiffAt ℝ k (fun z : SchurParameters m × SchurState m =>
    rootValue (σ j) (epsilon (2 * m))
      (X (by omega) z.1.1 j) (Y (by omega) z.1.1 j)
      (tangent (by omega) z.1.2 j + J z.2 j)) u
  exact rootValue_contDiffAt hX hY hp (hrad j)

theorem residualFamily_contDiffAt {m : ℕ} (hm : 0 < m)
    (σ : Fin (2 * m) → ℝ) {k : ℕ∞ω}
    (u : SchurParameters m × SchurState m)
    (hrad : ∀ j, 0 < 4 -
      (Y (by omega) u.1.1 j + σ j * epsilon (2 * m) *
        (tangent (by omega) u.1.2 j + J u.2 j)) ^ 2) :
    ContDiffAt ℝ k (residualFamily hm σ) u := by
  change ContDiffAt ℝ k
    (fun z : SchurParameters m × SchurState m =>
      z.2 - equationFamily hm σ z) u
  exact contDiffAt_snd.sub (equationFamily_contDiffAt hm σ u hrad)

end
end StructuralNote.FixedSchurEquationSmooth
