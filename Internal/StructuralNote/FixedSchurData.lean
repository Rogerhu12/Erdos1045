import StructuralNote.CommonFiberGeometry
import StructuralNote.EdgeCoordinates
import StructuralNote.CommonFiberNormalProjectionScaled

/-! Actual edge data for the fixed-Schur coordinates of the rewritten paper.
The complex chord field avoids choosing a branch at the end of the grid. -/

namespace StructuralNote.FixedSchurData

open Real Complex Erdos1045.EventualExact FourierMultiplier FiniteFourierLift
open SchurLift SchurSpectrum EdgeCoordinates CommonClosureEnergy CommonFiberGeometry
noncomputable section

def epsilon (n : ℕ) : ℝ := 2 * Real.sin (Real.pi / n) / n

def chordField {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) (j : Fin n) : ℂ :=
  (starRingEnd ℂ) (frame n j) * (diameterVector θ j + diameterVector θ (successor hn j))

def X {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) (j : Fin n) : ℝ := (chordField hn θ j).re
def Y {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) (j : Fin n) : ℝ := (chordField hn θ j).im

theorem epsilon_pos {n : ℕ} (hn : 2 ≤ n) : 0 < epsilon n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  apply div_pos _ hnR
  apply mul_pos (by norm_num)
  apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
  apply (div_lt_iff₀ hnR).mpr
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [Real.pi_pos]

theorem epsilon_inv {n : ℕ} (hn : 2 ≤ n) :
    (epsilon n)⁻¹ = CommonFiberNormalProjectionScaled.scale n := by
  unfold epsilon CommonFiberNormalProjectionScaled.scale
  field_simp

theorem epsilon_amplitude {n : ℕ} (hn : 2 ≤ n) :
    epsilon n * FiniteBox.amplitude n = 2 - 2 * Real.cos (Real.pi / n) := by
  have h := BoxLensLift.radius_identity hn
  simpa only [BoxLensLift.radius, BoxLensLift.angle, epsilon, mul_sub, mul_one] using h.symm

theorem conj_frame_mul (n : ℕ) (j : Fin n) :
    (starRingEnd ℂ) (frame n j) * frame n j = 1 := by
  rw [mul_comm, Complex.mul_conj, frame_normSq]
  rfl

theorem norm_frame (n : ℕ) (j : Fin n) : ‖frame n j‖ = 1 := by
  have h := frame_normSq n j
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (frame n j)]

theorem chordField_halfTurn {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (hθ : HalfPeriodic hm (fun j => (θ j : ℂ))) (j : Fin (2 * m)) :
    chordField (by omega) θ (halfTurn hm j) = chordField (by omega) θ j := by
  unfold chordField
  rw [frame_halfTurn hm, ← halfTurn_successor, diameterVector_halfTurn hm θ hθ,
    diameterVector_halfTurn hm θ hθ]
  simp only [map_neg]
  ring

theorem X_halfTurn {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (hθ : HalfPeriodic hm (fun j => (θ j : ℂ))) (j : Fin (2 * m)) :
    X (by omega) θ (halfTurn hm j) = X (by omega) θ j := by
  simp only [X, chordField_halfTurn hm θ hθ]

theorem Y_halfTurn {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (hθ : HalfPeriodic hm (fun j => (θ j : ℂ))) (j : Fin (2 * m)) :
    Y (by omega) θ (halfTurn hm j) = Y (by omega) θ j := by
  simp only [Y, chordField_halfTurn hm θ hθ]

theorem chordField_halfIndex {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (j : Fin m) :
    chordField (by omega) θ (CommonClosureEnergy.halfIndex j) =
      LensClosure.unit (angleAverage (by omega) θ (CommonClosureEnergy.halfIndex j)) *
        (2 * Real.cos (halfAngle hm θ j) : ℝ) := by
  unfold chordField
  rw [diameter_sum_half hm θ]
  have hf : frame (2 * m) (CommonClosureEnergy.halfIndex j) = LensClosure.unit (LensClosure.midpoint m j) :=
    BoxLensLift.frame_halfIndex j
  rw [hf, phase, unit_add]
  have hu : (starRingEnd ℂ) (LensClosure.unit (LensClosure.midpoint m j)) *
      LensClosure.unit (LensClosure.midpoint m j) = 1 := by
    rw [← hf]
    exact conj_frame_mul _ _
  rw [← mul_assoc, ← mul_assoc, hu, one_mul]

theorem X_halfIndex {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (j : Fin m) :
    X (by omega) θ (CommonClosureEnergy.halfIndex j) =
      2 * Real.cos (halfAngle hm θ j) * Real.cos (angleAverage (by omega) θ (CommonClosureEnergy.halfIndex j)) := by
  simp only [X, chordField_halfIndex hm θ, mul_re, LensClosure.unit_re,
    ofReal_re, ofReal_im, mul_zero, sub_zero]
  ring

theorem Y_halfIndex {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (j : Fin m) :
    Y (by omega) θ (CommonClosureEnergy.halfIndex j) =
      2 * Real.cos (halfAngle hm θ j) * Real.sin (angleAverage (by omega) θ (CommonClosureEnergy.halfIndex j)) := by
  simp only [Y, chordField_halfIndex hm θ, mul_im, LensClosure.unit_im,
    ofReal_re, ofReal_im, mul_zero, zero_add]
  ring

theorem framed_crossing {n : ℕ} (hn : 0 < n) (θ q p σ : Fin n → ℝ) (j : Fin n) :
    (starRingEnd ℂ) (frame n j) *
      (diameterVector θ j + diameterVector θ (successor hn j) + (σ j : ℂ) * edgeIncrement q p j) =
      ((X hn θ j + σ j * epsilon n * q j : ℝ) : ℂ) +
        I * ((Y hn θ j + σ j * epsilon n * p j : ℝ) : ℂ) := by
  have hedge : (starRingEnd ℂ) (frame n j) * ((σ j : ℂ) * edgeIncrement q p j) =
      (σ j : ℂ) * (epsilon n : ℂ) * ((q j : ℂ) + I * (p j : ℂ)) := by
    unfold edgeIncrement
    change _ = (σ j : ℂ) * ((2 * Real.sin (Real.pi / n) / n : ℝ) : ℂ) * _
    calc
      _ = ((starRingEnd ℂ) (frame n j) * frame n j) *
          ((σ j : ℂ) * ((2 * Real.sin (Real.pi / n) / n : ℝ) : ℂ) *
            ((q j : ℂ) + I * (p j : ℂ))) := by ring
      _ = _ := by rw [conj_frame_mul, one_mul]
  rw [mul_add, hedge]
  change chordField hn θ j + _ = _
  have hc := Complex.re_add_im (chordField hn θ j)
  simp only [X, Y, ofReal_add, ofReal_mul]
  linear_combination hc.symm

theorem selected_crossing_norm_sq {n : ℕ} (hn : 0 < n) (θ q p σ : Fin n → ℝ) (j : Fin n) :
    ‖diameterVector θ j + diameterVector θ (successor hn j) + (σ j : ℂ) * edgeIncrement q p j‖ ^ 2 =
      (X hn θ j + σ j * epsilon n * q j) ^ 2 +
        (Y hn θ j + σ j * epsilon n * p j) ^ 2 := by
  have h := congrArg (fun z : ℂ => ‖z‖ ^ 2) (framed_crossing hn θ q p σ j)
  rw [norm_mul, Complex.norm_conj, norm_frame, one_mul] at h
  rw [h, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, zero_mul,
    one_mul, sub_zero, add_zero, add_im, mul_im, zero_add]
  ring

end
end StructuralNote.FixedSchurData
