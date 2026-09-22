import StructuralNote.FixedSchurData
import StructuralNote.FixedSchurDomainSmallness
import StructuralNote.CommonFiberNonlocalFrames

/-! The radial component of a fixed-Schur step keeps the sharp quadratic
leading term. Tangential displacement enters only with the angle average. -/

namespace StructuralNote.FixedSchurRadialAlgebra

open Complex Erdos1045.EventualExact FourierMultiplier FiniteFourierLift SchurLift
open EdgeCoordinates FixedSchurData FixedSchurDomainSmallness
open CommonClosureEnergy CommonFiberNonlocalFrames CommonFiberNonlocalProjection

noncomputable section

theorem radial_edgeIncrement {n : ℕ} (hn : 0 < n)
    (θ q p : Fin n → ℝ) (j : Fin n) :
    radial (meanFrame hn θ j) (edgeIncrement q p j) =
      epsilon n * (q j * Real.cos (angleAverage hn θ j) +
        p j * Real.sin (angleAverage hn θ j)) := by
  have hcomplex : (starRingEnd ℂ) (meanFrame hn θ j) * edgeIncrement q p j =
      (epsilon n : ℂ) * (starRingEnd ℂ) (LensClosure.unit (angleAverage hn θ j)) *
        ((q j : ℂ) + I * (p j : ℂ)) := by
    unfold meanFrame edgeIncrement
    change (starRingEnd ℂ) (frame n j * _) *
      ((epsilon n : ℂ) * frame n j * _) = _
    rw [map_mul]
    calc
      _ = ((starRingEnd ℂ) (frame n j) * frame n j) *
          ((epsilon n : ℂ) * (starRingEnd ℂ) (LensClosure.unit (angleAverage hn θ j)) *
            ((q j : ℂ) + I * (p j : ℂ))) := by ring
      _ = _ := by rw [conj_frame_mul, one_mul]
  unfold radial
  rw [hcomplex]
  simp only [mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im,
    I_re, I_im, conj_re, conj_im, LensClosure.unit_re, LensClosure.unit_im]
  ring

theorem radial_edgeIncrement_bound {n : ℕ} (hn : 2 ≤ n)
    (θ q p : Fin n → ℝ) {R P S : ℝ} (j : Fin n)
    (hq : |q j| ≤ FiniteBox.amplitude n + R)
    (hp : |p j| ≤ P) (hθ : |angleAverage (by omega) θ j| ≤ S) :
    |radial (meanFrame (by omega) θ j) (edgeIncrement q p j)| ≤
      (Real.pi / n) ^ 2 + epsilon n * R + epsilon n * P * S := by
  have hε := (epsilon_pos hn).le
  have hc : |q j * Real.cos (angleAverage (by omega) θ j)| ≤
      FiniteBox.amplitude n + R := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)).trans
      (by simpa using hq)
  have hs : |p j * Real.sin (angleAverage (by omega) θ j)| ≤ P * S := by
    rw [abs_mul]
    exact mul_le_mul hp ((Real.abs_sin_le_abs).trans hθ) (abs_nonneg _)
      ((abs_nonneg _).trans hp)
  have hcos := CommonFiberNormalProjection.cos_zero_error (Real.pi / n)
  have ha : epsilon n * FiniteBox.amplitude n ≤ (Real.pi / n) ^ 2 := by
    rw [epsilon_amplitude hn]
    have habs := (neg_le_abs (Real.cos (Real.pi / n) - 1)).trans hcos
    linarith
  rw [radial_edgeIncrement, abs_mul, abs_of_nonneg hε]
  calc
    _ ≤ epsilon n * (FiniteBox.amplitude n + R + P * S) :=
      mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hc hs)) hε
    _ ≤ (Real.pi / n) ^ 2 + epsilon n * R + epsilon n * P * S := by
      nlinarith

theorem pointwise_close_bound {n : ℕ} (hn : 2 ≤ n)
    (q σ : Fin n → ℝ) {R : ℝ} (hσ : ∀ j, σ j = 1 ∨ σ j = -1)
    (hq : ‖q - baseWord σ‖ ≤ R) (j : Fin n) :
    |q j| ≤ FiniteBox.amplitude n + R := by
  have hdiff : |q j - FiniteBox.amplitude n * σ j| ≤ R := by
    calc
      _ ≤ ‖q - baseWord σ‖ := by
        simpa only [Pi.sub_apply, baseWord, Real.norm_eq_abs] using
          norm_le_pi_norm (q - baseWord σ) j
      _ ≤ R := hq
  have hA := (FiniteBox.amplitude_pos hn).le
  have hb : |FiniteBox.amplitude n * σ j| = FiniteBox.amplitude n := by
    rcases hσ j with h | h <;> simp [h, abs_of_nonneg hA]
  have ht := abs_add_le (q j - FiniteBox.amplitude n * σ j)
    (FiniteBox.amplitude n * σ j)
  rw [sub_add_cancel, hb] at ht
  linarith

end
end StructuralNote.FixedSchurRadialAlgebra
