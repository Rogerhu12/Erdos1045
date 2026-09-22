import Erdos1045.ExteriorGenerating

/-! # Applying the proved Fourier estimates to the actual exterior data -/

namespace Erdos1045.ExteriorClassical

open ExteriorBoundary Configuration FaberFourier FaberSampling MatrixDefect
noncomputable section

def matrixConstant (C τ : ℝ) : ℝ := 32 * Real.exp (2 * τ) * C * radialConstant τ

theorem matrixConstant_nonneg {C τ : ℝ} (hC : 0 ≤ C) : 0 ≤ matrixConstant C τ := by
  unfold matrixConstant radialConstant
  positivity

theorem radius_reciprocal {n : ℕ} (hn : 0 < n) {τ : ℝ} (hτ : 0 < τ) :
    1 / (1 + τ / (n : ℝ)) = radialRatio n τ := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have ht : (n : ℝ) + τ ≠ 0 := by positivity
  unfold radialRatio
  field_simp

theorem ExteriorData.matrix_sub_circle {n : ℕ} {z : Points n} (d : ExteriorData z) :
    d.matrix - d.circleMatrix = coefficientMatrix d.remainder := rfl

theorem ExteriorData.faber_error_bound {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (HL : ClassicalLaurentSeries)
    (HS : ClassicalFourierFacts) (HM : ClassicalGeometricMoment)
    (hn : 0 < n) {τ C : ℝ} (hτ : 0 < τ) (hC : 0 ≤ C)
    (hc : (1 / 2 : ℝ) ≤ d.capacity)
    (hsampling : H1Sampling (fun j : Fin n => d.angles.angle j) C)
    (hq : ∀ i t, ‖d.quotient i (((1 + τ / n : ℝ) : ℂ) * unit t)‖ ≤ 1 / 2) :
    frobSq (d.matrix - d.circleMatrix) ≤ matrixConstant C τ * (n : ℝ) ^ 2 * d.energySquared := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 1 < 1 + τ / (n : ℝ) := by linarith [div_pos hτ hn0]
  have he : (Real.sqrt d.energySquared) ^ 2 =
      2 * Real.pi * (∑' m : ℕ, (m : ℝ) ^ 2 * ‖d.coefficient m‖ ^ 2) := by
    rw [Real.sq_sqrt d.energySquared_nonneg, d.parseval_identity]
    rfl
  have hR (i : Fin n) : Summable (fun k =>
      ‖radialCoefficients (radialRatio n τ) (d.remainder i) k‖) := by
    rw [← radius_reciprocal hn hτ]
    exact d.remainder_summable HF HL hr i
  have hp (i : Fin n) : Summable (fun k =>
      ‖radialCoefficients (radialRatio n τ) (firstOrder
        (FaberFourier.coefficient d.capacity d.coefficient
          (fun j : Fin n => d.angles.angle j) i)) k‖) := by
    rw [← radius_reciprocal hn hτ]
    exact d.source_summable HL hr i
  have hid (i : Fin n) (t : ℝ) := d.correction_identity HF HL hr i t
  rw [radius_reciprocal hn hτ] at hid
  have h := faber_error_energy_bound HS HM hn hτ hc hC d.coefficient
    (fun j : Fin n => d.angles.angle j) hsampling d.sobolev.2 he d.remainder
    (fun i t => d.quotient i (((1 + τ / n : ℝ) : ℂ) * unit t)) hR hp hid hq
  simpa only [d.matrix_sub_circle, matrixConstant, Real.sq_sqrt d.energySquared_nonneg] using h

theorem ExteriorData.faber_remainder_bound {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (HL : ClassicalLaurentSeries)
    (HS : ClassicalFourierFacts) (HM : ClassicalGeometricMoment)
    (hn : 0 < n) {C η Q : ℝ} (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hc : (1 / 2 : ℝ) ≤ d.capacity)
    (hsampling : H1Sampling (fun j : Fin n => d.angles.angle j) C)
    (hq : ∀ i t, ‖d.quotient i (((1 + 1 / n : ℝ) : ℂ) * unit t)‖ ≤ 1 / 2)
    (hqη : ∀ i t, ‖d.quotient i (((1 + 1 / n : ℝ) : ℂ) * unit t)‖ ≤ η)
    (hscale : η ^ 2 ≤ Q * n * d.energySquared) :
    frobSq (d.matrix - d.circleMatrix - d.firstOrderMatrix) ≤
      matrixConstant C 1 * Q * (n : ℝ) ^ 3 * d.energySquared ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 1 < 1 + 1 / (n : ℝ) := by linarith [one_div_pos.mpr hn0]
  have he : (Real.sqrt d.energySquared) ^ 2 =
      2 * Real.pi * (∑' m : ℕ, (m : ℝ) ^ 2 * ‖d.coefficient m‖ ^ 2) := by
    rw [Real.sq_sqrt d.energySquared_nonneg, d.parseval_identity]
    rfl
  have hR (i : Fin n) : Summable (fun k =>
      ‖radialCoefficients (radialRatio n 1) (d.remainder i) k‖) := by
    rw [← radius_reciprocal hn (by norm_num : (0 : ℝ) < 1)]
    exact d.remainder_summable HF HL hr i
  have hp (i : Fin n) : Summable (fun k =>
      ‖radialCoefficients (radialRatio n 1) (firstOrder
        (FaberFourier.coefficient d.capacity d.coefficient
          (fun j : Fin n => d.angles.angle j) i)) k‖) := by
    rw [← radius_reciprocal hn (by norm_num : (0 : ℝ) < 1)]
    exact d.source_summable HL hr i
  have hid (i : Fin n) (t : ℝ) := d.correction_identity HF HL hr i t
  rw [radius_reciprocal hn (by norm_num : (0 : ℝ) < 1)] at hid
  have hscale' : η ^ 2 ≤ Q * n * (Real.sqrt d.energySquared) ^ 2 := by
    rwa [Real.sq_sqrt d.energySquared_nonneg]
  have h := faber_remainder_energy_bound HS HM hn (by norm_num) hc hC hη d.coefficient
    (fun j : Fin n => d.angles.angle j) hsampling d.sobolev.2 he d.remainder
    (fun i t => d.quotient i (((1 + 1 / n : ℝ) : ℂ) * unit t)) hR hp hid hq hqη hscale'
  have hs4 : (Real.sqrt d.energySquared) ^ 4 = d.energySquared ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt d.energySquared_nonneg]
  simpa only [d.matrix_sub_circle, ExteriorData.firstOrderMatrix, matrixConstant, hs4] using h

end
end Erdos1045.ExteriorClassical
