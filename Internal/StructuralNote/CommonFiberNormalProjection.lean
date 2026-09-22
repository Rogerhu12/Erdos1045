import StructuralNote.CommonFiberGeometry

/-! Exact normal projection of the actual closed lens increments and a scalar
Taylor bound that retains the mixed height-angle term needed in (9.21). -/

namespace StructuralNote.CommonFiberNormalProjection

open Erdos1045.EventualExact Complex LensClosure SchurLift
open CommonClosureEnergy CommonTangentialParameters CommonFiberGeometry
open scoped BigOperators
noncomputable section

theorem rotated_increment_real (μ b L σ t : ℝ) :
    ((starRingEnd ℂ) (unit μ) * LensClosure.increment (μ + b) L σ t).re =
      σ * Lens.width L t * Real.cos b - t * Real.sin b := by
  have hu : (starRingEnd ℂ) (unit μ) * unit μ = 1 := by
    rw [mul_comm, Complex.mul_conj, normSq_eq_norm_sq, norm_unit]
    norm_num
  have he : unit (μ + b) = unit μ * unit b := by
    simp only [unit, Complex.ofReal_add, add_mul, Complex.exp_add]
  simp only [LensClosure.increment, he, ← mul_assoc, hu, one_mul]
  simp only [mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im,
    mul_zero, mul_one, add_zero, zero_add, unit_re, unit_im]
  ring

theorem actual_half_normal {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ)
    (hz : closure (phase hm θ) (fun j => 2 * Real.cos (halfAngle hm θ j)) σ (coordinates hm v) ξ = 0)
    (j : Fin m) :
    constraint (by omega) (center hm θ v σ ξ) (halfIndex j) =
      (2 * m : ℝ) / (2 * Real.sin (Real.pi / (2 * m : ℝ))) *
        (σ j * Lens.width (2 * Real.cos (halfAngle hm θ j)) (heightParameter (coordinates hm v) ξ j) *
          Real.cos (angleAverage (by omega) θ (halfIndex j)) -
        heightParameter (coordinates hm v) ξ j * Real.sin (angleAverage (by omega) θ (halfIndex j))) := by
  have hf : frame (2 * m) (halfIndex j) = unit (LensClosure.midpoint m j) := by
    simpa only [CommonClosureEnergy.halfIndex, BoxLensLift.halfIndex] using BoxLensLift.frame_halfIndex j
  rw [constraint, center_half_difference hm θ v σ ξ hz, hf]
  simp only [fiberIncrement, phase, rotated_increment_real, Nat.cast_mul, Nat.cast_ofNat]

theorem cos_zero_error (b : ℝ) : |Real.cos b - 1| ≤ b ^ 2 / 2 := by
  rw [abs_of_nonpos (by linarith [Real.cos_le_one b])]
  linarith [Real.one_sub_sq_div_two_le_cos (x := b)]

theorem cos_linear_error (a h : ℝ) (hh : |h| ≤ 1) :
    |Real.cos (a + h) - Real.cos a + Real.sin a * h| ≤ h ^ 2 := by
  have he : Real.cos (a + h) - Real.cos a + Real.sin a * h =
      Real.cos a * (Real.cos h - 1) + Real.sin a * (h - Real.sin h) := by
    rw [Real.cos_add]
    ring
  rw [he]
  have hc := mul_le_mul (Real.abs_cos_le_one a) (cos_zero_error h)
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hs := mul_le_mul (Real.abs_sin_le_one a) (Real.abs_sub_sin_le h)
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have ht := abs_add_le (Real.cos a * (Real.cos h - 1)) (Real.sin a * (h - Real.sin h))
  rw [abs_mul, abs_mul] at ht
  have hp : |h| ^ 3 ≤ h ^ 2 := by nlinarith [sq_abs h, sq_nonneg h]
  nlinarith

theorem scalar_projection_error (a h b σ t : ℝ) (hσ : |σ| ≤ 1)
    (hh : |h| ≤ 1) (hb : |b| ≤ 1) (ht : t ^ 2 ≤ 4) :
    |σ * Lens.width (2 * Real.cos (a + h)) t * Real.cos b - t * Real.sin b -
      σ * (2 - 2 * Real.cos a) - 2 * σ * Real.sin a * h| ≤
      t ^ 2 / 2 + 3 * h ^ 2 + a ^ 2 * b ^ 2 + |t| * |b| := by
  have he : σ * Lens.width (2 * Real.cos (a + h)) t * Real.cos b - t * Real.sin b -
      σ * (2 - 2 * Real.cos a) - 2 * σ * Real.sin a * h =
      σ * (Lens.height t - 2) * Real.cos b -
      2 * σ * (Real.cos (a + h) - Real.cos a + Real.sin a * h) +
      σ * (2 - 2 * Real.cos (a + h)) * (Real.cos b - 1) - t * Real.sin b := by
    unfold Lens.width
    ring
  have h₁ : |σ * (Lens.height t - 2) * Real.cos b| ≤ t ^ 2 / 2 := by
    rw [abs_mul, abs_mul]
    have hfirst := mul_le_mul hσ (BoxLensLift.height_defect ht) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have hlast := mul_le_mul hfirst (Real.abs_cos_le_one b) (abs_nonneg _) (by positivity)
    simpa only [one_mul, mul_one] using hlast
  have h₂ : |2 * σ * (Real.cos (a + h) - Real.cos a + Real.sin a * h)| ≤ 2 * h ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hh' := mul_le_mul hσ (cos_linear_error a h hh) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  have hwidth : |2 - 2 * Real.cos (a + h)| ≤ 2 * (a ^ 2 + h ^ 2) := by
    rw [abs_of_nonneg (by linarith [Real.cos_le_one (a + h)])]
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := a + h), sq_nonneg (a - h)]
  have h₃ : |σ * (2 - 2 * Real.cos (a + h)) * (Real.cos b - 1)| ≤ a ^ 2 * b ^ 2 + h ^ 2 := by
    rw [abs_mul, abs_mul]
    have hw := mul_le_mul hσ hwidth (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have hp := mul_le_mul hw (cos_zero_error b) (abs_nonneg _) (by positivity)
    have hb2 : b ^ 2 ≤ 1 := by nlinarith [sq_abs b, abs_nonneg b]
    nlinarith [mul_le_mul_of_nonneg_left hb2 (sq_nonneg h)]
  have h₄ : |t * Real.sin b| ≤ |t| * |b| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (Real.abs_sin_le_abs (x := b)) (abs_nonneg _)
  rw [he]
  have hh₁ := abs_sub (σ * (Lens.height t - 2) * Real.cos b)
    (2 * σ * (Real.cos (a + h) - Real.cos a + Real.sin a * h))
  have hh₂ := abs_add_le
    (σ * (Lens.height t - 2) * Real.cos b - 2 * σ * (Real.cos (a + h) - Real.cos a + Real.sin a * h))
    (σ * (2 - 2 * Real.cos (a + h)) * (Real.cos b - 1))
  have hh₃ := abs_sub
    (σ * (Lens.height t - 2) * Real.cos b - 2 * σ * (Real.cos (a + h) - Real.cos a + Real.sin a * h) +
      σ * (2 - 2 * Real.cos (a + h)) * (Real.cos b - 1)) (t * Real.sin b)
  linarith

end
end StructuralNote.CommonFiberNormalProjection
