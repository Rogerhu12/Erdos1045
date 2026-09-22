import StructuralNote.CommonFiberNormalProjection
import StructuralNote.SignedPressureRemainder

/-! The normal Taylor error with the actual finite-box amplitude and scale. -/

namespace StructuralNote.CommonFiberNormalProjectionScaled

open Erdos1045.EventualExact Complex LensClosure SchurLift
open CommonClosureEnergy CommonTangentialParameters CommonFiberGeometry CommonFiberNormalProjection
open scoped BigOperators
noncomputable section

def scale (n : ℕ) : ℝ := n / (2 * Real.sin (Real.pi / n))

theorem scale_bounds {n : ℕ} (hn : 2 ≤ n) : 0 < scale n ∧ scale n ≤ (n : ℝ) ^ 2 / 4 := by
  have hs := SignedPressureRemainder.reciprocal_sine_le hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  refine ⟨div_pos hnR (mul_pos (by norm_num) hs.1), ?_⟩
  have hh := mul_le_mul_of_nonneg_left hs.2 hnR.le
  calc
    scale n = n * (1 / (2 * Real.sin (Real.pi / n))) := by unfold scale; ring
    _ ≤ n * (n / 4) := hh
    _ = _ := by ring

theorem scale_radius {n : ℕ} (hn : 2 ≤ n) :
    scale n * (2 - 2 * Real.cos (Real.pi / n)) = FiniteBox.amplitude n := by
  have hs := (SignedPressureRemainder.reciprocal_sine_le hn).1.ne'
  have he := BoxLensLift.radius_identity hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simp only [BoxLensLift.radius, BoxLensLift.angle] at he
  unfold scale
  calc
    _ = n / (2 * Real.sin (Real.pi / n)) * (2 * (1 - Real.cos (Real.pi / n))) := by ring
    _ = _ := by rw [he]; field_simp

theorem scaled_error {n : ℕ} (hn : 2 ≤ n) (h b σ t : ℝ) (hσ : |σ| ≤ 1)
    (hh : |h| ≤ 1) (hb : |b| ≤ 1) (ht : t ^ 2 ≤ 4) :
    |scale n * (σ * Lens.width (2 * Real.cos (Real.pi / n + h)) t * Real.cos b - t * Real.sin b) -
      FiniteBox.amplitude n * σ - (n : ℝ) * σ * h| ≤
      scale n * (t ^ 2 / 2 + 3 * h ^ 2 + (Real.pi / n) ^ 2 * b ^ 2 + |t| * |b|) := by
  have hs := (SignedPressureRemainder.reciprocal_sine_le hn).1.ne'
  have hlin : scale n * (2 * σ * Real.sin (Real.pi / n) * h) = (n : ℝ) * σ * h := by
    unfold scale
    field_simp
  have he := scalar_projection_error (Real.pi / n) h b σ t hσ hh hb ht
  have hc := mul_le_mul_of_nonneg_left he (scale_bounds hn).1.le
  have hid : scale n * (σ * Lens.width (2 * Real.cos (Real.pi / n + h)) t * Real.cos b - t * Real.sin b -
      σ * (2 - 2 * Real.cos (Real.pi / n)) - 2 * σ * Real.sin (Real.pi / n) * h) =
      scale n * (σ * Lens.width (2 * Real.cos (Real.pi / n + h)) t * Real.cos b - t * Real.sin b) -
        FiniteBox.amplitude n * σ - (n : ℝ) * σ * h := by
    rw [← scale_radius hn, ← hlin]
    ring
  rw [← hid, abs_mul, abs_of_nonneg (scale_bounds hn).1.le]
  exact hc

def normalError {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (σ : Fin m → ℝ) (ξ : ℂ) (j : Fin m) : ℝ :=
  constraint (by omega) (center hm θ v σ ξ) (halfIndex j) - FiniteBox.amplitude (2 * m) * σ j -
    (2 * m : ℝ) / 2 * σ j * angleDifference (by omega) θ (halfIndex j)

theorem actual_normal_error {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ)
    (hz : closure (phase hm θ) (fun j => 2 * Real.cos (halfAngle hm θ j)) σ (coordinates hm v) ξ = 0)
    (j : Fin m) (hσ : |σ j| ≤ 1)
    (hh : |angleDifference (by omega) θ (halfIndex j) / 2| ≤ 1)
    (hb : |angleAverage (by omega) θ (halfIndex j)| ≤ 1)
    (ht : heightParameter (coordinates hm v) ξ j ^ 2 ≤ 4) :
    |normalError hm θ v σ ξ j| ≤ scale (2 * m) *
      (heightParameter (coordinates hm v) ξ j ^ 2 / 2 +
      3 * (angleDifference (by omega) θ (halfIndex j) / 2) ^ 2 +
      (Real.pi / (2 * m : ℝ)) ^ 2 * angleAverage (by omega) θ (halfIndex j) ^ 2 +
      |heightParameter (coordinates hm v) ξ j| * |angleAverage (by omega) θ (halfIndex j)|) := by
  have he := scaled_error (by omega : 2 ≤ 2 * m) _ _ _ _ hσ hh hb ht
  unfold normalError
  rw [actual_half_normal hm θ v σ ξ hz]
  simp only [halfAngle, scale, Nat.cast_mul, Nat.cast_ofNat] at he ⊢
  convert he using 1
  congr 1
  ring

end
end StructuralNote.CommonFiberNormalProjectionScaled
