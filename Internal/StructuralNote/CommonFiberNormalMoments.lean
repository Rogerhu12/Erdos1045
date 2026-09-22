import StructuralNote.CommonFiberNormalAverage
import StructuralNote.CommonFiberDerivativeEnergy

/-! The square means entering normal projection, derived from the actual
angle and tangential energies rather than pointwise maxima. -/

namespace StructuralNote.CommonFiberNormalMoments

open Erdos1045.EventualExact Complex LensClosure SchurSpectrum
open CommonClosureEnergy CommonTangentialParameters CommonFiberDerivativeEnergy
open CommonFiberNormalAverage
open scoped BigOperators
noncomputable section

theorem angle_average_square {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (hmean : ∑ j, (θ j : ℂ) = 0) :
    average (fun j : Fin m => angleAverage (by omega) θ (halfIndex j) ^ 2) ≤
      8 * pairEnergy (by omega) (fun j => (θ j : ℂ)) / (2 * m : ℝ) ^ 2 := by
  have hn : 0 < (2 * m : ℝ) := by positivity
  have h : (∑ j : Fin m, angleAverage (by omega) θ (halfIndex j) ^ 2) ≤
      4 * pairEnergy (by omega) (fun j => (θ j : ℂ)) / (2 * m : ℝ) := by
    apply (le_div_iff₀ hn).mpr
    nlinarith only [average_energy hm θ hmean]
  calc
    _ = (2 / (2 * m : ℝ)) *
        ∑ j : Fin m, angleAverage (by omega) θ (halfIndex j) ^ 2 := by
      unfold average
      ring
    _ ≤ (2 / (2 * m : ℝ)) *
        (4 * pairEnergy (by omega) (fun j => (θ j : ℂ)) / (2 * m : ℝ)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

theorem angle_difference_square {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) :
    average (fun j : Fin m => (angleDifference (by omega) θ (halfIndex j) / 2) ^ 2) ≤
      4 * Real.pi ^ 2 * pairEnergy (by omega) (fun j => (θ j : ℂ)) / (2 * m : ℝ) ^ 3 := by
  have hn : 0 < (2 * m : ℝ) := by positivity
  have h : (∑ j : Fin m, angleDifference (by omega) θ (halfIndex j) ^ 2) ≤
      8 * Real.pi ^ 2 * pairEnergy (by omega) (fun j => (θ j : ℂ)) / (2 * m : ℝ) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hn)).mpr
    nlinarith only [half_difference_energy hm θ]
  calc
    _ = (1 / (2 * (2 * m : ℝ))) *
        ∑ j : Fin m, angleDifference (by omega) θ (halfIndex j) ^ 2 := by
      simp only [average, div_pow, ← Finset.sum_div]
      ring
    _ ≤ (1 / (2 * (2 * m : ℝ))) *
        (8 * Real.pi ^ 2 * pairEnergy (by omega) (fun j => (θ j : ℂ)) / (2 * m : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

theorem coordinate_average_square {m : ℕ} (hm : 0 < m) (v : Fin (2 * m) → ℂ) :
    average (fun j => coordinates hm v j ^ 2) ≤
      16 * Real.pi ^ 2 * pairEnergy (by omega) v / (2 * m : ℝ) ^ 3 := by
  have hn : 0 < (2 * m : ℝ) := by positivity
  have h : (∑ j, coordinates hm v j ^ 2) ≤
      8 * Real.pi ^ 2 * pairEnergy (by omega) v / (2 * m : ℝ) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hn)).mpr
    nlinarith only [coordinate_energy hm v]
  calc
    _ = (2 / (2 * m : ℝ)) * ∑ j, coordinates hm v j ^ 2 := by unfold average; ring
    _ ≤ (2 / (2 * m : ℝ)) * (8 * Real.pi ^ 2 * pairEnergy (by omega) v / (2 * m : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

theorem height_average_square {m : ℕ} (hm : 0 < m) (v : Fin (2 * m) → ℂ) (ξ : ℂ) :
    average (fun j => heightParameter (coordinates hm v) ξ j ^ 2) ≤
      32 * Real.pi ^ 2 * pairEnergy (by omega) v / (2 * m : ℝ) ^ 3 + 2 * ‖ξ‖ ^ 2 := by
  have hpoint (j : Fin m) : heightParameter (coordinates hm v) ξ j ^ 2 ≤
      2 * coordinates hm v j ^ 2 + 2 * ‖ξ‖ ^ 2 := by
    have h := harmonicFunctional_le_norm (LensClosure.midpoint m j) ξ
    have hs := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs] at hs
    unfold heightParameter
    nlinarith [sq_nonneg (coordinates hm v j - harmonicFunctional (LensClosure.midpoint m j) ξ)]
  have h := average_mono hpoint
  rw [average_add, average_mul, average_const hm] at h
  have hc := coordinate_average_square hm v
  have htwo := mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 2)
  calc
    _ ≤ 2 * (16 * Real.pi ^ 2 * pairEnergy (by omega) v / (2 * m : ℝ) ^ 3) + 2 * ‖ξ‖ ^ 2 :=
      h.trans (_root_.add_le_add htwo le_rfl)
    _ = _ := by ring

end
end StructuralNote.CommonFiberNormalMoments
