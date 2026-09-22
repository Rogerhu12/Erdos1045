import StructuralNote.CommonFiberNormalProjectionScaled

/-! Averaging the actual normal projection error retains the mixed term's
two different square-mean scales. -/

namespace StructuralNote.CommonFiberNormalAverage

open Erdos1045.EventualExact Complex LensClosure SchurLift
open CommonClosureEnergy CommonTangentialParameters CommonFiberGeometry
open CommonFiberNormalProjectionScaled
open scoped BigOperators
noncomputable section

def average {m : ℕ} (f : Fin m → ℝ) : ℝ := (∑ j, f j) / m

theorem average_nonneg {m : ℕ} (f : Fin m → ℝ) (hf : ∀ j, 0 ≤ f j) : 0 ≤ average f :=
  div_nonneg (Finset.sum_nonneg (fun j _ => hf j)) (Nat.cast_nonneg _)

theorem average_mono {m : ℕ} {f g : Fin m → ℝ} (h : ∀ j, f j ≤ g j) : average f ≤ average g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum (fun j _ => h j)) (Nat.cast_nonneg _)

theorem average_add {m : ℕ} (f g : Fin m → ℝ) :
    average (fun j => f j + g j) = average f + average g := by
  simp only [average, Finset.sum_add_distrib, add_div]

theorem average_mul {m : ℕ} (a : ℝ) (f : Fin m → ℝ) :
    average (fun j => a * f j) = a * average f := by
  simp only [average, ← Finset.mul_sum]
  ring

theorem average_div {m : ℕ} (f : Fin m → ℝ) (a : ℝ) :
    average (fun j => f j / a) = average f / a := by
  simp only [average, ← Finset.sum_div]
  ring

theorem average_const {m : ℕ} (hm : 0 < m) (a : ℝ) : average (fun _ : Fin m => a) = a := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp [average, hmR]

theorem mixed_average (f g : Fin m → ℝ) :
    average (fun j => |f j| * |g j|) ≤
      Real.sqrt (average (fun j => f j ^ 2)) * Real.sqrt (average (fun j => g j ^ 2)) := by
  have hf := average_nonneg (fun j => f j ^ 2) (fun j => sq_nonneg _)
  have hg := average_nonneg (fun j => g j ^ 2) (fun j => sq_nonneg _)
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => |f j|) (fun j => |g j|)
  simp only [sq_abs] at h
  have hsq : average (fun j => |f j| * |g j|) ^ 2 ≤
      average (fun j => f j ^ 2) * average (fun j => g j ^ 2) := by
    unfold average
    calc
      _ = (∑ j, |f j| * |g j|) ^ 2 / (m : ℝ) ^ 2 := div_pow _ _ _
      _ ≤ ((∑ j, f j ^ 2) * ∑ j, g j ^ 2) / (m : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right h (sq_nonneg _)
      _ = _ := by ring
  apply (sq_le_sq₀ (average_nonneg _ (fun j => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hf, Real.sq_sqrt hg]
  exact hsq

theorem normal_error_average {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ)
    (hz : closure (phase hm θ) (fun j => 2 * Real.cos (halfAngle hm θ j)) σ (coordinates hm v) ξ = 0)
    (hσ : ∀ j, |σ j| ≤ 1)
    (hh : ∀ j : Fin m, |angleDifference (by omega) θ (halfIndex j) / 2| ≤ 1)
    (hb : ∀ j : Fin m, |angleAverage (by omega) θ (halfIndex j)| ≤ 1)
    (ht : ∀ j, heightParameter (coordinates hm v) ξ j ^ 2 ≤ 4) :
    average (fun j => |normalError hm θ v σ ξ j|) ≤ scale (2 * m) *
      (average (fun j => heightParameter (coordinates hm v) ξ j ^ 2) / 2 +
        3 * average (fun j : Fin m => (angleDifference (by omega) θ (halfIndex j) / 2) ^ 2) +
        (Real.pi / (2 * m : ℝ)) ^ 2 *
          average (fun j : Fin m => angleAverage (by omega) θ (halfIndex j) ^ 2) +
        Real.sqrt (average (fun j => heightParameter (coordinates hm v) ξ j ^ 2)) *
          Real.sqrt (average (fun j : Fin m => angleAverage (by omega) θ (halfIndex j) ^ 2))) := by
  have h := average_mono (fun j => actual_normal_error hm θ v σ ξ hz j (hσ j) (hh j) (hb j) (ht j))
  simp only [average_mul, average_add, average_div] at h
  have hmixed := mixed_average (heightParameter (coordinates hm v) ξ)
    (fun j : Fin m => angleAverage (by omega) θ (halfIndex j))
  have hs := (scale_bounds (show 2 ≤ 2 * m by omega)).1.le
  nlinarith

end
end StructuralNote.CommonFiberNormalAverage
