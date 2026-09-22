import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-! Exact rational circle coordinates in (10.4), and the identities making
matching and selected crossing edges have length two. No nonedge feasibility
or stationary-point existence is asserted by these local identities. -/

noncomputable section

namespace StructuralNote.RationalChart

def rotation (t : ℝ) : ℂ :=
  ⟨(1 - t ^ 2) / (1 + t ^ 2), 2 * t / (1 + t ^ 2)⟩

theorem denominator_pos (t : ℝ) : 0 < 1 + t ^ 2 := by positivity

theorem complex_denominator_ne_zero (t : ℝ) : 1 - Complex.I * (t : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

theorem rotation_fraction (t : ℝ) :
    rotation t = (1 + Complex.I * (t : ℂ)) / (1 - Complex.I * (t : ℂ)) := by
  apply (eq_div_iff (complex_denominator_ne_zero t)).2
  apply Complex.ext
  · simp [rotation, Complex.mul_re, Complex.mul_im]
    field_simp
    ring
  · simp [rotation, Complex.mul_re, Complex.mul_im]
    field_simp
    ring

theorem rotation_normSq (t : ℝ) : Complex.normSq (rotation t) = 1 := by
  simp only [Complex.normSq_apply, rotation]
  field_simp
  ring

theorem rotation_norm (t : ℝ) : ‖rotation t‖ = 1 := by
  have h := rotation_normSq t
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (rotation t)]

@[simp] theorem rotation_zero : rotation 0 = 1 := by
  apply Complex.ext <;> norm_num [rotation]

theorem one_add_rotation_re (t : ℝ) : 1 + (rotation t).re = 2 / (1 + t ^ 2) := by
  dsimp [rotation]
  field_simp
  ring

theorem one_add_rotation_re_pos (t : ℝ) : 0 < 1 + (rotation t).re := by
  rw [one_add_rotation_re]
  positivity

theorem recover_parameter (t : ℝ) : (rotation t).im / (1 + (rotation t).re) = t := by
  rw [one_add_rotation_re]
  dsimp [rotation]
  field_simp

theorem rotation_injective : Function.Injective rotation := by
  intro t s h
  have := congrArg (fun z : ℂ => z.im / (1 + z.re)) h
  simpa only [recover_parameter] using this

theorem matching_difference (C d : ℂ) : (C + d) - (C - d) = 2 * d := by ring

theorem matching_length (C d : ℂ) (hd : ‖d‖ = 1) : ‖(C + d) - (C - d)‖ = 2 := by
  rw [matching_difference, norm_mul, hd]
  norm_num

def crossingIncrement (σ : ℝ) (d e U : ℂ) : ℂ := (σ : ℂ) * (2 * U - d - e)

theorem positive_crossing_difference (C d e U : ℂ) :
    (C + crossingIncrement 1 d e U + e) - (C - d) = 2 * U := by
  simp only [crossingIncrement, Complex.ofReal_one, one_mul]
  ring

theorem negative_crossing_difference (C d e U : ℂ) :
    (C + d) - (C + crossingIncrement (-1) d e U - e) = 2 * U := by
  simp only [crossingIncrement, Complex.ofReal_neg, Complex.ofReal_one]
  ring

theorem positive_crossing_length (C d e U : ℂ) (hU : ‖U‖ = 1) :
    ‖(C + crossingIncrement 1 d e U + e) - (C - d)‖ = 2 := by
  rw [positive_crossing_difference, norm_mul, hU]
  norm_num

theorem negative_crossing_length (C d e U : ℂ) (hU : ‖U‖ = 1) :
    ‖(C + d) - (C + crossingIncrement (-1) d e U - e)‖ = 2 := by
  rw [negative_crossing_difference, norm_mul, hU]
  norm_num

/-- The rational coordinates preserve unit length for every real parameter. -/
theorem rational_direction_norm (w : ℂ) (hw : ‖w‖ = 1) (t : ℝ) :
    ‖w * rotation t‖ = 1 := by
  rw [norm_mul, hw, rotation_norm, one_mul]

end StructuralNote.RationalChart
