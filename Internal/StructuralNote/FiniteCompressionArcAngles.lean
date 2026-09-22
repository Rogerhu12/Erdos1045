import StructuralNote.SignPatternGridShift
import StructuralNote.FiniteCompressionKernelGeometry

/-! The fixed kernel windows follow from actual midpoint locations of the
three arcs, allowing a full grid step of rounding error at every left cut. -/

namespace StructuralNote.FiniteCompressionArcAngles

open Real Filter
open SignPatternGridShift FixedDualClassificationStep FiniteCompressionKernelGeometry
open scoped Topology
noncomputable section

theorem midpoint_monotone (n : ℕ) : Monotone (cellMidpoint n) := by
  intro i j hij
  unfold cellMidpoint
  gcongr

theorem midpoint_half_period {m : ℕ} (hm : 0 < m) (j : ℕ) :
    cellMidpoint (2 * m) (j + m) = cellMidpoint (2 * m) j + Real.pi := by
  rw [cellMidpoint_add hm]
  have hmR : (m : ℝ) ≠ 0 := by positivity
  field_simp

theorem compressionAngle_eq_midpoint_sub {m r j : ℕ} (hj : j ≤ r) :
    compressionAngle m (r - j) = cellMidpoint (2 * m) r - cellMidpoint (2 * m) j := by
  unfold compressionAngle cellMidpoint
  rw [Nat.cast_sub hj]
  push_cast
  ring

theorem compressionAngle_reflected {m r j : ℕ} (hm : 0 < m) (hr : r ≤ j + m) :
    compressionAngle m (j + m - r) = cellMidpoint (2 * m) j + Real.pi - cellMidpoint (2 * m) r := by
  rw [compressionAngle_eq_midpoint_sub hr, midpoint_half_period hm]

theorem eventually_small_grid_step : ∀ᶠ m : ℕ in atTop,
    Real.pi / m ≤ (Real.pi - 3) / 24 := by
  have hp : 0 < (Real.pi - 3) / 24 := by linarith [pi_gt_three]
  exact ((tendsto_const_div_atTop_nhds_zero_nat Real.pi).eventually (gt_mem_nhds hp)).mono
    (fun _ h => h.le)

theorem three_arc_angle_bounds {m : ℕ} (hm : 0 < m) {c : ℝ}
    {L₀ R₀ L₁ R₁ L₂ R₂ j : ℕ}
    (hstep : Real.pi / m ≤ (Real.pi - 3) / 24)
    (hjL : L₀ ≤ j) (hjR : j ≤ R₀) (hjfirst : j ≤ L₁) (hlast : R₂ ≤ j + m)
    (hfirst : L₁ ≤ R₁) (hsecond : L₂ ≤ R₂)
    (hL₀ : c - 1 / 8 - Real.pi / m < cellMidpoint (2 * m) L₀)
    (hR₀ : cellMidpoint (2 * m) R₀ ≤ c + 1 / 8)
    (hL₁ : c + Real.pi / 3 - 1 / 8 - Real.pi / m < cellMidpoint (2 * m) L₁)
    (hR₁ : cellMidpoint (2 * m) R₁ ≤ c + Real.pi / 3 + 1 / 8)
    (hL₂ : c + 2 * Real.pi / 3 - 1 / 8 - Real.pi / m < cellMidpoint (2 * m) L₂)
    (hR₂ : cellMidpoint (2 * m) R₂ ≤ c + 2 * Real.pi / 3 + 1 / 8) :
    compressionAngle m (j - L₀) ≤ Real.pi / 12 ∧
      Real.pi / 4 ≤ compressionAngle m (L₁ - j) ∧
      compressionAngle m (R₁ - j) ≤ 5 * Real.pi / 12 ∧
      Real.pi / 4 ≤ compressionAngle m (j + m - R₂) ∧
      compressionAngle m (j + m - L₂) ≤ 5 * Real.pi / 12 := by
  have hjlo := midpoint_monotone (2 * m) hjL
  have hjhi := midpoint_monotone (2 * m) hjR
  rw [compressionAngle_eq_midpoint_sub hjL, compressionAngle_eq_midpoint_sub hjfirst,
    compressionAngle_eq_midpoint_sub (hjfirst.trans hfirst),
    compressionAngle_reflected hm hlast, compressionAngle_reflected hm (hsecond.trans hlast)]
  constructor
  · linarith [pi_gt_three]
  constructor
  · linarith [pi_gt_three]
  constructor
  · linarith [pi_gt_three]
  constructor <;> linarith [pi_gt_three]

end
end StructuralNote.FiniteCompressionArcAngles
