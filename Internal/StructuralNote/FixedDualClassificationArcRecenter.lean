import StructuralNote.FixedDualClassificationNormalizedSigns
import StructuralNote.FixedDualClassificationArcGrid

/-! Integer recentering and the phase shift associated with negating a word.
These are exact discrete symmetries, including the signs away from every zero arc. -/

namespace StructuralNote.FixedDualClassificationArcRecenter

open Real Set Erdos1045.EventualExact FiniteBox
open SignPatternSymmetry SignPatternGridShift
open FixedDualClassificationStep FixedDualClassificationZeroArcs
open FixedDualClassificationExteriorGaps FixedDualClassificationArcGrid
open FixedDualClassificationLobeGeometry
noncomputable section

theorem phase_normalization_nonneg {m : ℕ} (hm : 0 < m) {α : ℝ} (hα : 0 ≤ α) :
    ∃ k : ℕ, ∃ β ∈ Ico 0 (gridStep m), β = α - (k : ℝ) * gridStep m := by
  have hd := gridStep_pos hm
  let k : ℕ := ⌊α / gridStep m⌋₊
  have hklo : (k : ℝ) ≤ α / gridStep m := Nat.floor_le (div_nonneg hα hd.le)
  have hkhi : α / gridStep m < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlo := (le_div_iff₀ hd).mp hklo
  have hhi := (div_lt_iff₀ hd).mp hkhi
  refine ⟨k, α - k * gridStep m, ⟨by linarith, by nlinarith⟩, rfl⟩

theorem localizedSigns_rotate_direct {m : ℕ} {hm : 0 < m} {s : SignPattern hm} {α β : ℝ}
    (h : LocalizedSigns hm s α) (k : ℕ) (hβ : β = α - (k : ℝ) * gridStep m) :
    LocalizedSigns hm (rotatePattern k s) β := by
  intro j haway
  rw [patternSign_rotatePattern_site]
  have haway' : ∀ r : ℤ, (1 : ℝ) / 8 ≤
      |cellMidpoint (2 * m) (j + k) - zeroCenter α r| := by
    intro r
    have he : cellMidpoint (2 * m) (j + k) - zeroCenter α r =
        cellMidpoint (2 * m) j - zeroCenter β r := by
      rw [cellMidpoint_add hm, hβ]
      unfold zeroCenter gridStep
      ring
    rw [he]
    exact haway r
  rw [h (j + k) haway']
  have he : cellMidpoint (2 * m) (j + k) - α = cellMidpoint (2 * m) j - β := by
    rw [cellMidpoint_add hm, hβ]
    unfold gridStep
    ring
  rw [he]

theorem localizedSigns_negate_third {m : ℕ} {hm : 0 < m} {s : SignPattern hm} {α : ℝ}
    (h : LocalizedSigns hm s α) : LocalizedSigns hm (globalNegate s) (α + Real.pi / 3) := by
  intro j haway
  have haway' : ∀ r : ℤ, (1 : ℝ) / 8 ≤
      |cellMidpoint (2 * m) j - zeroCenter α r| := by
    intro r
    have he : zeroCenter (α + Real.pi / 3) (r - 1) = zeroCenter α r := by
      unfold zeroCenter
      push_cast
      ring
    simpa only [he] using haway (r - 1)
  have hne := cosine_ne_zero_of_away (cosine_away_of_outside_arcs haway')
  have he : cos (3 * (cellMidpoint (2 * m) j - (α + Real.pi / 3))) =
      -cos (3 * (cellMidpoint (2 * m) j - α)) := by
    rw [show 3 * (cellMidpoint (2 * m) j - (α + Real.pi / 3)) =
      3 * (cellMidpoint (2 * m) j - α) - Real.pi by ring, cos_sub_pi]
  rw [patternSign_globalNegate, h j haway', he]
  split_ifs <;> norm_num at *
  all_goals first | linarith | (apply hne; linarith)

theorem localizedSigns_two_thirds {m : ℕ} {hm : 0 < m} {s : SignPattern hm} {α : ℝ}
    (h : LocalizedSigns hm s α) : LocalizedSigns hm s (α + 2 * Real.pi / 3) := by
  have hh := localizedSigns_negate_third (localizedSigns_negate_third h)
  rw [globalNegate_involutive] at hh
  convert hh using 1
  ring

theorem cutIndex_add_grid {m : ℕ} (hm : 0 < m) {x : ℝ}
    (hx : gridStep m / 2 ≤ x) (k : ℕ) :
    cutIndex m (x + (k : ℝ) * gridStep m) = cutIndex m x + k := by
  have hmR : (m : ℝ) ≠ 0 := by positivity
  have he : (x + (k : ℝ) * gridStep m) * (m : ℝ) / Real.pi - 1 / 2 =
      (x * (m : ℝ) / Real.pi - 1 / 2) + (k : ℝ) := by
    unfold gridStep
    field_simp
    ring
  unfold cutIndex
  rw [he, Nat.floor_add_natCast (cutIndex_argument_nonneg hm hx)]

theorem arc_cuts_recenter {m : ℕ} (hm : 0 < m) {α β : ℝ} {i k : ℕ}
    (hβ0 : 0 ≤ β) (hstep : gridStep m ≤ (Real.pi - 3) / 24)
    (hβ : β = α + (i : ℝ) * Real.pi / 3 - (k : ℝ) * gridStep m) :
    arcLeft m β 0 + k = arcLeft m α i ∧ arcRight m β 0 + k = arcRight m α i := by
  have he : zeroCenter α i = zeroCenter β 0 + (k : ℝ) * gridStep m := by
    unfold zeroCenter
    rw [hβ]
    push_cast
    ring
  constructor
  · unfold arcLeft
    rw [he]
    rw [show zeroCenter β 0 + (k : ℝ) * gridStep m - 1 / 8 =
      (zeroCenter β 0 - 1 / 8) + (k : ℝ) * gridStep m by ring]
    exact (cutIndex_add_grid hm (arc_boundary_lower hm hβ0 hstep 0) k).symm
  · unfold arcRight
    rw [he]
    rw [show zeroCenter β 0 + (k : ℝ) * gridStep m + 1 / 8 =
      (zeroCenter β 0 + 1 / 8) + (k : ℝ) * gridStep m by ring]
    exact (cutIndex_add_grid hm (arc_boundary_right_lower hm hβ0 hstep 0) k).symm

end
end StructuralNote.FixedDualClassificationArcRecenter
