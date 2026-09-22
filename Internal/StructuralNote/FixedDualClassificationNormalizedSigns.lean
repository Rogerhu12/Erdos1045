import StructuralNote.FixedDualClassificationExteriorGaps
import StructuralNote.SignPatternGridShift
import StructuralNote.SignPatternEnergySymmetry

/-! A genuine integer grid rotation puts the comparison phase in one grid
step. This does not use a continuous rotation as a finite-grid symmetry. -/

namespace StructuralNote.FixedDualClassificationNormalizedSigns

open Real Set Filter Erdos1045.EventualExact FiniteBox
open FixedDualClassificationStep FixedDualClassificationZeroArcs
open FixedDualClassificationFinite FixedDualClassificationExteriorGaps
open SignPatternGridShift SignPatternSymmetry SignPatternEnergySymmetry
open FiniteCompressionRanked
noncomputable section

theorem normalized_zeroCenter {m : ℕ} {α β : ℝ} {k : ℕ}
    (hβ : β = α + 2 * Real.pi - (k : ℝ) * (Real.pi / m)) (r : ℤ) :
    zeroCenter β (r - 6) + (k : ℝ) * (Real.pi / m) = zeroCenter α r := by
  unfold zeroCenter
  rw [hβ]
  push_cast
  ring

theorem normalized_midpoint_cosine {m : ℕ} (hm : 0 < m) {α β : ℝ} {k : ℕ}
    (hβ : β = α + 2 * Real.pi - (k : ℝ) * (Real.pi / m)) (j : ℕ) :
    cos (3 * (cellMidpoint (2 * m) (j + k) - α)) =
      cos (3 * (cellMidpoint (2 * m) j - β)) := by
  rw [cellMidpoint_add hm]
  have he : 3 * (cellMidpoint (2 * m) j + (k : ℝ) * (Real.pi / m) - α) =
      3 * (cellMidpoint (2 * m) j - β) + (3 : ℕ) * (2 * Real.pi) := by
    rw [hβ]
    norm_num
    ring
  rw [he, cos_add_nat_mul_two_pi]

theorem localizedSigns_rotate {m : ℕ} {hm : 0 < m} {s : SignPattern hm} {α β : ℝ}
    (h : LocalizedSigns hm s α) (k : ℕ)
    (hβ : β = α + 2 * Real.pi - (k : ℝ) * (Real.pi / m)) :
    LocalizedSigns hm (rotatePattern k s) β := by
  intro j haway
  rw [patternSign_rotatePattern_site]
  have haway' : ∀ r : ℤ, (1 : ℝ) / 8 ≤
      |cellMidpoint (2 * m) (j + k) - zeroCenter α r| := by
    intro r
    have hr := haway (r - 6)
    rw [cellMidpoint_add hm, ← normalized_zeroCenter hβ r]
    simpa only [add_sub_add_right_eq_sub] using hr
  rw [h (j + k) haway', normalized_midpoint_cosine hm hβ j]

theorem eventually_normalized_localization (C₀ : ℝ) : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (s : SignPattern hm), deficit hm s ≤ C₀ / (2 * m : ℝ) ^ 2 →
    ∃ k : ℕ, ∃ β ∈ Ico 0 (Real.pi / m),
      LocalizedSigns hm (rotatePattern k s) β ∧
      deficit hm (rotatePattern k s) ≤ C₀ / (2 * m : ℝ) ^ 2 := by
  filter_upwards [eventually_localizedSigns C₀] with m h hm s hdef
  obtain ⟨α, hα, hsign⟩ := h hm s hdef
  obtain ⟨k, β, hβ, heq⟩ := phase_normalization hm hα
  refine ⟨k, β, hβ, localizedSigns_rotate hsign k heq, ?_⟩
  rwa [deficit_rotatePattern]

end
end StructuralNote.FixedDualClassificationNormalizedSigns
