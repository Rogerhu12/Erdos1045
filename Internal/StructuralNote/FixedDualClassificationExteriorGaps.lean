import StructuralNote.FixedDualClassificationUnwrappedSigns

/-! The actual signs on each closed gap between adjacent uncertain arcs.
The endpoints are included because localization holds at distance 1/8. -/

namespace StructuralNote.FixedDualClassificationExteriorGaps

open Real Set Filter Erdos1045.EventualExact FiniteBox
open FixedDualClassificationStep FixedDualClassificationZeroArcs
open FixedDualClassificationFinite FixedDualClassificationUnwrappedSigns
open FiniteCompressionRanked
noncomputable section

def LocalizedSigns {m : ℕ} (hm : 0 < m) (s : SignPattern hm) (α : ℝ) : Prop :=
  ∀ j : ℕ, (∀ k : ℤ, (1 : ℝ) / 8 ≤ |cellMidpoint (2 * m) j - zeroCenter α k|) →
    patternSign s (site hm j) =
      if 0 ≤ cos (3 * (cellMidpoint (2 * m) j - α)) then 1 else -1

theorem eventually_localizedSigns (C₀ : ℝ) : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (s : SignPattern hm), deficit hm s ≤ C₀ / (2 * m : ℝ) ^ 2 →
    ∃ α ∈ Icc (-(Real.pi / 3)) (Real.pi / 3), LocalizedSigns hm s α := by
  filter_upwards [eventually_near_maximum_unwrapped_signs C₀] with m h hm s hdef
  obtain ⟨α, hα, hsign⟩ := h hm s hdef
  exact ⟨α, hα, fun j hj => (hsign j hj).2⟩

theorem zeroCenter_mono (α : ℝ) : Monotone (zeroCenter α) := by
  intro k l hkl
  have hcast : (k : ℝ) ≤ l := by exact_mod_cast hkl
  have hmul := mul_le_mul_of_nonneg_right hcast pi_pos.le
  unfold zeroCenter
  linarith

theorem zeroCenter_succ (α : ℝ) (k : ℤ) :
    zeroCenter α (k + 1) = zeroCenter α k + Real.pi / 3 := by
  unfold zeroCenter
  push_cast
  ring

theorem outside_arcs_of_gap {α x : ℝ} {k : ℤ}
    (hl : zeroCenter α k + 1 / 8 ≤ x)
    (hr : x ≤ zeroCenter α (k + 1) - 1 / 8) :
    ∀ l : ℤ, (1 : ℝ) / 8 ≤ |x - zeroCenter α l| := by
  intro l
  by_cases h : l ≤ k
  · have hc := zeroCenter_mono α h
    have hx : 0 ≤ x - zeroCenter α l := by linarith
    rw [abs_of_nonneg hx]
    linarith
  · have hc := zeroCenter_mono α (show k + 1 ≤ l by omega)
    have hx : x - zeroCenter α l ≤ 0 := by linarith
    rw [abs_of_nonpos hx]
    linarith

theorem cosine_from_zero (α x : ℝ) (k : ℤ) :
    cos (3 * (x - α)) = -((-1 : ℝ) ^ k) * sin (3 * (x - zeroCenter α k)) := by
  have he : 3 * (x - α) =
      (3 * (x - zeroCenter α k) + Real.pi / 2) + k * Real.pi := by
    unfold zeroCenter
    ring
  rw [he, cos_add_int_mul_pi, cos_add_pi_div_two]
  ring

theorem sine_positive_in_gap {α x : ℝ} {k : ℤ}
    (hl : zeroCenter α k + 1 / 8 ≤ x)
    (hr : x ≤ zeroCenter α (k + 1) - 1 / 8) :
    0 < sin (3 * (x - zeroCenter α k)) := by
  rw [zeroCenter_succ] at hr
  apply sin_pos_of_pos_of_lt_pi <;> linarith

theorem cosine_positive_in_gap {α x : ℝ} {k : ℤ} (hk : (-1 : ℝ) ^ k = -1)
    (hl : zeroCenter α k + 1 / 8 ≤ x)
    (hr : x ≤ zeroCenter α (k + 1) - 1 / 8) : 0 < cos (3 * (x - α)) := by
  rw [cosine_from_zero α x k, hk]
  simpa only [neg_neg, one_mul] using sine_positive_in_gap hl hr

theorem cosine_negative_in_gap {α x : ℝ} {k : ℤ} (hk : (-1 : ℝ) ^ k = 1)
    (hl : zeroCenter α k + 1 / 8 ≤ x)
    (hr : x ≤ zeroCenter α (k + 1) - 1 / 8) : cos (3 * (x - α)) < 0 := by
  rw [cosine_from_zero α x k, hk, neg_one_mul]
  linarith [sine_positive_in_gap hl hr]

theorem sign_positive_in_gap {m : ℕ} {hm : 0 < m} {s : SignPattern hm} {α : ℝ}
    (h : LocalizedSigns hm s α) (j : ℕ) {k : ℤ} (hk : (-1 : ℝ) ^ k = -1)
    (hl : zeroCenter α k + 1 / 8 ≤ cellMidpoint (2 * m) j)
    (hr : cellMidpoint (2 * m) j ≤ zeroCenter α (k + 1) - 1 / 8) :
    patternSign s (site hm j) = 1 := by
  rw [h j (outside_arcs_of_gap hl hr), if_pos (cosine_positive_in_gap hk hl hr).le]

theorem sign_negative_in_gap {m : ℕ} {hm : 0 < m} {s : SignPattern hm} {α : ℝ}
    (h : LocalizedSigns hm s α) (j : ℕ) {k : ℤ} (hk : (-1 : ℝ) ^ k = 1)
    (hl : zeroCenter α k + 1 / 8 ≤ cellMidpoint (2 * m) j)
    (hr : cellMidpoint (2 * m) j ≤ zeroCenter α (k + 1) - 1 / 8) :
    patternSign s (site hm j) = -1 := by
  rw [h j (outside_arcs_of_gap hl hr), if_neg (not_le.mpr (cosine_negative_in_gap hk hl hr))]

end
end StructuralNote.FixedDualClassificationExteriorGaps
