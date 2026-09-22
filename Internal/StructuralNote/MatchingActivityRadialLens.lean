import StructuralNote.MatchingActivityRadialBounds

/-! Exact feasible interval coordinates for pairs with unequal matching radii. -/

namespace StructuralNote.MatchingActivityRadialLens

open Erdos1045 Erdos1045.EventualExact Complex LensClosure
open MatchingActivityRadialPair MatchingActivityRadialBounds
noncomputable section

theorem length_le_twice_cos {φ r₀ r₁ : ℝ} (hφ : |φ| ≤ 1 / 4)
    (h₀ : 0 ≤ r₀) (h₁ : 0 ≤ r₁) (h₀u : r₀ ≤ 1) (h₁u : r₁ ≤ 1) :
    length φ r₀ r₁ ≤ 2 * Real.cos φ := by
  have hφ2 : φ ^ 2 ≤ 1 / 16 := by nlinarith [abs_le.mp hφ, sq_abs φ]
  have hcos : (31 / 32 : ℝ) ≤ Real.cos φ := by nlinarith [Real.one_sub_sq_div_two_le_cos (x := φ)]
  have hsin : Real.sin φ ^ 2 ≤ 1 / 16 := Real.sin_sq_le_sq.trans hφ2
  have hid := Real.cos_sq_add_sin_sq φ
  have hq₀ : r₀ ^ 2 ≤ 1 := by nlinarith
  have hq₁ : r₁ ^ 2 ≤ 1 := by nlinarith
  have hprod : r₀ * r₁ ≤ 1 := (mul_le_mul h₀u h₁u h₁ (by norm_num)).trans_eq (by norm_num)
  have hm := mul_le_mul_of_nonneg_right hprod (show 0 ≤ Real.cos φ ^ 2 - Real.sin φ ^ 2 by linarith)
  have he : length φ r₀ r₁ ^ 2 = r₀ ^ 2 + r₁ ^ 2 +
      2 * (r₀ * r₁) * (Real.cos φ ^ 2 - Real.sin φ ^ 2) := by
    rw [length_sq]
    nlinarith [show (r₀ ^ 2 + r₁ ^ 2) * (Real.cos φ ^ 2 + Real.sin φ ^ 2) = r₀ ^ 2 + r₁ ^ 2 by rw [hid, mul_one]]
  apply (sq_le_sq₀ (norm_nonneg _) (by linarith : 0 ≤ 2 * Real.cos φ)).1
  change length φ r₀ r₁ ^ 2 ≤ (2 * Real.cos φ) ^ 2
  nlinarith only [he, hq₀, hq₁, hm, hid]

def framed (α : ℝ) (B : ℂ) : ℂ := (starRingEnd ℂ) (unit α) * B

theorem framed_norm (α : ℝ) (B : ℂ) : ‖framed α B‖ = ‖B‖ := by
  simp only [framed, norm_mul, norm_conj, norm_unit, one_mul]

theorem framed_reconstruction (α : ℝ) (B : ℂ) :
    unit α * ((framed α B).re + ((framed α B).im : ℂ) * I) = B := by
  rw [re_add_im, framed, ← mul_assoc, mul_conj, normSq_eq_norm_sq, norm_unit]
  norm_num

theorem positive_width_of_slack {L t : ℝ} (hL : 0 ≤ L) (hslack : L ^ 2 + t ^ 2 < 4) :
    0 < Lens.width L t := by
  apply (Lens.width_pos_iff L t).mpr
  have ht : t ^ 2 ≤ 4 := by nlinarith [sq_nonneg L]
  have hh := Lens.height_sq ht
  apply (sq_lt_sq₀ hL (Lens.height_nonneg t)).mp
  linarith only [hh, hslack]

theorem width_positive_at_scale {n φ r₀ r₁ t : ℝ} (hn : 0 < n)
    (hφ : |φ| ≤ 1 / 4) (h₀ : 0 ≤ r₀) (h₁ : 0 ≤ r₁) (h₀u : r₀ ≤ 1) (h₁u : r₁ ≤ 1)
    (hsin : 1 / n ≤ Real.sin φ) (ht : |t| ≤ 1 / n) :
    0 < Lens.width (length φ r₀ r₁) t := by
  have hL := length_le_twice_cos hφ h₀ h₁ h₀u h₁u
  have hL2 := pow_le_pow_left₀ (norm_nonneg (pair φ r₀ r₁)) hL 2
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / n) hsin 2
  have ht2 := pow_le_pow_left₀ (abs_nonneg t) ht 2
  rw [sq_abs] at ht2
  apply positive_width_of_slack (norm_nonneg _)
  have hid := Real.cos_sq_add_sin_sq φ
  have hp : 0 < (1 / n) ^ 2 := by positivity
  nlinarith only [hL2, hs, ht2, hid, hp]

theorem exists_lens_control {α φ r₀ r₁ : ℝ} (B : ℂ)
    (hwidth : 0 < Lens.width (length φ r₀ r₁) (framed (α + direction φ r₀ r₁) B).im)
    (hp : ‖((r₀ : ℂ) * unit (α - φ) + (r₁ : ℂ) * unit (α + φ)) + B‖ ≤ 2)
    (hm : ‖((r₀ : ℂ) * unit (α - φ) + (r₁ : ℂ) * unit (α + φ)) - B‖ ≤ 2) :
    ∃ σ : ℝ, |σ| ≤ 1 ∧
      B = increment (α + direction φ r₀ r₁) (length φ r₀ r₁) σ (framed (α + direction φ r₀ r₁) B).im := by
  let β := α + direction φ r₀ r₁
  let x := (framed β B).re
  let t := (framed β B).im
  have he : B = unit β * ((x : ℂ) + (t : ℂ) * I) := (framed_reconstruction β B).symm
  have hL : 0 ≤ length φ r₀ r₁ := norm_nonneg _
  rw [← rotated_length_direction α φ r₀ r₁] at hp hm
  rw [he] at hp hm
  have hpair : (length φ r₀ r₁ + x) ^ 2 + t ^ 2 ≤ 4 ∧
      (length φ r₀ r₁ - x) ^ 2 + t ^ 2 ≤ 4 := by
    constructor
    · have hh := pow_le_pow_left₀ (norm_nonneg _) hp 2
      rwa [Lens.norm_sq_rotated_plus (norm_unit β), show (2 : ℝ) ^ 2 = 4 by norm_num] at hh
    · have hh := pow_le_pow_left₀ (norm_nonneg _) hm 2
      rwa [Lens.norm_sq_rotated_minus (norm_unit β), show (2 : ℝ) ^ 2 = 4 by norm_num] at hh
  have ht := Lens.constraints_imply_height_bound hpair.1
  obtain ⟨σ, hσ, hx⟩ := (Lens.exists_normalized_iff hL ht hwidth).mp hpair
  refine ⟨σ, hσ, ?_⟩
  change B = unit β * (((σ * Lens.width (length φ r₀ r₁) t : ℝ) : ℂ) + (t : ℂ) * I)
  rw [← hx]
  exact he

end
end StructuralNote.MatchingActivityRadialLens
