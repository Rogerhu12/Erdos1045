import StructuralNote.CommonFiberGeometry
import EventualExact.NonlocalFeasibility

/-! Projection estimates for nonlocal chords. Tangential center increments
are charged only after changing from their own direction to the chord's
mean direction, giving the additional angular factor. -/

namespace StructuralNote.CommonFiberNonlocalProjection

open Erdos1045.EventualExact LensClosure CommonFiberGeometry Complex
open scoped BigOperators
noncomputable section

def radial (u b : ℂ) : ℝ := ((starRingEnd ℂ) u * b).re

theorem radial_change_bound (u v b : ℂ) :
    |radial u b| ≤ |radial v b| + ‖u - v‖ * ‖b‖ := by
  have he : radial u b = radial v b + radial (u - v) b := by
    simp only [radial, map_sub, sub_mul, Complex.sub_re]
    ring
  rw [he]
  have hb := Complex.abs_re_le_norm ((starRingEnd ℂ) (u - v) * b)
  simp only [norm_mul, Complex.norm_conj] at hb
  exact (abs_add_le _ _).trans (add_le_add le_rfl hb)

theorem radial_sum {ι : Type*} (s : Finset ι) (u : ℂ) (b : ι → ℂ) :
    radial u (∑ j ∈ s, b j) = ∑ j ∈ s, radial u (b j) := by
  simp only [radial, Finset.mul_sum, Complex.re_sum]

theorem radial_sum_bound {ι : Type*} (s : Finset ι) (u : ℂ) (a b : ι → ℂ)
    {R B δ : ℝ}
    (hr : ∀ j ∈ s, |radial (a j) (b j)| ≤ R)
    (hb : ∀ j ∈ s, ‖b j‖ ≤ B) (hd : ∀ j ∈ s, ‖u - a j‖ ≤ δ) :
    |radial u (∑ j ∈ s, b j)| ≤ s.card * (R + δ * B) := by
  rw [radial_sum]
  calc
    _ ≤ ∑ j ∈ s, |radial u (b j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ s, (R + δ * B) := by
      apply Finset.sum_le_sum
      intro j hj
      have hm := mul_le_mul (hd j hj) (hb j hj) (norm_nonneg _) (le_trans (norm_nonneg _) (hd j hj))
      exact (radial_change_bound u (a j) (b j)).trans (add_le_add (hr j hj) hm)
    _ = _ := by simp; ring

theorem norm_sum_bound {ι : Type*} (s : Finset ι) (b : ι → ℂ) {B : ℝ}
    (hb : ∀ j ∈ s, ‖b j‖ ≤ B) : ‖∑ j ∈ s, b j‖ ≤ s.card * B := by
  calc
    _ ≤ ∑ j ∈ s, ‖b j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ s, B := Finset.sum_le_sum hb
    _ = _ := by simp

theorem norm_add_unit_real_sq (α r : ℝ) (b : ℂ) :
    ‖unit α * (r : ℂ) + b‖ ^ 2 = r ^ 2 + 2 * r * radial (unit α) b + ‖b‖ ^ 2 := by
  have hu : (unit α).re ^ 2 + (unit α).im ^ 2 = 1 := by
    rw [unit_re, unit_im]
    nlinarith [Real.sin_sq_add_cos_sq α]
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    zero_add, radial, Complex.conj_re, Complex.conj_im]
  nlinarith [show ((unit α).re ^ 2 + (unit α).im ^ 2) * r ^ 2 = r ^ 2 by rw [hu, one_mul]]

theorem unit_pair_mean (α β : ℝ) :
    unit α + unit β = unit ((α + β) / 2) * (2 * Real.cos ((β - α) / 2) : ℝ) := by
  have h₁ : α = (α + β) / 2 - (β - α) / 2 := by ring
  have h₂ : β = (α + β) / 2 + (β - α) / 2 := by ring
  simpa only [← h₁, ← h₂] using unit_pair ((α + β) / 2) ((β - α) / 2)

theorem pair_distance_sq_bound (α β : ℝ) (b : ℂ) {R B : ℝ}
    (hr : |radial (unit ((α + β) / 2)) b| ≤ R) (hb : ‖b‖ ≤ B) :
    ‖unit α + unit β + b‖ ^ 2 ≤ 4 * Real.cos ((β - α) / 2) ^ 2 + 4 * R + B ^ 2 := by
  rw [unit_pair_mean, norm_add_unit_real_sq]
  have hc : |Real.cos ((β - α) / 2)| ≤ 1 := Real.abs_cos_le_one _
  have hc' : 2 * (2 * Real.cos ((β - α) / 2)) * radial (unit ((α + β) / 2)) b ≤ 4 * R := by
    have hm := mul_le_mul hc hr (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have ha := le_abs_self (Real.cos ((β - α) / 2) * radial (unit ((α + β) / 2)) b)
    rw [abs_mul] at ha
    nlinarith
  have hsq := pow_le_pow_left₀ (norm_nonneg b) hb 2
  nlinarith

end
end StructuralNote.CommonFiberNonlocalProjection
