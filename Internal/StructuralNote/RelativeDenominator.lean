import EventualExact.AntipodalLogRemainder
import Mathlib.Analysis.Real.Sqrt

/-! Relative quadratic denominator replacement in (9.24). Both configurations
share the same perturbed denominator. This preserves a factor of their difference. -/

noncomputable section
open scoped BigOperators

namespace StructuralNote.RelativeDenominator

open Erdos1045.EventualExact

def factor (δ : ℂ) : ℂ := 1 / (1 + δ) ^ 2 - 1

def correction (z δ : ℂ) : ℂ := (z / (1 + δ)) ^ 2 - z ^ 2

theorem denominator_norm_lower {δ : ℂ} (hδ : ‖δ‖ ≤ 1 / 2) :
    (1 : ℝ) / 2 ≤ ‖1 + δ‖ := by
  have hh := norm_sub_norm_le (1 : ℂ) (-δ)
  simpa only [norm_one, norm_neg, sub_neg_eq_add] using
    (show (1 : ℝ) / 2 ≤ ‖1 - -δ‖ by
      have hh' : 1 - ‖δ‖ ≤ ‖1 - -δ‖ := by simpa using hh
      linarith)

theorem factor_identity {δ : ℂ} (hδ : 1 + δ ≠ 0) :
    factor δ = -(δ * (2 + δ)) / (1 + δ) ^ 2 := by
  unfold factor
  field_simp
  ring

theorem factor_bound {δ : ℂ} (hδ : ‖δ‖ ≤ 1 / 2) : ‖factor δ‖ ≤ 10 * ‖δ‖ := by
  have hd := denominator_norm_lower hδ
  have hdp : 0 < ‖1 + δ‖ := by linarith
  have hdn := norm_pos_iff.mp hdp
  rw [factor_identity hdn, norm_div, norm_neg, norm_mul, norm_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hdp)).2
  have hn := norm_add_le (2 : ℂ) δ
  norm_num only [Complex.norm_ofNat] at hn
  have hd2 : 1 / 4 ≤ ‖1 + δ‖ ^ 2 := by nlinarith
  have hm := mul_nonneg (norm_nonneg δ) (sub_nonneg.mpr hd2)
  have hh := mul_le_mul_of_nonneg_left hn (norm_nonneg δ)
  have hh' := mul_nonneg (norm_nonneg δ) (sub_nonneg.mpr hδ)
  nlinarith

theorem correction_identity (z δ : ℂ) : correction z δ = z ^ 2 * factor δ := by
  unfold correction factor
  rw [div_pow]
  ring

theorem correction_difference {r : ℝ} {z w δ : ℂ}
    (hz : ‖z‖ ≤ r) (hw : ‖w‖ ≤ r) (hδ : ‖δ‖ ≤ 1 / 2) :
    ‖correction z δ - correction w δ‖ ≤ 20 * r * ‖z - w‖ * ‖δ‖ := by
  have hr : 0 ≤ r := (norm_nonneg z).trans hz
  have hs : ‖z + w‖ ≤ 2 * r := (norm_add_le z w).trans (by linarith)
  have he : correction z δ - correction w δ = (z - w) * (z + w) * factor δ := by
    rw [correction_identity, correction_identity]
    ring
  rw [he, norm_mul, norm_mul]
  calc
    _ ≤ ‖z - w‖ * (2 * r) * (10 * ‖δ‖) := by
      gcongr
      exact factor_bound hδ
    _ = _ := by ring

def quadraticCorrection {ι : Type*} [Fintype ι] (ρ δ : ι → ℂ) : ℝ :=
  -(∑ i, (correction (ρ i) (δ i)).re) / 2

/-- The error of replacing true denominators in two configurations, with the
shared denominator perturbation retained in an L² factor. -/
theorem quadratic_correction_difference {ι : Type*} [Fintype ι] {r : ℝ}
    (hr : 0 ≤ r) (ρ τ δ : ι → ℂ)
    (hρ : ∀ i, ‖ρ i‖ ≤ r) (hτ : ∀ i, ‖τ i‖ ≤ r)
    (hδ : ∀ i, ‖δ i‖ ≤ 1 / 2) :
    |quadraticCorrection ρ δ - quadraticCorrection τ δ| ≤
      10 * r * Real.sqrt (∑ i, ‖ρ i - τ i‖ ^ 2) * Real.sqrt (∑ i, ‖δ i‖ ^ 2) := by
  have hs : |(∑ i, (correction (ρ i) (δ i)).re) -
      (∑ i, (correction (τ i) (δ i)).re)| ≤
      20 * r * ∑ i, ‖ρ i - τ i‖ * ‖δ i‖ := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    have hh := (Complex.abs_re_le_norm (correction (ρ i) (δ i) - correction (τ i) (δ i))).trans
      (correction_difference (hρ i) (hτ i) (hδ i))
    simpa only [Complex.sub_re, mul_assoc] using hh
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun i => ‖ρ i - τ i‖) (fun i => ‖δ i‖)
  have hall := hs.trans (mul_le_mul_of_nonneg_left hcs (by positivity : 0 ≤ 20 * r))
  have he : quadraticCorrection ρ δ - quadraticCorrection τ δ =
      -((∑ i, (correction (ρ i) (δ i)).re) -
        (∑ i, (correction (τ i) (δ i)).re)) / 2 := by
    unfold quadraticCorrection
    ring
  rw [he, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hh := div_le_div_of_nonneg_right hall (by norm_num : (0 : ℝ) ≤ 2)
  calc
    _ ≤ (20 * r * (Real.sqrt (∑ i, ‖ρ i - τ i‖ ^ 2) *
        Real.sqrt (∑ i, ‖δ i‖ ^ 2))) / 2 := hh
    _ = _ := by ring

theorem correction_actual (c d w : ℂ) (hw : w ≠ 0) :
    correction (c / w) ((d - w) / w) = (c / d) ^ 2 - (c / w) ^ 2 := by
  have he : 1 + (d - w) / w = d / w := by field_simp; ring
  rw [correction, he, div_div_div_cancel_right₀ hw]

def potential {ι : Type*} [Fintype ι] (c d : ι → ℂ) : ℝ :=
  -(∑ i, ((c i / d i) ^ 2).re) / 2

theorem potential_change {ι : Type*} [Fintype ι] (c d w : ι → ℂ)
    (hw : ∀ i, w i ≠ 0) :
    potential c d - potential c w =
      quadraticCorrection (fun i => c i / w i) (fun i => (d i - w i) / w i) := by
  simp only [potential, quadraticCorrection, correction_actual _ _ _ (hw _),
    Complex.sub_re, Finset.sum_sub_distrib]
  ring

/-- Direct form for actual numerators and shared physical denominators. -/
theorem actual_potential_change_difference {ι : Type*} [Fintype ι] {r : ℝ}
    (hr : 0 ≤ r) (c c' d w : ι → ℂ) (hw : ∀ i, w i ≠ 0)
    (hc : ∀ i, ‖c i / w i‖ ≤ r) (hc' : ∀ i, ‖c' i / w i‖ ≤ r)
    (hd : ∀ i, ‖(d i - w i) / w i‖ ≤ 1 / 2) :
    |(potential c d - potential c w) - (potential c' d - potential c' w)| ≤
      10 * r * Real.sqrt (∑ i, ‖(c i - c' i) / w i‖ ^ 2) *
        Real.sqrt (∑ i, ‖(d i - w i) / w i‖ ^ 2) := by
  rw [potential_change c d w hw, potential_change c' d w hw]
  have hh := quadratic_correction_difference hr (fun i => c i / w i)
    (fun i => c' i / w i) (fun i => (d i - w i) / w i) hc hc' hd
  simpa only [sub_div] using hh

end StructuralNote.RelativeDenominator
