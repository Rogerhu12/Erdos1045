import StructuralNote.CommonClosureIncrements
import EventualExact.LensClosureSmooth

/-! Actual common-parameter closure roots, obtained from the linear tangential closure.
The source estimate is proved from the square-root and cosine formulas. -/

namespace StructuralNote.CommonClosureExistence

open Erdos1045.EventualExact Erdos1045.EventualExact.LensClosure
open Complex Set Metric
open scoped BigOperators Topology ContDiff
noncomputable section

theorem cosine_width_abs_le {t : ℝ} (a : ℝ) (ht : t ^ 2 ≤ 4) :
    |Lens.width (2 * Real.cos a) t| ≤ t ^ 2 / 2 + a ^ 2 := by
  have hh := BoxLensLift.height_defect ht
  have hc : |2 - 2 * Real.cos a| ≤ a ^ 2 := by
    rw [abs_of_nonneg (by linarith [Real.cos_le_one a])]
    linarith [Real.one_sub_sq_div_two_le_cos (x := a)]
  have he : Lens.width (2 * Real.cos a) t = (Lens.height t - 2) + (2 - 2 * Real.cos a) := by
    unfold Lens.width
    ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hh hc)

theorem increment_source_bound (α μ L s t : ℝ) (hs : |s| ≤ 1) :
    ‖increment α L s t - unit μ * ((t : ℂ) * I)‖ ≤
      |Lens.width L t| + |α - μ| * |t| := by
  have he : increment α L s t - unit μ * ((t : ℂ) * I) =
      unit α * ((s * Lens.width L t : ℝ) : ℂ) +
        (unit α - unit μ) * ((t : ℂ) * I) := by
    unfold increment
    ring
  rw [he]
  calc
    _ ≤ ‖unit α * ((s * Lens.width L t : ℝ) : ℂ)‖ +
        ‖(unit α - unit μ) * ((t : ℂ) * I)‖ := norm_add_le _ _
    _ = |s| * |Lens.width L t| + ‖unit α - unit μ‖ * |t| := by
      simp only [norm_mul, norm_unit, Complex.norm_real, Real.norm_eq_abs,
        norm_I, mul_one, one_mul]
    _ ≤ _ := add_le_add
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hs (abs_nonneg (Lens.width L t)))
      (mul_le_mul_of_nonneg_right (norm_unit_sub_le α μ) (abs_nonneg t))

/-- Tangential closure cancels the entire linear source before its norm is estimated. -/
theorem closure_source_bound {m : ℕ} (α L s t : Fin m → ℝ) (hs : ∀ j, |s j| ≤ 1)
    (hclosed : (∑ j, unit (midpoint m j) * ((t j : ℂ) * I)) = 0) :
    ‖closure α L s t 0‖ ≤
      ∑ j, (|Lens.width (L j) (t j)| + |α j - midpoint m j| * |t j|) := by
  have he : closure α L s t 0 = ∑ j,
      (increment (α j) (L j) (s j) (t j) - unit (midpoint m j) * ((t j : ℂ) * I)) := by
    rw [Finset.sum_sub_distrib, hclosed, sub_zero]
    simp only [LensClosure.closure, heightParameter, map_zero, add_zero]
  rw [he]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ =>
    increment_source_bound _ _ _ _ _ (hs j))

/-- An explicit geometric source estimate in terms of angle and tangential sizes. -/
theorem closure_geometric_source {m : ℕ} (α a s t : Fin m → ℝ)
    {e d h : ℝ} (hh : h ≤ 1) (hs : ∀ j, |s j| ≤ 1)
    (he : ∀ j, |α j - midpoint m j| ≤ e)
    (hd : ∀ j, |a j| ≤ d) (ht : ∀ j, |t j| ≤ h)
    (hclosed : (∑ j, unit (midpoint m j) * ((t j : ℂ) * I)) = 0) :
    ‖closure α (fun j => 2 * Real.cos (a j)) s t 0‖ ≤
      m * (h ^ 2 / 2 + d ^ 2 + e * h) := by
  calc
    _ ≤ ∑ j, (|Lens.width (2 * Real.cos (a j)) (t j)| + |α j - midpoint m j| * |t j|) :=
      closure_source_bound α _ s t hs hclosed
    _ ≤ ∑ _j : Fin m, (h ^ 2 / 2 + d ^ 2 + e * h) := by
      apply Finset.sum_le_sum
      intro j _
      have hh0 : 0 ≤ h := (abs_nonneg _).trans (ht j)
      have hd0 : 0 ≤ d := (abs_nonneg _).trans (hd j)
      have ht2 : (t j) ^ 2 ≤ h ^ 2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hh0).mpr (ht j)
      have ha2 : (a j) ^ 2 ≤ d ^ 2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hd0).mpr (hd j)
      have ht4 : (t j) ^ 2 ≤ 4 := by nlinarith
      have hw := cosine_width_abs_le (a j) ht4
      have hm := mul_le_mul (he j) (ht j) (abs_nonneg _) ((abs_nonneg _).trans (he j))
      nlinarith only [hw, ht2, ha2, hm]
    _ = _ := by simp; ring

/-- Common continuous parameters determine a unique small closure root for every sign word. -/
theorem exists_unique_geometric_root {m : ℕ} (hm : 2 ≤ m) (α a s t : Fin m → ℝ)
    {e d h R : ℝ} (hR : 0 ≤ R) (hh : h ≤ 1)
    (hs : ∀ j, |s j| ≤ 1)
    (he : ∀ j, |α j - midpoint m j| ≤ e)
    (hd : ∀ j, |a j| ≤ d) (ht : ∀ j, |t j| ≤ h)
    (hclosed : (∑ j, unit (midpoint m j) * ((t j : ℂ) * I)) = 0)
    (hsmall : e + h + R ≤ 1 / 4)
    (hradius : 4 * (h ^ 2 / 2 + d ^ 2 + e * h) ≤ R) :
    ∃! ξ : ℂ, ‖ξ‖ ≤ R ∧ closure α (fun j => 2 * Real.cos (a j)) s t ξ = 0 := by
  apply exists_unique_closure_root hm α (fun j => 2 * Real.cos (a j)) s t hR hs
  · intro j
    linarith [he j, ht j]
  · have hb := closure_geometric_source α a s t hh hs he hd ht hclosed
    have hc := mul_le_mul_of_nonneg_left hradius (show (0 : ℝ) ≤ m by positivity)
    nlinarith only [hb, hc]

/-- The same root lies on a genuinely smooth local branch of the actual closure equation. -/
theorem geometric_root_smooth {m : ℕ} (hm : 2 ≤ m) (α a s t : Fin m → ℝ)
    {R : ℝ} (hs : ∀ j, |s j| ≤ 1)
    (hsmall : ∀ j, |α j - midpoint m j| + |t j| + R ≤ 1 / 4)
    {ξ : ℂ} (hξ : ‖ξ‖ ≤ R) (hzero : closure α (fun j => 2 * Real.cos (a j)) s t ξ = 0) :
    let p : Parameters m := (α, (fun j => 2 * Real.cos (a j)), s, t)
    ∃ g : Parameters m → ℂ, g p = ξ ∧ ContDiffAt ℝ ∞ g p ∧
      (∀ᶠ p' in 𝓝 p, closureFamily p' (g p') = 0) ∧
      (∀ᶠ z in 𝓝 (p, ξ), closureFamily z.1 z.2 = 0 ↔ g z.1 = z.2) := by
  exact exists_smooth_closure_root hm _ ξ hs
    (ball_height_small α t hsmall (mem_closedBall_zero_iff.mpr hξ)) hzero

end
end StructuralNote.CommonClosureExistence
