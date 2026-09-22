import EventualExact.CotangentForce
import Erdos1045.CirclePotential
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Secants of the actual negative cotangent, with quantitative lower bounds.
The diagonal value is the derivative, so the same weight works when the two
consecutive angular distances happen to coincide. -/

namespace Erdos1045.EventualExact.CotangentSecant

open Set
open Erdos1045.CirclePotential

noncomputable section

def slope (x y : ℝ) : ℝ :=
  if x = y then second x else (first y - first x) / (y - x)

theorem first_eq_neg_cot (x : ℝ) : first x = -circleCot (x / 2) := by
  simp only [first, circleCot, neg_div]

theorem slope_symm (x y : ℝ) : slope y x = slope x y := by
  by_cases h : x = y
  · subst y
    rfl
  · simp only [slope, if_neg h, if_neg (Ne.symm h)]
    field_simp
    ring

theorem first_difference (x y : ℝ) : first y - first x = slope x y * (y - x) := by
  by_cases h : x = y
  · subst y
    simp
  · rw [slope, if_neg h, div_mul_cancel₀ _ (sub_ne_zero.mpr (Ne.symm h))]

theorem first_complement (x : ℝ) : first (2 * Real.pi - x) = -first x := by
  simp only [first]
  rw [show (2 * Real.pi - x) / 2 = Real.pi - x / 2 by ring,
    Real.sin_pi_sub, Real.cos_pi_sub]
  ring

theorem second_complement (x : ℝ) : second (2 * Real.pi - x) = second x := by
  simp only [second]
  rw [show (2 * Real.pi - x) / 2 = Real.pi - x / 2 by ring, Real.sin_pi_sub]

theorem slope_complement (x y : ℝ) :
    slope (2 * Real.pi - x) (2 * Real.pi - y) = slope x y := by
  by_cases h : x = y
  · subst y
    simp [slope, second_complement]
  · have hc : 2 * Real.pi - x ≠ 2 * Real.pi - y := by intro he; apply h; linarith
    rw [slope, if_neg hc, slope, if_neg h, first_complement, first_complement]
    field_simp
    ring

/-- A secant equals a derivative at a point between its endpoints. -/
theorem exists_derivative {x y : ℝ} (hx : x ∈ arc) (hy : y ∈ arc) :
    ∃ z ∈ Icc (min x y) (max x y), z ∈ arc ∧ slope x y = second z := by
  have hforward {a b : ℝ} (ha : a ∈ arc) (hb : b ∈ arc) (hab : a < b) :
      ∃ z ∈ Ioo a b, slope a b = second z := by
    have hsub : Icc a b ⊆ arc := fun z hz => ⟨ha.1.trans_le hz.1, hz.2.trans_lt hb.2⟩
    have hcont : ContinuousOn first (Icc a b) := fun z hz =>
      (first_hasDerivAt (hsub hz)).continuousAt.continuousWithinAt
    obtain ⟨z, hz, he⟩ := exists_hasDerivAt_eq_slope first second hab hcont
      (fun z hz => first_hasDerivAt (hsub ⟨hz.1.le, hz.2.le⟩))
    exact ⟨z, hz, by rw [slope, if_neg hab.ne]; exact he.symm⟩
  rcases lt_trichotomy x y with h | h | h
  · obtain ⟨z, hz, he⟩ := hforward hx hy h
    exact ⟨z, by simpa [min_eq_left h.le, max_eq_right h.le] using
      (show z ∈ Icc x y from ⟨hz.1.le, hz.2.le⟩),
      ⟨hx.1.trans hz.1, hz.2.trans hy.2⟩, he⟩
  · subst y
    exact ⟨x, by simp, hx, by simp [slope]⟩
  · obtain ⟨z, hz, he⟩ := hforward hy hx h
    refine ⟨z, ?_, ⟨hy.1.trans hz.1, hz.2.trans hx.2⟩, ?_⟩
    · simpa [min_eq_right h.le, max_eq_left h.le] using
        (show z ∈ Icc y x from ⟨hz.1.le, hz.2.le⟩)
    · rw [← slope_symm]
      exact he

theorem slope_pos {x y : ℝ} (hx : x ∈ arc) (hy : y ∈ arc) : 0 < slope x y := by
  obtain ⟨z, _, hz, he⟩ := exists_derivative hx hy
  rw [he, second]
  have hs := sin_half_pos hz
  positivity

/-- An upper bound on both angular distances gives a lower bound on the secant. -/
theorem slope_lower_of_upper {x y H : ℝ} (hx : x ∈ arc) (hy : y ∈ arc)
    (hxH : x ≤ H) (hyH : y ≤ H) : 2 / H ^ 2 ≤ slope x y := by
  obtain ⟨z, hzI, hz, he⟩ := exists_derivative hx hy
  have hH : 0 < H := hx.1.trans_le hxH
  have hzH : z ≤ H := hzI.2.trans (max_le hxH hyH)
  have hc := correctedSecond_nonneg hz
  have hbase : 2 / z ^ 2 ≤ second z := by
    unfold correctedSecond at hc
    linarith
  rw [he]
  apply le_trans ?_ hbase
  apply (div_le_div_iff₀ (sq_pos_of_pos hH) (sq_pos_of_pos hz.1)).mpr
  nlinarith [(sq_le_sq₀ hz.1.le hH.le).mpr hzH]

theorem slope_lower_of_complement_upper {x y H : ℝ}
    (hx : x ∈ arc) (hy : y ∈ arc)
    (hxH : 2 * Real.pi - x ≤ H) (hyH : 2 * Real.pi - y ≤ H) :
    2 / H ^ 2 ≤ slope x y := by
  rw [← slope_complement]
  apply slope_lower_of_upper
  · exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  · exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
  · exact hxH
  · exact hyH

end
end Erdos1045.EventualExact.CotangentSecant
