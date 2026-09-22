import Erdos1045.ClosedHullSupport

/-! The support integral of the concrete regular polygon, evaluated on one
fundamental angular sector and extended by its exact rotational periodicity. -/

namespace Erdos1045.HullGeometry

open Configuration MeasureTheory
noncomputable section

theorem regular_projection (n : ℕ) (i : Fin n) (t : ℝ) :
    (regular n i * Complex.exp (-((t : ℂ) * Complex.I))).re =
      Real.cos (2 * Real.pi * (i : ℝ) / n - t) := by
  rw [point_projection]
  simp [regular, Complex.exp_re, Complex.exp_im, Real.cos_sub]

theorem regular_projection_le_cos {n : ℕ} (hn : 0 < n) (i : Fin n)
    {t : ℝ} (ht₁ : -(Real.pi / n) ≤ t) (ht₂ : t ≤ Real.pi / n) :
    Real.cos (2 * Real.pi * (i : ℝ) / n - t) ≤ Real.cos t := by
  by_cases hi : (i : ℕ) = 0
  · simp [hi, Real.cos_neg]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hiR : 1 ≤ (i : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hi)
  have hin : (i : ℝ) + 1 ≤ n := by exact_mod_cast (i.isLt)
  have hα₀ : 0 ≤ Real.pi * (i : ℝ) / n := by positivity
  have hαπ : Real.pi * (i : ℝ) / n ≤ Real.pi := by
    apply (div_le_iff₀ hnR).mpr
    nlinarith [Real.pi_pos]
  have hβ₀ : 0 ≤ Real.pi * (i : ℝ) / n - t := by
    have : Real.pi / n ≤ Real.pi * (i : ℝ) / n :=
      div_le_div_of_nonneg_right (by nlinarith [Real.pi_pos]) hnR.le
    linarith
  have hβπ : Real.pi * (i : ℝ) / n - t ≤ Real.pi := by
    have : Real.pi * (i : ℝ) / n + Real.pi / n ≤ Real.pi := by
      rw [← add_div]
      apply (div_le_iff₀ hnR).mpr
      nlinarith [Real.pi_pos]
    linarith
  have hs := mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hα₀ hαπ)
    (Real.sin_nonneg_of_nonneg_of_le_pi hβ₀ hβπ)
  have hid : Real.cos t - Real.cos (2 * Real.pi * (i : ℝ) / n - t) =
      2 * Real.sin (Real.pi * (i : ℝ) / n) *
        Real.sin (Real.pi * (i : ℝ) / n - t) := by
    rw [Real.cos_sub_cos]
    have h₁ : (t + (2 * Real.pi * (i : ℝ) / n - t)) / 2 =
        Real.pi * (i : ℝ) / n := by ring
    have h₂ : (t - (2 * Real.pi * (i : ℝ) / n - t)) / 2 =
        -(Real.pi * (i : ℝ) / n - t) := by ring
    rw [h₁, h₂, Real.sin_neg]
    ring
  linarith

theorem regular_support_sector {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht₁ : -(Real.pi / n) ≤ t) (ht₂ : t ≤ Real.pi / n) :
    support (regular n) t = Real.cos t := by
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_, Set.mem_range_self (⟨0, hn⟩ : Fin n)⟩
    · rintro a ⟨i, rfl⟩
      dsimp only
      rw [regular_projection]
      exact regular_projection_le_cos hn i ht₁ ht₂
  · have h := projection_le_support (regular n) (⟨0, hn⟩ : Fin n) t
    rw [regular_projection] at h
    simpa using h

theorem regular_projection_rotate {n : ℕ} (hn : 0 < n) (i : Fin n) (t : ℝ) :
    (regular n (finRotate n i) *
      Complex.exp (-(((t + 2 * Real.pi / n : ℝ) : ℂ) * Complex.I))).re =
      (regular n i * Complex.exp (-((t : ℂ) * Complex.I))).re := by
  rw [regular_projection, regular_projection]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hnR : (m + 1 : ℝ) ≠ 0 := by positivity
  by_cases hi : i = Fin.last m
  · subst i
    rw [finRotate_last]
    simp only [Fin.val_zero, Fin.val_last, Nat.cast_zero, Nat.cast_succ,
      mul_zero, zero_div]
    have h : 0 - (t + 2 * Real.pi / (m + 1)) =
        (2 * Real.pi * m / (m + 1) - t) - 2 * Real.pi := by
      field_simp
      ring
    rw [h, Real.cos_sub_two_pi]
  · rw [show (finRotate (m + 1) i : ℝ) = (i : ℝ) + 1 by
      exact_mod_cast (coe_finRotate_of_ne_last hi)]
    congr 1
    push_cast
    ring

theorem regular_support_periodic {n : ℕ} (hn : 0 < n) :
    Function.Periodic (support (regular n)) (2 * Real.pi / n) := by
  intro t
  unfold support
  congr 1
  ext a
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨j, rfl⟩ := (finRotate n).surjective i
    exact ⟨j, (regular_projection_rotate hn j t).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨finRotate n i, regular_projection_rotate hn i t⟩

theorem hullPerimeter_regular_proved (n : ℕ) (hn : 3 ≤ n) :
    hullPerimeter (regular n) = circlePerimeter n := by
  have hn₀ : 0 < n := by omega
  have hnR : (n : ℝ) ≠ 0 := by positivity
  have hp := regular_support_periodic hn₀
  have hi := hp.intervalIntegral_add_zsmul_eq (n : ℤ) 0
    ((support_continuous (regular n)).intervalIntegrable)
  have hmul : (n : ℤ) • (2 * Real.pi / n) = 2 * Real.pi := by
    simp only [zsmul_eq_mul, Int.cast_natCast]
    field_simp
  simp only [zero_add, hmul, zsmul_eq_mul, Int.cast_natCast] at hi
  have hshift := hp.intervalIntegral_add_eq 0 (-(Real.pi / n))
  have hend : -(Real.pi / n) + 2 * Real.pi / n = Real.pi / n := by ring
  simp only [zero_add, hend] at hshift
  have hsector : (∫ t in -(Real.pi / n)..(Real.pi / n), support (regular n) t) =
      2 * Real.sin (Real.pi / n) := by
    calc
      _ = ∫ t in -(Real.pi / n)..(Real.pi / n), Real.cos t := by
        apply intervalIntegral.integral_congr
        intro t ht
        have hnonneg : 0 ≤ Real.pi / n := by positivity
        rw [Set.uIcc_of_le (by linarith)] at ht
        exact regular_support_sector hn₀ ht.1 ht.2
      _ = _ := by rw [integral_cos, Real.sin_neg]; ring
  unfold hullPerimeter circlePerimeter
  rw [hi, hshift, hsector]
  ring

end
end Erdos1045.HullGeometry
