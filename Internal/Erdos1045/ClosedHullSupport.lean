import Erdos1045.ClosedGeometry
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! Positivity and inclusion monotonicity of the concrete support integral.
No convex-geometry interface is assumed in these proofs. -/

namespace Erdos1045.HullGeometry

open Configuration MeasureTheory
noncomputable section

theorem support_continuous {n : ℕ} (z : Points n) : Continuous (support z) :=
  (support_joint_continuous n).comp (continuous_const.prodMk continuous_id)

theorem point_projection (a : ℂ) (t : ℝ) :
    (a * Complex.exp (-((t : ℂ) * Complex.I))).re =
      a.re * Real.cos t + a.im * Real.sin t := by
  simp [Complex.mul_re, Complex.exp_re, Complex.exp_im]

theorem projection_integral (a : ℂ) :
    (∫ t in (0 : ℝ)..(2 * Real.pi),
      (a * Complex.exp (-((t : ℂ) * Complex.I))).re) = 0 := by
  simp_rw [point_projection]
  rw [intervalIntegral.integral_add
    ((Real.continuous_cos.const_mul _).intervalIntegrable _ _)
    ((Real.continuous_sin.const_mul _).intervalIntegrable _ _)]
  simp [intervalIntegral.integral_const_mul, integral_cos, integral_sin]

theorem projection_le_support {n : ℕ} (z : Points n) (i : Fin n) (t : ℝ) :
    (z i * Complex.exp (-((t : ℂ) * Complex.I))).re ≤ support z t := by
  exact le_csSup (Set.finite_range _).bddAbove (Set.mem_range_self i)

theorem hullPerimeter_empty (z : Points 0) : hullPerimeter z = 0 := by
  simp [hullPerimeter, support, Set.range_eq_empty]

theorem hullPerimeter_nonneg_proved (n : ℕ) (z : Points n) :
    0 ≤ hullPerimeter z := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [hullPerimeter_empty]
  let i : Fin n := ⟨0, hn⟩
  have hc : Continuous (fun t : ℝ =>
      (z i * Complex.exp (-((t : ℂ) * Complex.I))).re) := by fun_prop
  have h := intervalIntegral.integral_mono (μ := volume) (by positivity : 0 ≤ 2 * Real.pi)
    (hc.intervalIntegrable _ _) ((support_continuous z).intervalIntegrable _ _)
    (projection_le_support z i)
  rw [projection_integral] at h
  exact h

theorem projection_le_support_of_mem_convexHull {n : ℕ} (z : Points n)
    {a : ℂ} (ha : a ∈ convexHull ℝ (Set.range z)) (t : ℝ) :
    (a * Complex.exp (-((t : ℂ) * Complex.I))).re ≤ support z t := by
  apply convexHull_min (t := {a : ℂ |
    (a * Complex.exp (-((t : ℂ) * Complex.I))).re ≤ support z t}) ?_ ?_ ha
  · rintro a ⟨i, rfl⟩
    exact projection_le_support z i t
  · intro a ha b hb r s hr hs hrs
    simp only [Set.mem_ofPred_eq] at *
    simp only [add_mul, Complex.add_re, smul_mul_assoc, Complex.smul_re, smul_eq_mul]
    calc
      _ ≤ r * support z t + s * support z t :=
        add_le_add (mul_le_mul_of_nonneg_left ha hr) (mul_le_mul_of_nonneg_left hb hs)
      _ = support z t := by rw [← add_mul, hrs, one_mul]

theorem support_mono_of_nonempty {n m : ℕ} (hn : 0 < n)
    (z : Points n) (w : Points m)
    (h : Set.range z ⊆ convexHull ℝ (Set.range w)) (t : ℝ) :
    support z t ≤ support w t := by
  apply csSup_le
  · exact ⟨_, Set.mem_range_self (⟨0, hn⟩ : Fin n)⟩
  · rintro a ⟨i, rfl⟩
    exact projection_le_support_of_mem_convexHull w (h (Set.mem_range_self i)) t

theorem hullPerimeter_monotone_proved (n m : ℕ) (z : Points n) (w : Points m)
    (h : Set.range z ⊆ convexHull ℝ (Set.range w)) :
    hullPerimeter z ≤ hullPerimeter w := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [hullPerimeter_empty]
    exact hullPerimeter_nonneg_proved m w
  exact intervalIntegral.integral_mono (by positivity)
    ((support_continuous z).intervalIntegrable _ _) ((support_continuous w).intervalIntegrable _ _)
    (support_mono_of_nonempty hn z w h)

theorem support_periodic {n : ℕ} (z : Points n) :
    Function.Periodic (support z) (2 * Real.pi) := by
  intro t
  simp only [support, point_projection, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem projection_integral_interval (a : ℂ) (x y : ℝ) :
    (∫ t in x..y, (a * Complex.exp (-((t : ℂ) * Complex.I))).re) =
      a.re * (Real.sin y - Real.sin x) +
        a.im * (Real.cos x - Real.cos y) := by
  simp_rw [point_projection]
  rw [intervalIntegral.integral_add
    ((Real.continuous_cos.const_mul _).intervalIntegrable _ _)
    ((Real.continuous_sin.const_mul _).intervalIntegrable _ _)]
  simp [intervalIntegral.integral_const_mul, integral_cos, integral_sin]

theorem projection_arg (a : ℂ) :
    a.re * Real.cos a.arg + a.im * Real.sin a.arg = ‖a‖ := by
  rw [← Complex.norm_mul_cos_arg a, ← Complex.norm_mul_sin_arg a]
  calc
    _ = ‖a‖ * (Real.sin a.arg ^ 2 + Real.cos a.arg ^ 2) := by ring
    _ = ‖a‖ := by rw [Real.sin_sq_add_cos_sq, mul_one]

/-- Integrating each of two vertex projections on the half-circle pointing
toward that vertex gives twice their distance. -/
theorem hullPerimeter_distance_le_half_proved (n : ℕ) (z : Points n)
    (i j : Fin n) : ‖z i - z j‖ ≤ hullPerimeter z / 2 := by
  let θ : ℝ := (z i - z j).arg
  let x : ℝ := θ - Real.pi / 2
  let y : ℝ := θ + Real.pi / 2
  have hxy : x ≤ y := by dsimp [x, y]; linarith [Real.pi_pos]
  have hyx : y ≤ x + 2 * Real.pi := by dsimp [x, y]; linarith [Real.pi_pos]
  have hc (a : ℂ) : Continuous (fun t : ℝ =>
      (a * Complex.exp (-((t : ℂ) * Complex.I))).re) := by fun_prop
  have hi := intervalIntegral.integral_mono (μ := volume) hxy ((hc (z i)).intervalIntegrable _ _)
    ((support_continuous z).intervalIntegrable _ _) (projection_le_support z i)
  have hj := intervalIntegral.integral_mono (μ := volume) hyx ((hc (z j)).intervalIntegrable _ _)
    ((support_continuous z).intervalIntegrable _ _) (projection_le_support z j)
  have hsum := add_le_add hi hj
  rw [intervalIntegral.integral_add_adjacent_intervals
    ((support_continuous z).intervalIntegrable _ _)
    ((support_continuous z).intervalIntegrable _ _)] at hsum
  rw [(support_periodic z).intervalIntegral_add_eq x 0] at hsum
  simp only [zero_add] at hsum
  rw [projection_integral_interval, projection_integral_interval] at hsum
  have hsinx : Real.sin x = -Real.cos θ := by
    simp [x, Real.sin_sub]
  have hcosx : Real.cos x = Real.sin θ := by
    simp [x, Real.cos_sub]
  have hsiny : Real.sin y = Real.cos θ := by
    simp [y, Real.sin_add]
  have hcosy : Real.cos y = -Real.sin θ := by
    simp [y, Real.cos_add]
  rw [Real.sin_add_two_pi, Real.cos_add_two_pi, hsinx, hcosx, hsiny, hcosy] at hsum
  have hnorm := projection_arg (z i - z j)
  change (z i - z j).re * Real.cos θ + (z i - z j).im * Real.sin θ = _ at hnorm
  simp only [Complex.sub_re, Complex.sub_im] at hnorm
  change _ ≤ hullPerimeter z at hsum
  linarith

end
end Erdos1045.HullGeometry
