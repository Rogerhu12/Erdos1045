import Erdos1045.ClosedHullSupport

namespace Erdos1045.HullGeometry

open Configuration
noncomputable section

theorem projection_affine (a b w : ℂ) (t : ℝ) :
    ((a + b * w) * Complex.exp (-((t : ℂ) * Complex.I))).re =
      (a * Complex.exp (-((t : ℂ) * Complex.I))).re +
        ‖b‖ * (w * Complex.exp (-(((t - b.arg : ℝ) : ℂ) * Complex.I))).re := by
  have hb := Complex.norm_mul_exp_arg_mul_I b
  have he : b * Complex.exp (-((t : ℂ) * Complex.I)) =
      (‖b‖ : ℂ) * Complex.exp (-(((t - b.arg : ℝ) : ℂ) * Complex.I)) := by
    nth_rw 1 [← hb]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [add_mul, Complex.add_re]
  congr 1
  have he' : b * w * Complex.exp (-((t : ℂ) * Complex.I)) =
      (‖b‖ : ℂ) * (w * Complex.exp (-(((t - b.arg : ℝ) : ℂ) * Complex.I))) := by
    calc
      _ = w * (b * Complex.exp (-((t : ℂ) * Complex.I))) := by ring
      _ = _ := by rw [he]; ring
  rw [he']
  simp

theorem support_affine {n : ℕ} (hn : 0 < n) (z : Points n) (a b : ℂ) (t : ℝ) :
    support (fun i => a + b * z i) t =
      (a * Complex.exp (-((t : ℂ) * Complex.I))).re + ‖b‖ * support z (t - b.arg) := by
  let i₀ : Fin n := ⟨0, hn⟩
  have hne : (Set.range (fun i : Fin n =>
      (z i * Complex.exp (-(((t - b.arg : ℝ) : ℂ) * Complex.I))).re)).Nonempty :=
    ⟨_, Set.mem_range_self i₀⟩
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_, Set.mem_range_self i₀⟩
    · rintro x ⟨i, rfl⟩
      dsimp only
      rw [projection_affine]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (projection_le_support z i (t - b.arg)) (norm_nonneg b))
  · obtain ⟨i, hi⟩ := hne.csSup_mem (Set.finite_range (fun i : Fin n =>
      (z i * Complex.exp (-(((t - b.arg : ℝ) : ℂ) * Complex.I))).re))
    change (z i * Complex.exp (-(((t - b.arg : ℝ) : ℂ) * Complex.I))).re =
      support z (t - b.arg) at hi
    rw [← hi, ← projection_affine]
    exact projection_le_support (fun i => a + b * z i) i t

theorem hullPerimeter_affine_proved (n : ℕ) (z : Points n) (a b : ℂ) :
    hullPerimeter (fun i => a + b * z i) = ‖b‖ * hullPerimeter z := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hullPerimeter_empty]
  unfold hullPerimeter
  simp_rw [support_affine hn]
  have hc : Continuous (fun t : ℝ =>
      (a * Complex.exp (-((t : ℂ) * Complex.I))).re) := by fun_prop
  have hs : Continuous (fun t => ‖b‖ * support z (t - b.arg)) :=
    ((support_continuous z).comp (continuous_id.sub continuous_const)).const_mul _
  rw [intervalIntegral.integral_add (hc.intervalIntegrable _ _) (hs.intervalIntegrable _ _),
    projection_integral, zero_add, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_right]
  have hp := (support_periodic z).intervalIntegral_add_eq (-b.arg) 0
  congr 1
  simpa only [zero_sub, zero_add, sub_eq_add_neg, add_comm, add_zero] using hp

end
end Erdos1045.HullGeometry
