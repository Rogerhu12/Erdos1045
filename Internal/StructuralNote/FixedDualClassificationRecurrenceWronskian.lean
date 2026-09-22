import StructuralNote.FixedDualClassificationRecurrence

/-! Reflection and exact telescoping of the finite-kernel recurrence. -/

namespace StructuralNote.FixedDualClassificationRecurrenceWronskian

open Real Erdos1045.EventualExact
open FixedDualClassificationKernel FixedDualClassificationRecurrence
open scoped BigOperators
noncomputable section

theorem finiteKernel_antiperiodic (n : ℕ) (t : ℝ) :
    finiteKernel n (t + Real.pi) = -finiteKernel n t := by
  have hp (p : Fin n) : SchurWeights.weight n p * Real.cos (p * (t + Real.pi)) =
      -(SchurWeights.weight n p * Real.cos (p * t)) := by
    by_cases ha : SchurWeights.Active n p
    · rw [mul_add, Real.cos_add_nat_mul_pi, ha.1.neg_one_pow]
      ring
    · rw [SchurWeights.weight_eq_zero ha]
      ring
  unfold finiteKernel
  simp_rw [hp]
  rw [Finset.sum_neg_distrib]
  ring

theorem finiteKernel_pi_sub (n : ℕ) (t : ℝ) :
    finiteKernel n (Real.pi - t) = -finiteKernel n t := by
  have h := finiteKernel_antiperiodic n (-t)
  rw [finiteKernel_even] at h
  simpa only [sub_eq_add_neg, add_comm] using h

theorem finiteKernel_quarter_zero (n : ℕ) : finiteKernel n (Real.pi / 2) = 0 := by
  have h := finiteKernel_pi_sub n (Real.pi / 2)
  rw [show Real.pi - Real.pi / 2 = Real.pi / 2 by ring] at h
  linarith

def wronskian (n : ℕ) (r : ℝ) : ℝ :=
  Real.cos (r * (2 * Real.pi / n)) * finiteKernel n ((r + 1) * (2 * Real.pi / n)) -
    Real.cos ((r + 1) * (2 * Real.pi / n)) * finiteKernel n (r * (2 * Real.pi / n))

theorem cosine_recurrence (r b : ℝ) :
    Real.cos ((r + 2) * b) + Real.cos (r * b) =
      2 * Real.cos b * Real.cos ((r + 1) * b) := by
  have h := Real.cos_add ((r + 1) * b) b
  have h' := Real.cos_sub ((r + 1) * b) b
  rw [show (r + 1) * b + b = (r + 2) * b by ring] at h
  rw [show (r + 1) * b - b = r * b by ring] at h'
  nlinarith

theorem wronskian_difference (n : ℕ) (r : ℝ) :
    wronskian n (r + 1) - wronskian n r =
      Real.cos ((r + 1) * (2 * Real.pi / n)) *
        (finiteKernel n ((r + 2) * (2 * Real.pi / n)) -
          2 * Real.cos (2 * Real.pi / n) * finiteKernel n ((r + 1) * (2 * Real.pi / n)) +
            finiteKernel n (r * (2 * Real.pi / n))) := by
  have h := cosine_recurrence r (2 * Real.pi / n)
  unfold wronskian
  rw [show r + 1 + 1 = r + 2 by ring]
  linear_combination -finiteKernel n ((r + 1) * (2 * Real.pi / n)) * h

theorem wronskian_increment {m r : ℕ} (hm : 0 < m) (hr : r + 1 < m) :
    wronskian (2 * m) (r + 1) - wronskian (2 * m) r =
      2 * Real.sin (Real.pi / (2 * m : ℕ)) ^ 2 *
        Real.cot ((r + 1) * (2 * Real.pi / (2 * m : ℕ))) ^ 2 := by
  have h := finiteKernel_grid_recurrence (r := r + 1) hm (by omega) hr
  dsimp only at h
  push_cast at h ⊢
  rw [wronskian_difference]
  push_cast
  rw [show (r : ℝ) + 1 + 1 = r + 2 by ring,
    show (r : ℝ) + 1 - 1 = r by ring] at h
  rw [h]
  rw [Real.cot_eq_cos_div_sin]
  ring

theorem wronskian_middle_zero {m R : ℕ} (hm : 0 < m)
    (hR : m = 2 * R + 1 ∨ m = 2 * R + 2) : wronskian (2 * m) R = 0 := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold wronskian
  rcases hR with hR | hR
  · have he : ((R : ℝ) + 1) * (2 * Real.pi / (2 * m : ℕ)) =
        Real.pi - (R : ℝ) * (2 * Real.pi / (2 * m : ℕ)) := by
      have hcast : (m : ℝ) = 2 * R + 1 := by exact_mod_cast hR
      push_cast
      field_simp
      nlinarith
    rw [he, Real.cos_pi_sub, finiteKernel_pi_sub]
    ring
  · have he : ((R : ℝ) + 1) * (2 * Real.pi / (2 * m : ℕ)) = Real.pi / 2 := by
      have hcast : (m : ℝ) = 2 * R + 2 := by exact_mod_cast hR
      push_cast
      field_simp
      nlinarith
    rw [he, Real.cos_pi_div_two, finiteKernel_quarter_zero]
    ring

theorem wronskian_telescope {m R r : ℕ} (hm : 0 < m)
    (hR : m = 2 * R + 1 ∨ m = 2 * R + 2) (hr : r ≤ R) :
    wronskian (2 * m) r = -2 * Real.sin (Real.pi / (2 * m : ℕ)) ^ 2 *
      ∑ s ∈ Finset.Ico r R, Real.cot (((s : ℝ) + 1) * (2 * Real.pi / (2 * m : ℕ))) ^ 2 := by
  have hRm : R < m := by omega
  have hs := Finset.sum_congr (s₁ := Finset.Ico r R) rfl (fun s hs =>
    wronskian_increment hm (show s + 1 < m from by have := (Finset.mem_Ico.mp hs).2; omega))
  have ht := Finset.sum_Ico_sub (fun s : ℕ => wronskian (2 * m) s) hr
  simp only [Nat.cast_add, Nat.cast_one] at ht
  rw [ht, ← Finset.mul_sum, wronskian_middle_zero hm hR] at hs
  linarith

theorem wronskian_nonpos {m R r : ℕ} (hm : 0 < m)
    (hR : m = 2 * R + 1 ∨ m = 2 * R + 2) (hr : r ≤ R) :
    wronskian (2 * m) r ≤ 0 := by
  rw [wronskian_telescope hm hR hr]
  exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (Real.sin (Real.pi / (2 * m : ℕ)))])
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem wronskian_floor_formula {m r : ℕ} (hm : 0 < m) (hr : r ≤ (m - 1) / 2) :
    wronskian (2 * m) r = -2 * Real.sin (Real.pi / (2 * m : ℕ)) ^ 2 *
      ∑ s ∈ Finset.Ico r ((m - 1) / 2),
        Real.cot (((s : ℝ) + 1) * (2 * Real.pi / (2 * m : ℕ))) ^ 2 := by
  exact wronskian_telescope hm (by omega) hr

theorem grid_cosine_pos {m r : ℕ} (hm : 0 < m) (hr : 2 * r < m) :
    0 < Real.cos ((r : ℝ) * (2 * Real.pi / (2 * m : ℕ))) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hrR : 2 * (r : ℝ) < m := by exact_mod_cast hr
  rw [show (r : ℝ) * (2 * Real.pi / (2 * m : ℕ)) = (r : ℝ) * Real.pi / m by push_cast; ring]
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have hn : 0 ≤ (r : ℝ) * Real.pi / m := by positivity
    linarith [pi_pos]
  · apply (div_lt_iff₀ hmR).mpr
    have h := mul_lt_mul_of_pos_right hrR pi_pos
    nlinarith

theorem ratio_step {m R r : ℕ} (hm : 0 < m)
    (hR : m = 2 * R + 1 ∨ m = 2 * R + 2) (hr : r + 1 ≤ R) :
    finiteKernel (2 * m) (((r : ℝ) + 1) * (2 * Real.pi / (2 * m : ℕ))) /
        Real.cos (((r : ℝ) + 1) * (2 * Real.pi / (2 * m : ℕ))) ≤
      finiteKernel (2 * m) ((r : ℝ) * (2 * Real.pi / (2 * m : ℕ))) /
        Real.cos ((r : ℝ) * (2 * Real.pi / (2 * m : ℕ))) := by
  have hc := grid_cosine_pos hm (show 2 * r < m from by omega)
  have hc' := grid_cosine_pos hm (show 2 * (r + 1) < m from by omega)
  simp only [Nat.cast_add, Nat.cast_one] at hc'
  apply (div_le_div_iff₀ hc' hc).mpr
  have hw := wronskian_nonpos hm hR (show r ≤ R from by omega)
  unfold wronskian at hw
  nlinarith

theorem ratio_antitone {m R r s : ℕ} (hm : 0 < m)
    (hR : m = 2 * R + 1 ∨ m = 2 * R + 2) (hrs : r ≤ s) (hs : s ≤ R) :
    finiteKernel (2 * m) ((s : ℝ) * (2 * Real.pi / (2 * m : ℕ))) /
        Real.cos ((s : ℝ) * (2 * Real.pi / (2 * m : ℕ))) ≤
      finiteKernel (2 * m) ((r : ℝ) * (2 * Real.pi / (2 * m : ℕ))) /
        Real.cos ((r : ℝ) * (2 * Real.pi / (2 * m : ℕ))) := by
  revert hs
  induction s, hrs using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ s hrs ih =>
    intro hs
    have h := ratio_step hm hR hs
    simpa only [Nat.cast_add, Nat.cast_one] using h.trans (ih (by omega))

end
end StructuralNote.FixedDualClassificationRecurrenceWronskian
