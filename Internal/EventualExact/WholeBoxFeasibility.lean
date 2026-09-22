import EventualExact.BoxLensLift
import EventualExact.NonlocalFeasibility

/-! Every actual nonlinear box lift is a diameter-two configuration. -/

namespace Erdos1045.EventualExact.WholeBoxFeasibility

open Complex FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open BoxLensLift NonlocalFeasibility
noncomputable section

theorem root_sum_formula (n : ℕ) :
    LocalPhase.regularRoot n + 1 =
      (2 * Real.cos (Real.pi / n) : ℝ) * LocalPhase.phase n 1 := by
  unfold LocalPhase.regularRoot LocalPhase.phase
  simp only [Nat.cast_one, one_mul]
  rw [show (2 * Real.pi / n : ℝ) = 2 * (Real.pi / n) by ring]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      zero_mul, sub_zero, add_zero, Real.cos_two_mul, Real.sin_two_mul] <;> ring

theorem reference_sum {n : ℕ} (hn : 0 < n) (j : Fin n) :
    character n 1 (successor hn j) + character n 1 j =
      (baseWidth n : ℂ) * frame n j := by
  change character n 1 ((j.val + 1) % n) + character n 1 j = _
  rw [character_mod hn, character_add]
  have he : character n 1 1 = LocalPhase.regularRoot n := by simp [character]
  rw [he, ← mul_add_one, root_sum_formula]
  unfold baseWidth angle frame
  push_cast
  ring

theorem liftedCenter_all_cross_constraints {m : ℕ} (hm : 16 ≤ m)
    (q : Fin (2 * m) → ℝ) (hq : q ∈ FiniteBox.Q (by omega)) (j : Fin (2 * m)) :
    ‖(baseWidth (2 * m) : ℂ) * frame (2 * m) j +
      difference (by omega) (liftedCenter hm q hq) j‖ ≤ 2 ∧
    ‖(baseWidth (2 * m) : ℂ) * frame (2 * m) j -
      difference (by omega) (liftedCenter hm q hq) j‖ ≤ 2 := by
  have hhalf (k : Fin m) := liftedCenter_cross_constraints hm q hq k
  simp only [← frame_halfIndex] at hhalf
  by_cases hj : j.val < m
  · exact hhalf ⟨j.val, hj⟩
  · let k : Fin m := ⟨j.val - m, by omega⟩
    have he : halfTurn (by omega) (halfIndex k) = j := by
      apply Fin.ext
      simp only [halfTurn, halfIndex, k]
      rw [Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt j.isLt]
    have hd : difference (by omega) (liftedCenter hm q hq)
        (halfTurn (by omega) (halfIndex k)) =
        difference (by omega) (liftedCenter hm q hq) (halfIndex k) := by
      unfold difference
      rw [← halfTurn_successor, liftedCenter_halfTurn, liftedCenter_halfTurn]
    rw [← he, frame_halfTurn, hd, mul_neg]
    constructor
    · convert (hhalf k).2 using 1
      rw [show -((baseWidth (2 * m) : ℂ) * frame (2 * m) (halfIndex k)) +
          difference (by omega) (liftedCenter hm q hq) (halfIndex k) =
          -((baseWidth (2 * m) : ℂ) * frame (2 * m) (halfIndex k) -
          difference (by omega) (liftedCenter hm q hq) (halfIndex k)) by ring, norm_neg]
    · convert (hhalf k).1 using 1
      rw [show -((baseWidth (2 * m) : ℂ) * frame (2 * m) (halfIndex k)) -
          difference (by omega) (liftedCenter hm q hq) (halfIndex k) =
          -((baseWidth (2 * m) : ℂ) * frame (2 * m) (halfIndex k) +
          difference (by omega) (liftedCenter hm q hq) (halfIndex k)) by ring, norm_neg]

theorem vertices_character {n : ℕ} (c : Fin n → ℂ) (j : Fin n) :
    vertices c j = character n 1 j + c j := by simp [vertices, character]

theorem vertices_cross_next {m : ℕ} (hm : 16 ≤ m)
    (q : Fin (2 * m) → ℝ) (hq : q ∈ FiniteBox.Q (by omega)) (j : Fin (2 * m)) :
    ‖vertices (liftedCenter hm q hq) (cyclicAdvance j (m + 1)) -
      vertices (liftedCenter hm q hq) j‖ ≤ 2 := by
  have he : cyclicAdvance j (m + 1) = halfTurn (by omega) (successor (by omega) j) := by
    apply Fin.ext
    simp only [cyclicAdvance, halfTurn, successor, Nat.mod_add_mod]
    congr 1
    omega
  rw [he]
  have h := (liftedCenter_all_cross_constraints hm q hq j).2
  rw [← reference_sum (by omega)] at h
  simp only [vertices_character]
  rw [character_halfTurn (by omega) (by decide : Odd 1), liftedCenter_halfTurn]
  convert h using 1
  rw [show -character (2 * m) 1 (successor (by omega) j) +
      liftedCenter hm q hq (successor (by omega) j) -
      (character (2 * m) 1 j + liftedCenter hm q hq j) =
      -(character (2 * m) 1 (successor (by omega) j) + character (2 * m) 1 j -
        difference (by omega) (liftedCenter hm q hq) j) by unfold difference; ring,
    norm_neg]

theorem vertices_matching {m : ℕ} (hm : 16 ≤ m)
    (q : Fin (2 * m) → ℝ) (hq : q ∈ FiniteBox.Q (by omega)) (j : Fin (2 * m)) :
    ‖vertices (liftedCenter hm q hq) (cyclicAdvance j m) -
      vertices (liftedCenter hm q hq) j‖ = 2 := by
  have he : cyclicAdvance j m = halfTurn (by omega) j := rfl
  rw [he]
  simp only [vertices_character, character_halfTurn (m := m) (by omega) (by decide : Odd 1),
    liftedCenter_halfTurn]
  rw [show -character (2 * m) 1 j + liftedCenter hm q hq j -
      (character (2 * m) 1 j + liftedCenter hm q hq j) =
      (-2 : ℂ) * character (2 * m) 1 j by ring, norm_mul]
  simp [character, ClosedFourier.root_norm]

theorem vertices_cross_prev {m : ℕ} (hm : 16 ≤ m)
    (q : Fin (2 * m) → ℝ) (hq : q ∈ FiniteBox.Q (by omega)) (j : Fin (2 * m)) :
    ‖vertices (liftedCenter hm q hq) (cyclicAdvance j (m - 1)) -
      vertices (liftedCenter hm q hq) j‖ ≤ 2 := by
  have h := vertices_cross_next hm q hq (cyclicAdvance j (m - 1))
  rw [advance_back_forward (by omega : 1 ≤ m), norm_sub_rev] at h
  exact h

theorem liftedCenter_offset_bound {m r : ℕ} (hm : 256 ≤ 2 * m)
    (q : Fin (2 * m) → ℝ) (hq : q ∈ FiniteBox.Q (by omega))
    (hr : r < 2 * m) (j : Fin (2 * m)) :
    ‖vertices (liftedCenter (by omega) q hq) (cyclicAdvance j r) -
      vertices (liftedCenter (by omega) q hq) j‖ ≤ 2 := by
  by_cases hprev : r = m - 1
  · subst r; exact vertices_cross_prev (by omega) q hq j
  by_cases hmatch : r = m
  · subst r; exact (vertices_matching (by omega) q hq j).le
  by_cases hnext : r = m + 1
  · subst r; exact vertices_cross_next (by omega) q hq j
  apply (nonlocal_offset_strict (by omega) hr ⟨hprev, hmatch, hnext⟩
    (liftedCenter (by omega) q hq) (liftedCenter_halfTurn (by omega) q hq)
    (C := 2048) ?_ ?_ j).le
  · have hnR : (256 : ℝ) ≤ (2 * m : ℕ) := by exact_mod_cast hm
    nlinarith
  · intro i
    exact liftedCenter_increment_norm_le (by omega) q hq i

theorem cyclicAdvance_forwardDistance {n : ℕ} (i j : Fin n) :
    cyclicAdvance i (cyclicForwardDistance i j) = j := by
  apply Fin.ext
  simp only [cyclicAdvance, cyclicForwardDistance, Nat.add_mod_mod]
  rw [show i.val + (j.val + n - i.val) = j.val + n by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]

/-- The genuine whole-box feasibility endpoint, including the three cross offsets. -/
theorem liftedCenter_diameterAtMost {m : ℕ} (hm : 256 ≤ 2 * m)
    (q : Fin (2 * m) → ℝ) (hq : q ∈ FiniteBox.Q (by omega)) :
    Configuration.DiameterAtMost 2 (vertices (liftedCenter (by omega) q hq)) := by
  intro i j
  have h := liftedCenter_offset_bound hm q hq
    (Nat.mod_lt (i.val + 2 * m - j.val) (by omega)) j
  change ‖vertices (liftedCenter (by omega) q hq)
      (cyclicAdvance j (cyclicForwardDistance j i)) -
      vertices (liftedCenter (by omega) q hq) j‖ ≤ 2 at h
  rwa [cyclicAdvance_forwardDistance] at h

end
end Erdos1045.EventualExact.WholeBoxFeasibility
