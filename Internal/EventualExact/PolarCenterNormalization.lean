import EventualExact.PolarCenterEnergy

/-! Mean normalization by an actual physical translation before removing the angle. -/

noncomputable section
open scoped BigOperators

namespace Erdos1045.EventualExact.PolarCenterNormalization

open Complex FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum PolarCenterEnergy

def translation {n : ℕ} (θ : Fin n → ℝ) (C : Fin n → ℂ) : ℂ :=
  (∑ j, phase (θ j) * C j) / (∑ j, phase (θ j))

def correctedCenter {n : ℕ} (θ : Fin n → ℝ) (C : Fin n → ℂ) (j : Fin n) : ℂ :=
  phase (θ j) * (C j - translation θ C)

theorem sum_phase_error {n : ℕ} (θ : Fin n → ℝ) :
    ‖(∑ j, phase (θ j)) - (n : ℂ)‖ ≤ (n : ℝ) * ‖θ‖ := by
  have he : (∑ j, phase (θ j)) - (n : ℂ) = ∑ j, (phase (θ j) - 1) := by simp
  rw [he]
  calc
    _ ≤ ∑ j, ‖phase (θ j) - 1‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, ‖θ‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact (phase_sub_one (θ j)).trans (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm θ j)
    _ = _ := by simp

theorem sum_phase_lower {n : ℕ} (θ : Fin n → ℝ) (hθ : ‖θ‖ ≤ 1 / 2) :
    (n : ℝ) / 2 ≤ ‖∑ j, phase (θ j)‖ := by
  have h := norm_sub_norm_le (n : ℂ) (∑ j, phase (θ j))
  rw [norm_sub_rev, Complex.norm_natCast] at h
  have he := sum_phase_error θ
  have hm := mul_le_mul_of_nonneg_left hθ (Nat.cast_nonneg n)
  linarith

theorem sum_phase_ne_zero {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) (hθ : ‖θ‖ ≤ 1 / 2) :
    (∑ j, phase (θ j)) ≠ 0 := by
  apply norm_ne_zero_iff.mp
  exact ne_of_gt (lt_of_lt_of_le (by positivity) (sum_phase_lower θ hθ))

theorem weighted_center_sum_bound {n : ℕ} (θ : Fin n → ℝ) (C : Fin n → ℂ)
    (hC : ∑ j, C j = 0) :
    ‖∑ j, phase (θ j) * C j‖ ≤ (n : ℝ) * ‖θ‖ * ‖C‖ := by
  have he : (∑ j, phase (θ j) * C j) = ∑ j, (phase (θ j) - 1) * C j := by
    simp only [sub_mul, one_mul, Finset.sum_sub_distrib, hC, sub_zero]
  rw [he]
  calc
    _ ≤ ∑ j, ‖(phase (θ j) - 1) * C j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, ‖θ‖ * ‖C‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      have ht : ‖phase (θ j) - 1‖ ≤ ‖θ‖ :=
        (phase_sub_one (θ j)).trans (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm θ j)
      exact mul_le_mul ht (norm_le_pi_norm C j) (norm_nonneg _) (norm_nonneg θ)
    _ = _ := by simp; ring

theorem translation_norm_le {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) (C : Fin n → ℂ)
    (hθ : ‖θ‖ ≤ 1 / 2) (hC : ∑ j, C j = 0) :
    ‖translation θ C‖ ≤ 2 * ‖θ‖ * ‖C‖ := by
  have hd : 0 < ‖∑ j, phase (θ j)‖ := norm_pos_iff.mpr (sum_phase_ne_zero hn θ hθ)
  rw [translation, norm_div]
  apply (div_le_iff₀ hd).mpr
  have hmul := mul_le_mul_of_nonneg_left (sum_phase_lower θ hθ)
    (by positivity : 0 ≤ 2 * ‖θ‖ * ‖C‖)
  exact (weighted_center_sum_bound θ C hC).trans (by nlinarith)

theorem correctedCenter_mean_zero {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) (C : Fin n → ℂ)
    (hθ : ‖θ‖ ≤ 1 / 2) : ∑ j, correctedCenter θ C j = 0 := by
  simp only [correctedCenter, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [translation]
  field_simp [sum_phase_ne_zero hn θ hθ]
  simp

theorem phase_cancel (t : ℝ) : phase (-t) * phase t = 1 := by
  simp only [phase, neg_neg, ← GapRigidity.circle_add, add_neg_cancel]
  simp [GapRigidity.circle]

theorem physical_center_translation {n : ℕ} (θ : Fin n → ℝ) (C : Fin n → ℂ) (j : Fin n) :
    phase (-θ j) * correctedCenter θ C j = C j - translation θ C := by
  rw [correctedCenter, ← mul_assoc, phase_cancel, one_mul]

/-- Reconstructing the physical vertices changes every vertex by precisely the same translation. -/
theorem physical_vertices_translation {n : ℕ} (θ : Fin n → ℝ) (C v : Fin n → ℂ) (j : Fin n) :
    phase (-θ j) * (v j + correctedCenter θ C j) =
      phase (-θ j) * (v j + phase (θ j) * C j) - translation θ C := by
  rw [mul_add, physical_center_translation, mul_add, ← mul_assoc, phase_cancel]
  ring

theorem shifted_norm_le {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) (C : Fin n → ℂ)
    (hθ : ‖θ‖ ≤ 1 / 2) (hC : ∑ j, C j = 0) :
    ‖(fun j => C j - translation θ C)‖ ≤ 2 * ‖C‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  have ht := translation_norm_le hn θ C hθ hC
  have hc := norm_le_pi_norm C j
  have hh := mul_le_mul_of_nonneg_right hθ (norm_nonneg C)
  exact (norm_sub_le _ _).trans (by nlinarith)

theorem correctedCenter_norm_le {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) (C : Fin n → ℂ)
    (hθ : ‖θ‖ ≤ 1 / 2) (hC : ∑ j, C j = 0) :
    ‖correctedCenter θ C‖ ≤ 2 * ‖C‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  simp only [correctedCenter, norm_mul, phase_norm, one_mul]
  exact (norm_le_pi_norm (fun j => C j - translation θ C) j).trans (shifted_norm_le hn θ C hθ hC)

theorem correctedCenter_halfPeriodic {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (C : Fin (2 * m) → ℂ) (hθ : ∀ j, θ (halfTurn hm j) = θ j) (hC : HalfPeriodic hm C) :
    HalfPeriodic hm (correctedCenter θ C) := by
  intro j
  simp only [correctedCenter, hθ j, hC j]

theorem pairEnergy_sub_const {n : ℕ} (hn : 0 < n) (C : Fin n → ℂ) (t : ℂ) :
    pairEnergy hn (fun j => C j - t) = pairEnergy hn C := by
  have he (j h : ℕ) : LocalDFT.pairRatio n (periodize hn (fun j => C j - t)) j h =
      LocalDFT.pairRatio n (periodize hn C) j h := by
    unfold LocalDFT.pairRatio periodize
    congr 1
    ring
  simp only [pairEnergy, LocalDFT.energyA, he]

theorem constraint_sub_const {n : ℕ} (hn : 0 < n) (C : Fin n → ℂ) (t : ℂ) :
    constraint hn (fun j => C j - t) = constraint hn C := by
  funext j
  have he : difference hn (fun j => C j - t) j = difference hn C j := by unfold difference; ring
  simp only [constraint, he]

theorem correctedCenter_energy_le {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) (C : Fin n → ℂ)
    (hθ : ‖θ‖ ≤ 1 / 2) (hC : ∑ j, C j = 0) :
    pairEnergy hn (correctedCenter θ C) ≤
      2 * pairEnergy hn C + 8 * ‖C‖ ^ 2 * DiscreteEnergy.realEnergy hn θ := by
  have h := energy_bound hn 1 θ (fun j => C j - translation θ C)
  have he : center 1 θ (fun j => C j - translation θ C) = correctedCenter θ C := by
    funext j
    simp only [center, one_mul, correctedCenter]
  rw [he, norm_one, one_pow, mul_one, pairEnergy_sub_const] at h
  have hs := pow_le_pow_left₀ (norm_nonneg _) (shifted_norm_le hn θ C hθ hC) 2
  have hm := mul_le_mul_of_nonneg_right hs (pairEnergy_nonneg hn (fun j => (θ j : ℂ)))
  dsimp [DiscreteEnergy.realEnergy] at *
  nlinarith

theorem correctedCenter_constraint_difference_le {n : ℕ} (hn : 2 ≤ n)
    (θ : Fin n → ℝ) (C : Fin n → ℂ) (hθ : ‖θ‖ ≤ 1 / 2) (hC : ∑ j, C j = 0) :
    SchurLiftBounds.meanSquare
      (constraint (by omega) (correctedCenter θ C) - constraint (by omega) C) ≤
      Real.pi ^ 2 * n * (‖θ‖ ^ 2 * pairEnergy (by omega) C +
        4 * ‖C‖ ^ 2 * DiscreteEnergy.realEnergy (by omega) θ) := by
  have h := constraint_difference_le_energy hn 1 θ (fun j => C j - translation θ C)
  have he : center 1 θ (fun j => C j - translation θ C) = correctedCenter θ C := by
    funext j
    simp only [center, one_mul, correctedCenter]
  rw [he, constraint_sub_const, pairEnergy_sub_const] at h
  simp only [sub_self, norm_zero, norm_one, one_mul, zero_add, one_pow] at h
  have hs := pow_le_pow_left₀ (norm_nonneg _)
    (shifted_norm_le (show 0 < n by omega) θ C hθ hC) 2
  have hm := mul_le_mul_of_nonneg_right hs
    (pairEnergy_nonneg (show 0 < n by omega) (fun j => (θ j : ℂ)))
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  dsimp [DiscreteEnergy.realEnergy] at *
  nlinarith

end Erdos1045.EventualExact.PolarCenterNormalization
