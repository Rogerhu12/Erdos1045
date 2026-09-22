import EventualExact.AntipodalEnergy
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-! Quantitative control of the actual antipodal angle coordinates. -/

namespace Erdos1045.EventualExact.PolarAngleControl

open Complex AntipodalDecomposition FourierMultiplier
open scoped BigOperators
noncomputable section

theorem near_one_lower {z : ℂ} (hz : ‖z - 1‖ ≤ 1 / 2) : 1 / 2 ≤ z.re ∧ 1 / 2 ≤ ‖z‖ := by
  have hr := (Complex.abs_re_le_norm (z - 1)).trans hz
  simp only [sub_re, one_re] at hr
  have h : 1 / 2 ≤ z.re := by linarith [(abs_le.mp hr).1]
  exact ⟨h, h.trans (Complex.re_le_norm z)⟩

theorem log_lipschitz_near_one {z w : ℂ} (hz : ‖z - 1‖ ≤ 1 / 2) (hw : ‖w - 1‖ ≤ 1 / 2) :
    ‖Complex.log z - Complex.log w‖ ≤ 2 * ‖z - w‖ := by
  let S : Set ℂ := Metric.closedBall 1 (1 / 2)
  have hs (x : ℂ) (hx : x ∈ S) : ‖x - 1‖ ≤ 1 / 2 := by
    simpa only [S, Metric.mem_closedBall, dist_eq_norm] using hx
  apply (convex_closedBall (1 : ℂ) (1 / 2 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f' := fun x => x⁻¹)
  · intro x hx
    apply (Complex.hasDerivAt_log (Or.inl ?_)).hasDerivWithinAt
    exact lt_of_lt_of_le (by norm_num) (near_one_lower (hs x hx)).1
  · intro x hx
    rw [norm_inv]
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) (near_one_lower (hs x hx)).2
    simpa using h
  · simpa only [Metric.mem_closedBall, dist_eq_norm] using hw
  · simpa only [Metric.mem_closedBall, dist_eq_norm] using hz

theorem arg_lipschitz_near_one {z w : ℂ} (hz : ‖z - 1‖ ≤ 1 / 2) (hw : ‖w - 1‖ ≤ 1 / 2) :
    |z.arg - w.arg| ≤ 2 * ‖z - w‖ := by
  have h := (Complex.abs_im_le_norm (Complex.log z - Complex.log w)).trans
    (log_lipschitz_near_one hz hw)
  simpa only [sub_im, Complex.log_im] using h

theorem arg_one_add_bound {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : |(1 + z).arg| ≤ 2 * ‖z‖ := by
  simpa only [add_sub_cancel_left, Complex.arg_one, sub_zero] using
    arg_lipschitz_near_one (z := 1 + z) (w := 1) (by simpa using hz) (by simp)

theorem divided_difference_unit_bound {a b v w : ℂ} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ‖a / v - b / w‖ ≤ ‖a - b‖ + ‖b‖ * ‖v - w‖ := by
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw
  have he : a / v - b / w = (a - b) / v + (b / w) * (w - v) / v := by
    field_simp
    ring
  rw [he]
  have h := norm_add_le ((a - b) / v) ((b / w) * (w - v) / v)
  simpa only [norm_div, norm_mul, hv, hw, div_one, norm_sub_rev w v] using h

def rotatedOdd (m : ℕ) (u : ℕ → ℂ) (j : ℕ) : ℂ :=
  oddSequence m u j / LocalPhase.regularRoot (2 * m) ^ j

def angle (m : ℕ) (u : ℕ → ℂ) (j : ℕ) : ℝ := (1 + rotatedOdd m u j).arg

theorem rotatedOdd_norm (m : ℕ) (u : ℕ → ℂ) (j : ℕ) :
    ‖rotatedOdd m u j‖ = ‖oddSequence m u j‖ := by
  simp only [rotatedOdd, norm_div, norm_pow, LocalChord.root_norm, one_pow, div_one]

theorem rotatedOdd_periodic {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) : Function.Periodic (rotatedOdd m u) m := by
  intro j
  simp only [rotatedOdd, oddSequence_antiperiodic m u hu, pow_add, root_halfTurn hm,
    mul_neg_one, neg_div, div_neg, neg_neg]

theorem angle_periodic {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) : Function.Periodic (angle m u) m := by
  intro j
  simp only [angle, rotatedOdd_periodic hm u hu j]

theorem angle_bound {m : ℕ} (u : ℕ → ℂ) (j : ℕ) (hsmall : ‖oddSequence m u j‖ ≤ 1 / 2) :
    |angle m u j| ≤ 2 * ‖oddSequence m u j‖ := by
  have h := arg_one_add_bound (by simpa only [rotatedOdd_norm] using hsmall :
    ‖rotatedOdd m u j‖ ≤ 1 / 2)
  simpa only [angle, rotatedOdd_norm] using h

theorem angle_difference_bound {m : ℕ} (u : ℕ → ℂ) (j k : ℕ)
    (hj : ‖oddSequence m u j‖ ≤ 1 / 2) (hk : ‖oddSequence m u k‖ ≤ 1 / 2) :
    |angle m u k - angle m u j| ≤ 2 * (‖oddSequence m u k - oddSequence m u j‖ +
      ‖oddSequence m u j‖ * ‖LocalPhase.regularRoot (2 * m) ^ k - LocalPhase.regularRoot (2 * m) ^ j‖) := by
  have hl := arg_lipschitz_near_one (z := 1 + rotatedOdd m u k) (w := 1 + rotatedOdd m u j)
    (by simpa only [add_sub_cancel_left, rotatedOdd_norm] using hk)
    (by simpa only [add_sub_cancel_left, rotatedOdd_norm] using hj)
  have hd := divided_difference_unit_bound
    (a := oddSequence m u k) (b := oddSequence m u j)
    (v := LocalPhase.regularRoot (2 * m) ^ k) (w := LocalPhase.regularRoot (2 * m) ^ j)
    (by simp [LocalChord.root_norm]) (by simp [LocalChord.root_norm])
  simp only [add_sub_add_left_eq_sub] at hl
  exact hl.trans (mul_le_mul_of_nonneg_left hd (by norm_num))

theorem angle_pairRatio_bound {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ)
    (hsmall : ∀ j, ‖oddSequence m u j‖ ≤ 1 / 2) {h : ℕ} (hh : 0 < h) (hhn : h < 2 * m) (j : ℕ) :
    ‖LocalDFT.pairRatio (2 * m) (fun k => (angle m u k : ℂ)) j h‖ ≤
      2 * (‖LocalDFT.pairRatio (2 * m) (oddSequence m u) j h‖ + ‖oddSequence m u j‖) := by
  have ha := angle_difference_bound u j (j + h) (hsmall j) (hsmall (j + h))
  have hd : 0 < ‖LocalPhase.regularRoot (2 * m) ^ (j + h) - LocalPhase.regularRoot (2 * m) ^ j‖ :=
    norm_pos_iff.mpr (LocalDFT.vertex_difference_ne_zero (by omega) hh hhn j)
  simp only [LocalDFT.pairRatio, norm_div, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  apply (div_le_iff₀ hd).2
  have he : (‖oddSequence m u (j + h) - oddSequence m u j‖ /
      ‖LocalPhase.regularRoot (2 * m) ^ (j + h) - LocalPhase.regularRoot (2 * m) ^ j‖) *
      ‖LocalPhase.regularRoot (2 * m) ^ (j + h) - LocalPhase.regularRoot (2 * m) ^ j‖ =
      ‖oddSequence m u (j + h) - oddSequence m u j‖ := div_mul_cancel₀ _ hd.ne'
  nlinarith

theorem angle_pairRatio_square {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ)
    (hsmall : ∀ j, ‖oddSequence m u j‖ ≤ 1 / 2) {h : ℕ} (hh : 0 < h) (hhn : h < 2 * m) (j : ℕ) :
    normSq (LocalDFT.pairRatio (2 * m) (fun k => (angle m u k : ℂ)) j h) ≤
      8 * normSq (LocalDFT.pairRatio (2 * m) (oddSequence m u) j h) + 8 * normSq (oddSequence m u j) := by
  have hb := angle_pairRatio_bound hm u hsmall hh hhn j
  simp only [normSq_eq_norm_sq]
  nlinarith [sq_nonneg (‖LocalDFT.pairRatio (2 * m) (oddSequence m u) j h‖ - ‖oddSequence m u j‖),
    norm_nonneg (LocalDFT.pairRatio (2 * m) (fun k => (angle m u k : ℂ)) j h),
    norm_nonneg (LocalDFT.pairRatio (2 * m) (oddSequence m u) j h), norm_nonneg (oddSequence m u j)]

theorem angle_energy_bound {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ)
    (hsmall : ∀ j, ‖oddSequence m u j‖ ≤ 1 / 2) :
    LocalDFT.energyA (2 * m) (fun k => (angle m u k : ℂ)) ≤
      8 * LocalDFT.energyA (2 * m) (oddSequence m u) +
        4 * ((2 * m : ℝ) - 1) * (∑ j ∈ Finset.range (2 * m), normSq (oddSequence m u j)) := by
  have hs := Finset.sum_le_sum (s := (Finset.range (2 * m)).erase 0) (fun h hh =>
    Finset.sum_le_sum (s := Finset.range (2 * m)) (fun j _ =>
      angle_pairRatio_square hm u hsmall (Nat.pos_of_ne_zero (Finset.ne_of_mem_erase hh))
        (Finset.mem_range.mp (Finset.mem_of_mem_erase hh)) j))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hs
  have hcard : (((Finset.range (2 * m)).erase 0).card : ℝ) = (2 * m : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)), Finset.card_range,
      Nat.cast_sub (by omega : 1 ≤ 2 * m)]
    push_cast
    ring
  rw [hcard] at hs
  unfold LocalDFT.energyA
  linarith

end
end Erdos1045.EventualExact.PolarAngleControl
