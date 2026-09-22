import EventualExact.SchurWeights
import EventualExact.FiniteMultiplier
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.BigOperators.Intervals

/-! Uniform bounds and a strict square-mass bound for the actual Schur weights. -/

namespace Erdos1045.EventualExact.SchurWeights

open scoped BigOperators
noncomputable section

theorem sin_parabolic_lower {x : ℝ} (hx : 0 ≤ x) (hxp : x ≤ Real.pi) :
    x * (Real.pi - x) / Real.pi ≤ Real.sin x := by
  have hhalf {y : ℝ} (hy : 0 ≤ y) (hyp : y ≤ Real.pi / 2) :
      y * (Real.pi - y) / Real.pi ≤ Real.sin y := by
    have hp2 : Real.pi ^ 2 ≤ 12 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have hyp' : y * Real.pi ≤ 6 := by nlinarith [Real.pi_pos]
    have hcube : y ^ 3 / 6 ≤ y ^ 2 / Real.pi := by
      apply (le_div_iff₀ Real.pi_pos).2
      nlinarith [mul_nonneg (sq_nonneg y) (show 0 ≤ 6 - y * Real.pi by linarith)]
    have hs := Real.sin_ge_sub_cube hy
    rw [show y * (Real.pi - y) / Real.pi = y - y ^ 2 / Real.pi by
      field_simp]
    linarith
  by_cases h : x ≤ Real.pi / 2
  · exact hhalf hx h
  · have hs := hhalf (show 0 ≤ Real.pi - x by linarith)
      (show Real.pi - x ≤ Real.pi / 2 by linarith)
    rw [Real.sin_pi_sub] at hs
    convert hs using 1; ring

theorem sin_grid_lower {n : ℕ} (hn : 0 < n) {a : ℝ}
    (ha : 0 ≤ a) (han : a ≤ n) :
    a * ((n : ℝ) - a) * Real.pi / (n : ℝ) ^ 2 ≤ Real.sin (a * Real.pi / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs := sin_parabolic_lower (show 0 ≤ a * Real.pi / n by positivity)
    ((div_le_iff₀ hnR).2 (by nlinarith [Real.pi_pos]))
  convert hs using 1
  field_simp

theorem weight_le_rational {n p : ℕ} (hp : Active n p) :
    weight n p ≤ (n : ℝ) / (((p : ℝ) + 1) * ((n : ℝ) - p + 1)) := by
  rcases active_bounds hp with ⟨hn, hp1, hpn, hnp⟩
  have hleft : 0 < (n : ℝ) - (p - 1) := by linarith
  have hright : 0 < (n : ℝ) - (p + 1) := by linarith
  have hplus : 0 < (n : ℝ) - p + 1 := by linarith
  have hnN : 0 < n := by exact_mod_cast hn
  have hden1 := sin_grid_lower hnN hp1.le (by linarith : (p : ℝ) - 1 ≤ n)
  have hden2 := sin_grid_lower hnN (by linarith : (0 : ℝ) ≤ p + 1) hpn.le
  have hprod := mul_le_mul hden1 hden2
    (by positivity : 0 ≤ ((p : ℝ) + 1) * ((n : ℝ) - (p + 1)) * Real.pi / (n : ℝ) ^ 2)
    (le_trans (by positivity) hden1)
  have hs1 : 0 < Real.sin (((p : ℝ) - 1) * Real.pi / n) :=
    lt_of_lt_of_le (by positivity) hden1
  have hs2 : 0 < Real.sin (((p : ℝ) + 1) * Real.pi / n) :=
    lt_of_lt_of_le (by positivity) hden2
  have hsq := Real.sin_sq_le_sq (x := Real.pi / n)
  rw [weight, if_pos hp]
  apply (div_le_iff₀ (mul_pos hs1 hs2)).2
  calc
    _ ≤ (((p : ℝ) - 1) * ((n : ℝ) - p - 1) / n) * (Real.pi / n) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = (n : ℝ) / (((p : ℝ) + 1) * ((n : ℝ) - p + 1)) *
        ((((p : ℝ) - 1) * ((n : ℝ) - (p - 1)) * Real.pi / (n : ℝ) ^ 2) *
        (((p : ℝ) + 1) * ((n : ℝ) - (p + 1)) * Real.pi / (n : ℝ) ^ 2)) := by
      field_simp [hn.ne', hplus.ne']
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (by positivity)

def endpointReciprocal (n p : ℕ) : ℝ := if Active n p then 1 / ((p : ℝ) + 1) else 0

theorem endpointReciprocal_nonneg (n p : ℕ) : 0 ≤ endpointReciprocal n p := by
  unfold endpointReciprocal
  split_ifs <;> positivity

theorem weight_le_endpoints {n p : ℕ} (hp : p ≤ n) (hn : Even n) :
    weight n p ≤ endpointReciprocal n p + endpointReciprocal n (n - p) := by
  by_cases ha : Active n p
  · have hb := (active_reflect hn hp).2 ha
    rcases active_bounds ha with ⟨hnpos, hp1, hpn, hnp⟩
    have hplus : 0 < (n : ℝ) - p + 1 := by linarith
    rw [endpointReciprocal, if_pos ha, endpointReciprocal, if_pos hb, Nat.cast_sub hp]
    refine (weight_le_rational ha).trans ?_
    calc
      _ ≤ ((n : ℝ) + 2) / (((p : ℝ) + 1) * ((n : ℝ) - p + 1)) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by field_simp [hplus.ne']; ring
  · rw [weight_eq_zero ha]
    exact add_nonneg (endpointReciprocal_nonneg _ _) (endpointReciprocal_nonneg _ _)

theorem endpointReciprocal_le (n p : ℕ) : endpointReciprocal n p ≤ 1 / ((p : ℝ) + 1) := by
  unfold endpointReciprocal
  split_ifs
  · exact le_rfl
  · positivity

theorem weight_le_two_div_min {n p : ℕ} (hp : p ≤ n) (hn : Even n) :
    weight n p ≤ 2 / ((min p (n - p) : ℕ) + 1 : ℝ) := by
  have hmin1 : ((min p (n - p) : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.min_le_left p (n - p)
  have hmin2 : ((min p (n - p) : ℕ) : ℝ) ≤ (n - p : ℕ) := by
    exact_mod_cast Nat.min_le_right p (n - p)
  have hmpos : 0 < ((min p (n - p) : ℕ) : ℝ) + 1 := by positivity
  have h1 := (endpointReciprocal_le n p).trans
    (one_div_le_one_div_of_le hmpos (by linarith))
  have h2 := (endpointReciprocal_le n (n - p)).trans
    (one_div_le_one_div_of_le hmpos (by linarith))
  have h := (weight_le_endpoints hp hn).trans (add_le_add h1 h2)
  calc
    _ ≤ 1 / (((min p (n - p) : ℕ) : ℝ) + 1) +
        1 / (((min p (n - p) : ℕ) : ℝ) + 1) := h
    _ = _ := by push_cast; ring

def oddSquareTail (p : ℕ) : ℝ :=
  if Odd p ∧ 3 ≤ p then 1 / ((p : ℝ) + 1) ^ 2 else 0

theorem oddSquareTail_sum {m : ℕ} (hm : 2 ≤ m) :
    (∑ p ∈ Finset.range (2 * m), oddSquareTail p) ≤ 3 / 16 - 1 / (4 * (m : ℝ)) := by
  induction m, hm using Nat.le_induction with
  | base => norm_num [oddSquareTail, Finset.sum_range_succ]
  | succ m hm ih =>
    have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have heven : ¬Odd (2 * m) := by rintro ⟨k, hk⟩; omega
    have hodd : Odd (2 * m + 1) := ⟨m, rfl⟩
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [oddSquareTail, heven, false_and, if_false, add_zero,
      hodd, show 3 ≤ 2 * m + 1 by omega, and_self, if_true] at ih ⊢
    have he : 1 / (((2 * m + 1 : ℕ) : ℝ) + 1) ^ 2 ≤
        1 / (4 * (m : ℝ)) - 1 / (4 * ((m + 1 : ℕ) : ℝ)) := by
      push_cast
      field_simp
      nlinarith
    linarith

theorem endpointReciprocal_sq_le_tail (n p : ℕ) :
    endpointReciprocal n p ^ 2 ≤ oddSquareTail p := by
  by_cases h : Active n p
  · simp [endpointReciprocal, h, oddSquareTail, h.1, h.2.1]
  · rw [endpointReciprocal, if_neg h]
    norm_num only [zero_pow]
    unfold oddSquareTail
    split_ifs <;> positivity

theorem endpointReciprocal_square_sum {m : ℕ} (hm : 2 ≤ m) :
    (∑ p : Fin (2 * m), endpointReciprocal (2 * m) p ^ 2) ≤ 3 / 16 := by
  rw [Fin.sum_univ_eq_sum_range (fun p => endpointReciprocal (2 * m) p ^ 2)]
  refine (Finset.sum_le_sum (fun p _ => endpointReciprocal_sq_le_tail _ p)).trans ?_
  exact (oddSquareTail_sum hm).trans (sub_le_self _ (by positivity))

theorem endpointReciprocal_le_quarter (n p : ℕ) : endpointReciprocal n p ≤ 1 / 4 := by
  by_cases h : Active n p
  · rw [endpointReciprocal, if_pos h]
    apply one_div_le_one_div_of_le (by norm_num)
    have hp : (3 : ℝ) ≤ p := by exact_mod_cast h.2.1
    linarith
  · simp [endpointReciprocal, h]

theorem endpointReciprocal_sum (n : ℕ) :
    (∑ p : Fin n, endpointReciprocal n p) ≤ 16 + (n : ℝ) / 64 := by
  rw [Fin.sum_univ_eq_sum_range (endpointReciprocal n)]
  calc
    _ ≤ ∑ p ∈ Finset.range (64 + n), endpointReciprocal n p :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun p _ _ => endpointReciprocal_nonneg n p)
    _ = (∑ p ∈ Finset.range 64, endpointReciprocal n p) +
        ∑ p ∈ Finset.range n, endpointReciprocal n (64 + p) :=
      Finset.sum_range_add _ _ _
    _ ≤ (∑ _p ∈ Finset.range 64, (1 / 4 : ℝ)) +
        ∑ _p ∈ Finset.range n, (1 / 64 : ℝ) := by
      apply add_le_add
      · exact Finset.sum_le_sum fun p _ => endpointReciprocal_le_quarter n p
      · apply Finset.sum_le_sum
        intro p _
        refine (endpointReciprocal_le n (64 + p)).trans ?_
        apply one_div_le_one_div_of_le (by norm_num)
        push_cast
        linarith [Nat.cast_nonneg (α := ℝ) p]
    _ = _ := by simp; ring

theorem active_neg {n : ℕ} [NeZero n] (hn : Even n) (p : Fin n) :
    Active n (-p).val ↔ Active n p.val := by
  rw [← weight_ne_zero_iff, FourierMultiplier.weight_neg hn, weight_ne_zero_iff]

theorem weight_le_endpoints_fin {n : ℕ} [NeZero n] (hn : Even n) (p : Fin n) :
    weight n p ≤ endpointReciprocal n p + endpointReciprocal n (-p).val := by
  by_cases hp : p = 0
  · subst p
    simp [weight_zero, endpointReciprocal, Active]
  · rw [Fin.val_neg, if_neg hp]
    exact weight_le_endpoints p.isLt.le hn

theorem endpoint_cross_identity {n : ℕ} [NeZero n] (hn : Even n) (p : Fin n) :
    endpointReciprocal n p * endpointReciprocal n (-p).val =
      (endpointReciprocal n p + endpointReciprocal n (-p).val) / ((n : ℝ) + 2) := by
  by_cases ha : Active n p
  · have hpa : Active n (-p).val := (active_neg hn p).2 ha
    have hp0 : p ≠ 0 := by intro h; have := ha.2.1; simp [h] at this
    rcases active_bounds ha with ⟨_, _, _, hnp⟩
    have hp : 0 < (n : ℝ) - p + 1 := by linarith
    simp only [endpointReciprocal, if_pos ha, if_pos hpa]
    rw [Fin.val_neg, if_neg hp0, Nat.cast_sub p.isLt.le]
    field_simp [hp.ne']
    ring
  · have hpa : ¬Active n (-p).val := fun h => ha ((active_neg hn p).1 h)
    simp [endpointReciprocal, ha, hpa]

theorem weight_square_sum_le_endpoints {n : ℕ} (hn0 : 0 < n) (hn : Even n) :
    (∑ p : Fin n, weight n p ^ 2) ≤
      2 * (∑ p : Fin n, endpointReciprocal n p ^ 2) +
        4 * (∑ p : Fin n, endpointReciprocal n p) / ((n : ℝ) + 2) := by
  let : NeZero n := ⟨hn0.ne'⟩
  have he : (∑ p : Fin n, endpointReciprocal n (-p).val) =
      ∑ p : Fin n, endpointReciprocal n p :=
    Equiv.sum_comp (Equiv.neg (Fin n)) (fun p => endpointReciprocal n p)
  have he2 : (∑ p : Fin n, endpointReciprocal n (-p).val ^ 2) =
      ∑ p : Fin n, endpointReciprocal n p ^ 2 :=
    Equiv.sum_comp (Equiv.neg (Fin n)) (fun p => endpointReciprocal n p ^ 2)
  calc
    _ ≤ ∑ p : Fin n, (endpointReciprocal n p + endpointReciprocal n (-p).val) ^ 2 := by
      apply Finset.sum_le_sum
      intro p _
      exact (sq_le_sq₀ (weight_nonneg _ _) (add_nonneg (endpointReciprocal_nonneg _ _)
        (endpointReciprocal_nonneg _ _))).2 (weight_le_endpoints_fin hn p)
    _ = _ := by
      have hpoint (p : Fin n) :
          (endpointReciprocal n p + endpointReciprocal n (-p).val) ^ 2 =
          endpointReciprocal n p ^ 2 + endpointReciprocal n (-p).val ^ 2 +
            2 * ((endpointReciprocal n p + endpointReciprocal n (-p).val) / ((n : ℝ) + 2)) := by
        rw [← endpoint_cross_identity hn p]
        ring
      simp_rw [hpoint]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp only [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib, he, he2]
      ring

/-- A finite telescoping argument supplies the strict spectral gap, without a zeta limit. -/
theorem weight_square_sum_le_fifteen_thirtytwo {m : ℕ} (hm : 2048 ≤ 2 * m) :
    (∑ p : Fin (2 * m), weight (2 * m) p ^ 2) ≤ 15 / 32 := by
  have hnR : (2048 : ℝ) ≤ (2 * m : ℕ) := by exact_mod_cast hm
  have hs := weight_square_sum_le_endpoints (by omega : 0 < 2 * m) (even_two_mul m)
  have hsq := endpointReciprocal_square_sum (by omega : 2 ≤ m)
  have hsum := endpointReciprocal_sum (2 * m)
  have hcross : 4 * (16 + ((2 * m : ℕ) : ℝ) / 64) /
      (((2 * m : ℕ) : ℝ) + 2) ≤ 3 / 32 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((2 * m : ℕ) : ℝ) + 2)).2
    linarith
  have hc := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 4))
    (by positivity : (0 : ℝ) ≤ ((2 * m : ℕ) : ℝ) + 2)
  linarith

theorem weight_square_sum_lt_half {m : ℕ} (hm : 2048 ≤ 2 * m) :
    (∑ p : Fin (2 * m), weight (2 * m) p ^ 2) < 1 / 2 :=
  (weight_square_sum_le_fifteen_thirtytwo hm).trans_lt (by norm_num)

/-- The exact energy multiplier has one additional uniformly controlled frequency factor. -/
theorem frequency_weight_sq_le {n p : ℕ} (hp : p ≤ n) (hn : Even n) :
    (p : ℝ) * ((n : ℝ) - p) * weight n p ^ 2 ≤ 4 * n := by
  let d : ℝ := ((min p (n - p) : ℕ) : ℝ)
  have hd : 0 ≤ d := by unfold d; positivity
  have hw := weight_le_two_div_min hp hn
  have hscaled : weight n p * (d + 1) ≤ 2 :=
    (le_div_iff₀ (by positivity : 0 < d + 1)).mp hw
  have hs := (sq_le_sq₀ (mul_nonneg (weight_nonneg _ _) (by positivity : 0 ≤ d + 1))
    (by norm_num : (0 : ℝ) ≤ 2)).2 hscaled
  have hdw : d * weight n p ^ 2 ≤ 4 := by
    have hm := mul_le_mul_of_nonneg_right (show d ≤ (d + 1) ^ 2 by nlinarith [sq_nonneg d])
      (sq_nonneg (weight n p))
    nlinarith
  have hprod : (p : ℝ) * ((n : ℝ) - p) ≤ (n : ℝ) * d := by
    by_cases he : p ≤ n - p
    · dsimp [d]
      rw [Nat.min_eq_left he]
      nlinarith [sq_nonneg (p : ℝ)]
    · dsimp [d]
      rw [Nat.min_eq_right (by omega), Nat.cast_sub hp]
      have hpR : (p : ℝ) ≤ n := by exact_mod_cast hp
      nlinarith [sq_nonneg ((n : ℝ) - p)]
  calc
    _ ≤ ((n : ℝ) * d) * weight n p ^ 2 :=
      mul_le_mul_of_nonneg_right hprod (sq_nonneg _)
    _ = (n : ℝ) * (d * weight n p ^ 2) := by ring
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hdw (Nat.cast_nonneg n)]

end
end Erdos1045.EventualExact.SchurWeights
