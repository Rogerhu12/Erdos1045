import Erdos1045.FaberCauchy

namespace Erdos1045.FaberFourier

open scoped BigOperators
noncomputable section

theorem character_series_summable {a : ℕ → ℂ} (ha : Summable (fun m => ‖a m‖))
    (t : ℝ) (l : ℕ) : Summable (fun m => a m * character (m + l) t) := by
  apply Summable.of_norm
  simpa [norm_mul, norm_character] using ha

theorem tail_tsum_eq_indicator {f : ℕ → ℂ} (hf : Summable f) (k : ℕ) :
    (∑' m, f (m + k)) = ∑' m, if k ≤ m then f m else 0 := by
  have hi : Summable (fun m => if k ≤ m then f m else 0) := by
    convert hf.indicator (Set.Ici k) using 1 <;> first | rfl | (funext m; simp [Set.indicator])
  have hs := hi.sum_add_tsum_nat_add k
  have hz : (∑ m ∈ Finset.range k, if k ≤ m then f m else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    simp [show ¬k ≤ m from Nat.not_le.mpr (Finset.mem_range.mp hm)]
  simpa [hz] using hs

theorem twisted_coefficient {n : ℕ} (c : ℝ) (a : ℕ → ℂ) (θ : Fin n → ℝ)
    (ha : Summable (fun m => ‖a m‖)) (j : Fin n) (k : ℕ) :
    character k (θ j) * coefficient c a θ j k = (c : ℂ)⁻¹ *
      (∑' m, if k ≤ m then a m * character (m + 1) (θ j) else 0) := by
  calc
    _ = (c : ℂ)⁻¹ * ∑' m,
        (character k (θ j) * character 1 (θ j)) *
          (a (m + k) * character m (θ j)) := by
      dsimp only [coefficient, series, tailCoefficients]
      rw [tsum_mul_left]
      ring
    _ = (c : ℂ)⁻¹ * ∑' m, a (m + k) * character (m + k + 1) (θ j) := by
      congr 1
      apply tsum_congr
      intro m
      rw [character_add, character_add]
      ring
    _ = _ := congrArg ((c : ℂ)⁻¹ * ·)
      (tail_tsum_eq_indicator (character_series_summable ha (θ j) 1) k)

theorem twisted_firstOrder {n : ℕ} (c : ℝ) (a : ℕ → ℂ) (θ : Fin n → ℝ)
    (ha : Summable (fun m => ‖a m‖)) (j : Fin n) (k : ℕ) :
    character k (θ j) * firstOrder (coefficient c a θ j) k = (c : ℂ)⁻¹ *
      (∑' m, if k ≤ m then (k : ℂ) * a m * character (m + 1) (θ j) else 0) := by
  have ht := twisted_coefficient c a θ ha j k
  have hsum : (∑' m, if k ≤ m then (k : ℂ) * a m * character (m + 1) (θ j) else 0) =
      (k : ℂ) * (∑' m, if k ≤ m then a m * character (m + 1) (θ j) else 0) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    split_ifs <;> ring
  rw [hsum]
  dsimp only [firstOrder]
  calc
    _ = (k : ℂ) * (character k (θ j) * coefficient c a θ j k) := by ring
    _ = _ := by rw [ht]; ring

theorem finite_crossWeight_identity {n : ℕ} (hn : 0 < n) (m : ℕ) (z : ℂ) :
    (2 / (n : ℂ)) * (∑ k ∈ Finset.range n, if k ≤ m then (k : ℂ) * z else 0) =
      (crossWeight n m : ℂ) * z := by
  have hr := crossWeight_eq_sum hn m
  have hc := congrArg Complex.ofReal hr
  push_cast at hc
  rw [hc, mul_assoc, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp

theorem weighted_character_summable {n : ℕ} (hn : 0 < n)
    {a : ℕ → ℂ} (ha : Summable (fun m => ‖a m‖)) (t : ℝ) :
    Summable (fun m => (crossWeight n m : ℂ) * a m * character (m + 1) t) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun m => norm_nonneg _) _ (ha.mul_left (n : ℝ))
  intro m
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_character, mul_one,
    abs_of_nonneg (crossWeight_nonneg n m)]
  exact mul_le_mul_of_nonneg_right (crossWeight_le hn m) (norm_nonneg _)

theorem firstOrder_row_identity {n : ℕ} (hn : 0 < n)
    (c : ℝ) (a : ℕ → ℂ) (θ : Fin n → ℝ) (ha : Summable (fun m => ‖a m‖)) (j : Fin n) :
    (2 / (n : ℂ)) * (∑ k ∈ Finset.range n,
      character k (θ j) * firstOrder (coefficient c a θ j) k) =
      (c : ℂ)⁻¹ * ∑' m, (crossWeight n m : ℂ) * a m * character (m + 1) (θ j) := by
  let f : ℕ → ℕ → ℂ := fun k m =>
    if k ≤ m then (k : ℂ) * a m * character (m + 1) (θ j) else 0
  have hf (k : ℕ) : Summable (f k) := by
    have h := ((character_series_summable ha (θ j) 1).indicator (Set.Ici k)).mul_left (k : ℂ)
    simpa [f, Set.indicator, mul_assoc] using h
  simp_rw [twisted_firstOrder c a θ ha j]
  change (2 / (n : ℂ)) * (∑ k ∈ Finset.range n, (c : ℂ)⁻¹ * ∑' m, f k m) = _
  rw [← Finset.mul_sum, ← Summable.tsum_finsetSum (fun k _ => hf k)]
  calc
    _ = (c : ℂ)⁻¹ * ∑' m, (2 / (n : ℂ)) * (∑ k ∈ Finset.range n, f k m) := by
      rw [tsum_mul_left]
      ring
    _ = _ := by
      congr 1
      apply tsum_congr
      intro m
      simpa [f, mul_assoc] using finite_crossWeight_identity hn m (a m * character (m + 1) (θ j))

/-- Equation (5.10), first as a complex identity. All exchanges of infinite
and finite sums use absolute convergence of the original Laurent coefficients. -/
theorem firstOrder_cross_identity_complex {n : ℕ} (hn : 0 < n)
    (c : ℝ) (a : ℕ → ℂ) (θ : Fin n → ℝ) (ha : Summable (fun m => ‖a m‖)) :
    (2 / (n : ℂ)) * (∑ j, ∑ k ∈ Finset.range n,
      character k (θ j) * firstOrder (coefficient c a θ j) k) =
      (c : ℂ)⁻¹ * crossSeries a θ := by
  rw [Finset.mul_sum]
  simp_rw [firstOrder_row_identity hn c a θ ha]
  rw [← Finset.mul_sum, ← Summable.tsum_finsetSum
    (fun j _ => weighted_character_summable hn ha (θ j))]
  have heq : (∑' m, ∑ j, (crossWeight n m : ℂ) * a m * character (m + 1) (θ j)) =
      ∑' m, (crossWeight n m : ℂ) * a m * powerSum θ (m + 1) := by
    apply tsum_congr
    intro m
    rw [powerSum, Finset.mul_sum]
  rw [heq]
  congr 1
  have hs : Summable (fun m => (crossWeight n m : ℂ) * a m * powerSum θ (m + 1)) := by
    have h := summable_sum (s := Finset.univ) (fun j _ => weighted_character_summable hn ha (θ j))
    simpa [powerSum, Finset.mul_sum] using h
  have h := hs.tsum_eq_zero_add
  simpa [crossSeries, crossWeight, cappedFrequency] using h

theorem firstOrder_cross_identity {n : ℕ} (hn : 0 < n)
    (c : ℝ) (a : ℕ → ℂ) (θ : Fin n → ℝ) (ha : Summable (fun m => ‖a m‖)) :
    (2 / (n : ℝ)) * (∑ j, ∑ k ∈ Finset.range n,
      character k (θ j) * firstOrder (coefficient c a θ j) k).re =
      (crossSeries a θ).re / c := by
  have h := congrArg Complex.re (firstOrder_cross_identity_complex hn c a θ ha)
  have hleft : (2 / (n : ℂ)) = ((2 / (n : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  have hright : (c : ℂ)⁻¹ = ((c⁻¹ : ℝ) : ℂ) := by simp
  rw [hleft, hright] at h
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, div_eq_mul_inv, mul_comm (c⁻¹)] using h

end

end Erdos1045.FaberFourier
