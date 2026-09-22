import EventualExact.CyclicDistance
import EventualExact.WeightedMaximum
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Algebra.Order.Floor.Semiring

/-! The complete finite maximum principle for inverse-square cyclic weights. -/

noncomputable section

open scoped BigOperators

namespace Erdos1045.EventualExact

variable {n : ℕ}

theorem cyclic_weight_uniform_lower {i j : Fin n} {b : ℝ} (hb : 0 < b) (hji : j ≠ i) :
    4 / (Real.pi * b ^ 2 * (n : ℝ) ^ 2) ≤
      1 / (Real.pi * b ^ 2 * (cyclicDistance i j : ℝ) ^ 2) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  have hd : (0 : ℝ) < cyclicDistance i j := by
    exact_mod_cast cyclicDistance_pos (Ne.symm hji)
  have hdn : 2 * (cyclicDistance i j : ℝ) ≤ n := by
    exact_mod_cast two_mul_cyclicDistance_le i j
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have hs : 4 * (cyclicDistance i j : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ Real.pi * b ^ 2 by positivity)
  nlinarith

theorem cyclic_weight_neighbors_lower {i j : Fin n} {R : ℕ} {b : ℝ}
    (hb : 0 < b) (hR : R < n) (hj : j ∈ cyclicNeighbors i R) :
    1 / (Real.pi * b ^ 2 * (R : ℝ) ^ 2) ≤
      1 / (Real.pi * b ^ 2 * (cyclicDistance i j : ℝ) ^ 2) := by
  have hd : (0 : ℝ) < cyclicDistance i j := by
    exact_mod_cast cyclicDistance_pos (Ne.symm (mem_cyclicNeighbors_ne hR hj))
  have hdR : (cyclicDistance i j : ℝ) ≤ R := by
    exact_mod_cast mem_cyclicNeighbors_distance_le hR hj
  apply one_div_le_one_div_of_le (by positivity)
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  nlinarith

/-- The pointwise maximum version; its neighbor set is explicitly constructed. -/
theorem cyclic_cubic_maximum_at_max {w : Fin n → Fin n → ℝ} {s : Fin n → ℝ}
    {i : Fin n} {M b : ℝ} (hb : 0 < b) (hM : 0 < M) (hi : s i = M)
    (hs : ∀ j, s j ≤ M) (hzero : ∑ j, s j = 0)
    (hw0 : ∀ j, 0 ≤ w i j)
    (hw : ∀ j, j ≠ i →
      1 / (Real.pi * b ^ 2 * (cyclicDistance i j : ℝ) ^ 2) ≤ w i j) :
    M ^ 3 ≤ 36 * Real.pi * b ^ 2 * finiteSquareMass s * weightedLaplacian w s i := by
  let S := finiteSquareMass s
  have hS : M ^ 2 ≤ S := maximum_sq_le_finiteSquareMass hi
  have hS0 : 0 ≤ S := finiteSquareMass_nonneg s
  have hSpos : 0 < S := lt_of_lt_of_le (sq_pos_of_pos hM) hS
  let R : ℕ := ⌈8 * S / M ^ 2⌉₊
  have hceil : 8 * S / M ^ 2 ≤ (R : ℝ) := Nat.le_ceil _
  have hceil_lt : (R : ℝ) < 8 * S / M ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hRmass : 8 * S ≤ (R : ℝ) * M ^ 2 := (div_le_iff₀ (sq_pos_of_pos hM)).1 hceil
  have hRupper : (R : ℝ) * M ^ 2 ≤ 9 * S := by
    have h := (lt_div_iff₀ (sq_pos_of_pos hM)).1
      (show (R : ℝ) - 1 < 8 * S / M ^ 2 by linarith)
    nlinarith
  have hRpos : (0 : ℝ) < R := by nlinarith
  by_cases hRn : R < n
  · have hweights : ∀ j ∈ cyclicNeighbors i R,
        1 / (Real.pi * b ^ 2 * (R : ℝ) ^ 2) ≤ w i j := by
      intro j hj
      exact (cyclic_weight_neighbors_lower hb hRn hj).trans
        (hw j (mem_cyclicNeighbors_ne hRn hj))
    have hbudget : 8 * finiteSquareMass s ≤ (cyclicNeighbors i R).card * M ^ 2 := by
      rw [cyclicNeighbors_card i hRn]
      exact hRmass
    have hl := weightedLaplacian_ge_half_card hi hM (by positivity) hs hw0
      (cyclicNeighbors i R) hweights hbudget
    rw [cyclicNeighbors_card i hRn] at hl
    have he : (R : ℝ) * (1 / (Real.pi * b ^ 2 * (R : ℝ) ^ 2)) * M / 4 =
        M / (4 * Real.pi * b ^ 2 * R) := by field_simp
    rw [he] at hl
    have hm := mul_le_mul_of_nonneg_left hl
      (show 0 ≤ 36 * Real.pi * b ^ 2 * S by positivity)
    have he' : 36 * Real.pi * b ^ 2 * S * (M / (4 * Real.pi * b ^ 2 * R)) =
        9 * S * M / R := by field_simp; ring
    rw [he'] at hm
    apply le_trans ?_ hm
    apply (le_div_iff₀ hRpos).2
    nlinarith [mul_le_mul_of_nonneg_right hRupper hM.le]
  · have hnR : (n : ℝ) ≤ R := by exact_mod_cast le_of_not_gt hRn
    have hbudget : (Fintype.card (Fin n) : ℝ) * M ^ 2 / 12 ≤ S := by
      simp only [Fintype.card_fin]
      have hm := mul_le_mul_of_nonneg_right hnR (sq_nonneg M)
      nlinarith
    have hglobal : ∀ j, j ≠ i →
        4 / (Real.pi * b ^ 2 * (Fintype.card (Fin n) : ℝ) ^ 2) ≤ w i j := by
      intro j hji
      simpa only [Fintype.card_fin] using (cyclic_weight_uniform_lower hb hji).trans (hw j hji)
    have hl := cubic_maximum_le_three_pi hi hM.le (ne_of_gt hb) hs hzero hglobal hbudget
    have hlap : 0 ≤ weightedLaplacian w s i := weightedLaplacian_nonneg_at_max hw0
      (fun j => (hs j).trans_eq hi.symm)
    nlinarith [mul_nonneg (show 0 ≤ Real.pi * b ^ 2 * S by positivity) hlap]

@[simp] theorem weightedLaplacian_neg (w : Fin n → Fin n → ℝ) (s : Fin n → ℝ) (i : Fin n) :
    weightedLaplacian w (-s) i = -weightedLaplacian w s i := by
  unfold weightedLaplacian
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.neg_apply]
  ring

@[simp] theorem finiteSquareMass_neg (s : Fin n → ℝ) : finiteSquareMass (-s) = finiteSquareMass s := by
  simp [finiteSquareMass]

/-- The full norm form of manuscript (2.22), including negative extremal values. -/
theorem cyclic_cubic_maximum {w : Fin n → Fin n → ℝ} {s : Fin n → ℝ}
    (hn : 0 < n) {b : ℝ} (hb : 0 < b) (hzero : ∑ j, s j = 0)
    (hw0 : ∀ i j, 0 ≤ w i j)
    (hw : ∀ i j, j ≠ i →
      1 / (Real.pi * b ^ 2 * (cyclicDistance i j : ℝ) ^ 2) ≤ w i j) :
    ‖s‖ ^ 3 ≤ 36 * Real.pi * b ^ 2 * finiteSquareMass s * ‖weightedLaplacian w s‖ := by
  classical
  let : NeZero n := ⟨ne_of_gt hn⟩
  obtain ⟨i, _, himax⟩ := Finset.exists_max_image Finset.univ (fun i : Fin n => |s i|)
    Finset.univ_nonempty
  have hmax : ∀ j, |s j| ≤ |s i| := fun j => himax j (Finset.mem_univ j)
  have hnorm : ‖s‖ = |s i| := by
    apply le_antisymm
    · exact (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun j => by
        simpa only [Real.norm_eq_abs] using hmax j
    · simpa only [Real.norm_eq_abs] using norm_le_pi_norm s i
  have hfactor : 0 ≤ 36 * Real.pi * b ^ 2 * finiteSquareMass s := by
    have := finiteSquareMass_nonneg s
    positivity
  by_cases hM : |s i| = 0
  · simpa only [hnorm, hM, zero_pow (by decide : (3 : ℕ) ≠ 0)] using
      mul_nonneg hfactor (norm_nonneg (weightedLaplacian w s))
  have hMpos : 0 < |s i| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hM)
  by_cases hsi : 0 ≤ s i
  · have hi : s i = |s i| := (abs_of_nonneg hsi).symm
    have hs : ∀ j, s j ≤ |s i| := fun j => (le_abs_self _).trans (hmax j)
    have hl := cyclic_cubic_maximum_at_max hb hMpos hi hs hzero (hw0 i) (hw i)
    have hlap : weightedLaplacian w s i ≤ ‖weightedLaplacian w s‖ :=
      (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (weightedLaplacian w s) i))
    rw [hnorm]
    exact hl.trans (mul_le_mul_of_nonneg_left hlap hfactor)
  · have hi : (-s) i = |s i| := by simp only [Pi.neg_apply, abs_of_neg (lt_of_not_ge hsi)]
    have hs : ∀ j, (-s) j ≤ |s i| := fun j => (neg_le_abs _).trans (hmax j)
    have hz : ∑ j, (-s) j = 0 := by simp [hzero]
    have hl := cyclic_cubic_maximum_at_max hb hMpos hi hs hz (hw0 i) (hw i)
    rw [finiteSquareMass_neg, weightedLaplacian_neg] at hl
    have hlap : -weightedLaplacian w s i ≤ ‖weightedLaplacian w s‖ :=
      (neg_le_abs _).trans (by simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (weightedLaplacian w s) i))
    rw [hnorm]
    exact hl.trans (mul_le_mul_of_nonneg_left hlap hfactor)

end Erdos1045.EventualExact
