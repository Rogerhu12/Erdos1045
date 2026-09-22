import StructuralNote.FixedSchurNormalInnerEnergy
import StructuralNote.FixedSchurQuadraticExpansion

/-! Uniform estimates for a solution of the actual linearized normal equation.
The estimates cover normalized L1, normalized L2 and the supremum norm.
Existence of the differentiated solution comes from the smooth chart. -/

namespace StructuralNote.FixedSchurRotatedInverse

open Erdos1045.EventualExact SchurLiftBounds
open EdgeCoordinates FixedSchurHarmonicBounds FixedSchurInnerAngles
open FixedSchurNormalInnerEnergy FixedSchurQuadraticExpansion
open scoped BigOperators

noncomputable section

def linearized {n : ℕ} (a b q : Fin n → ℝ) : Fin n → ℝ :=
  fun j => a j * q j + b j * J q j

theorem J_abs_sum_le {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) :
    (∑ j, |J q j|) ≤ 2 * ∑ j, |q j| := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => J_pointwise_l1 hn q j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  exact hs.trans_eq (by field_simp)

theorem meanSquare_le_of_abs_le {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    {C : ℝ} (_hC : 0 ≤ C) (hq : ∀ j, |q j| ≤ C) : meanSquare q ≤ C ^ 2 := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    show q j ^ 2 ≤ C ^ 2 by
      simpa only [sq_abs] using (pow_le_pow_left₀ (abs_nonneg _) (hq j) 2))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold meanSquare
  exact (div_le_iff₀ hnR).2 (by nlinarith only [hs])

theorem J_meanSquare_le {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) :
    meanSquare (J q) ≤ 4 * meanSquare q := by
  have hm : 0 ≤ meanSquare q := by unfold meanSquare; positivity
  have hJ (j : Fin n) : |J q j| ≤ 2 * Real.sqrt (meanSquare q) := by
    apply (J_pointwise_l1 hn q j).trans
    have h := mul_le_mul_of_nonneg_left (normalized_abs_sum_le_sqrt_meanSquare hn q)
      (by norm_num : (0 : ℝ) ≤ 2)
    exact (by ring : (2 : ℝ) / n * ∑ i, |q i| = 2 * ((∑ i, |q i|) / n)).le.trans h
  have h := meanSquare_le_of_abs_le hn (J q) (by positivity) hJ
  simpa only [mul_pow, Real.sq_sqrt hm, show (2 : ℝ) ^ 2 = 4 by norm_num] using h

private theorem point_bound {n : ℕ} (a b q : Fin n → ℝ)
    (ha : ∀ j, |a j - 1| ≤ (1 / 10 : ℝ))
    (hb : ∀ j, |b j| ≤ (1 / 10 : ℝ)) (j : Fin n) :
    |q j| ≤ |linearized a b q j| + |q j| / 10 + |J q j| / 10 := by
  have hid : q j = linearized a b q j - (a j - 1) * q j - b j * J q j := by
    unfold linearized
    ring
  have hsub (x y : ℝ) : |x - y| ≤ |x| + |y| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le x (-y)
  calc
    |q j| = |linearized a b q j - (a j - 1) * q j - b j * J q j| := congrArg abs hid
    _ ≤ |linearized a b q j| + |(a j - 1) * q j| + |b j * J q j| :=
      (hsub _ _).trans (add_le_add (hsub _ _) le_rfl)
    _ ≤ |linearized a b q j| + |q j| / 10 + |J q j| / 10 := by
      rw [abs_mul, abs_mul]
      have h₁ := mul_le_mul_of_nonneg_right (ha j) (abs_nonneg (q j))
      have h₂ := mul_le_mul_of_nonneg_right (hb j) (abs_nonneg (J q j))
      linarith only [h₁, h₂]

theorem solution_l1_bound {n : ℕ} (hn : 0 < n) (a b q : Fin n → ℝ)
    (ha : ∀ j, |a j - 1| ≤ (1 / 10 : ℝ))
    (hb : ∀ j, |b j| ≤ (1 / 10 : ℝ)) :
    (∑ j, |q j|) / (n : ℝ) ≤ 2 * ((∑ j, |linearized a b q j|) / (n : ℝ)) := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => point_bound a b q ha hb j)
  simp only [Finset.sum_add_distrib, ← Finset.sum_div] at hs
  have hJ := J_abs_sum_le hn q
  have hq : 0 ≤ ∑ j, |q j| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hsum : (∑ j, |q j|) ≤ 2 * ∑ j, |linearized a b q j| := by linarith only [hs, hJ, hq]
  exact (div_le_div_of_nonneg_right hsum (Nat.cast_nonneg n : (0 : ℝ) ≤ n)).trans_eq (by ring)

theorem solution_sup_bound {n : ℕ} (hn : 0 < n) (a b q : Fin n → ℝ)
    (ha : ∀ j, |a j - 1| ≤ (1 / 10 : ℝ))
    (hb : ∀ j, |b j| ≤ (1 / 10 : ℝ)) :
    ‖q‖ ≤ 2 * ‖linearized a b q‖ := by
  have hJ := J_norm_le hn q
  have hpoint (j : Fin n) : ‖q j‖ ≤ ‖linearized a b q‖ + 3 * ‖q‖ / 10 := by
    have hqj : |q j| ≤ ‖q‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm q j
    have hJj : |J q j| ≤ ‖J q‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (J q) j
    have hMj : |linearized a b q j| ≤ ‖linearized a b q‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (linearized a b q) j
    rw [Real.norm_eq_abs]
    linarith only [point_bound a b q ha hb j, hqj, hJj, hMj, hJ]
  have hnorm := (pi_norm_le_iff_of_nonneg (by positivity)).2 hpoint
  linarith only [hnorm, norm_nonneg q]

theorem solution_meanSquare_bound {n : ℕ} (hn : 0 < n) (a b q : Fin n → ℝ)
    (ha : ∀ j, |a j - 1| ≤ (1 / 10 : ℝ))
    (hb : ∀ j, |b j| ≤ (1 / 10 : ℝ)) :
    meanSquare q ≤ 4 * meanSquare (linearized a b q) := by
  let f : Fin n → ℝ := fun j => (1 - a j) * q j
  let g : Fin n → ℝ := fun j => -b j * J q j
  have hf : meanSquare f ≤ (1 / 10 : ℝ) ^ 2 * meanSquare q := by
    apply meanSquare_domination f q (by norm_num)
    intro j
    dsimp [f]
    rw [abs_mul, abs_sub_comm 1]
    exact mul_le_mul_of_nonneg_right (ha j) (abs_nonneg _)
  have hg : meanSquare g ≤ (1 / 10 : ℝ) ^ 2 * meanSquare (J q) := by
    apply meanSquare_domination g (J q) (by norm_num)
    intro j
    dsimp [g]
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_right (hb j) (abs_nonneg _)
  have hJ := J_meanSquare_le hn q
  have hfg := meanSquare_add_le f g
  have hid : q = linearized a b q + (f + g) := by
    funext j
    dsimp [linearized, f, g]
    ring
  have hsum := meanSquare_add_le (linearized a b q) (f + g)
  rw [← hid] at hsum
  have hnonneg : 0 ≤ meanSquare q := by unfold meanSquare; positivity
  linarith only [hf, hg, hJ, hfg, hsum, hnonneg]

theorem solution_l2_bound {n : ℕ} (hn : 0 < n) (a b q : Fin n → ℝ)
    (ha : ∀ j, |a j - 1| ≤ (1 / 10 : ℝ))
    (hb : ∀ j, |b j| ≤ (1 / 10 : ℝ)) :
    Real.sqrt (meanSquare q) ≤ 2 * Real.sqrt (meanSquare (linearized a b q)) := by
  have h := Real.sqrt_le_sqrt (solution_meanSquare_bound hn a b q ha hb)
  simpa only [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
    show Real.sqrt 4 = (2 : ℝ) by norm_num] using h

end
end StructuralNote.FixedSchurRotatedInverse
