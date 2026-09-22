import StructuralNote.FixedSchurNormalScalarDifference

/-! Finite-sum normal-error comparison, retaining the support of sign changes
and the mean of the angle instead of its maximum. -/

namespace StructuralNote.FixedSchurNormalDifferenceSum

open FixedSchurNormalScalarDifference
open scoped BigOperators

noncomputable section

def normalTerm (ε σ a p b s c : ℝ) : ℝ :=
  σ * a - p * Real.tan b - c * (σ * rootCorrection ε s)

theorem normalTerm_difference {ε σ τ a p p' b s t c A D P C : ℝ}
    (hε : ε ≠ 0) (_hA : 0 ≤ A) (_hD : 0 ≤ D) (hP : 0 ≤ P) (hC : 0 ≤ C)
    (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1)
    (ha : |a| ≤ A) (hp : |p - p'| ≤ D) (hc : |c| ≤ C)
    (hs : |s| ≤ P) (ht : |t| ≤ P) (hes : |ε * s| ≤ 1) (het : |ε * t| ≤ 1) :
    |normalTerm ε σ a p b s c - normalTerm ε τ a p' b t c| ≤
      (if σ ≠ τ then 2 * A else 0) + D * |Real.tan b| +
        C * (P * |s - t| + if σ ≠ τ then P ^ 2 else 0) := by
  have hsign : |(σ - τ) * a| ≤ if σ ≠ τ then 2 * A else 0 := by
    split_ifs with h
    · have hd : |σ - τ| ≤ 2 := by
        rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> norm_num
      rw [abs_mul]
      exact mul_le_mul hd ha (abs_nonneg _) (by norm_num)
    · have heq : σ = τ := not_ne_iff.mp h
      simp only [heq, sub_self, zero_mul, abs_zero, le_refl]
  have hroot := signed_rootCorrection_difference hε hP hs ht hes het hσ hτ
  have hid : normalTerm ε σ a p b s c - normalTerm ε τ a p' b t c =
      (σ - τ) * a - (p - p') * Real.tan b -
        c * (σ * rootCorrection ε s - τ * rootCorrection ε t) := by
    unfold normalTerm
    ring
  rw [hid]
  apply (abs_sub _ _).trans
  apply add_le_add
  · exact (abs_sub _ _).trans (add_le_add hsign (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hp (abs_nonneg _)))
  · rw [abs_mul]
    exact mul_le_mul hc hroot (abs_nonneg _) hC

theorem normalTerm_sum_difference {n : ℕ} (ε : ℝ) (hε : ε ≠ 0)
    (σ τ a p p' b s t c : Fin n → ℝ) {A D P C H : ℝ}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hP : 0 ≤ P) (hC : 0 ≤ C) (_hH : 0 ≤ H)
    (hσ : ∀ j, σ j = 1 ∨ σ j = -1) (hτ : ∀ j, τ j = 1 ∨ τ j = -1)
    (ha : ∀ j, |a j| ≤ A) (hp : ∀ j, |p j - p' j| ≤ D)
    (hc : ∀ j, |c j| ≤ C) (hs : ∀ j, |s j| ≤ P) (ht : ∀ j, |t j| ≤ P)
    (hes : ∀ j, |ε * s j| ≤ 1) (het : ∀ j, |ε * t j| ≤ 1)
    (hst : ∀ j, |s j - t j| ≤ H) :
    (∑ j, |normalTerm ε (σ j) (a j) (p j) (b j) (s j) (c j) -
      normalTerm ε (τ j) (a j) (p' j) (b j) (t j) (c j)|) ≤
        2 * A * ((Finset.univ.filter (fun j => σ j ≠ τ j)).card : ℝ) +
          D * (∑ j, |Real.tan (b j)|) +
          C * (P * H * n + P ^ 2 * ((Finset.univ.filter (fun j => σ j ≠ τ j)).card : ℝ)) := by
  classical
  have hpoint (j : Fin n) := normalTerm_difference (b := b j) hε hA hD hP hC (hσ j) (hτ j)
    (ha j) (hp j) (hc j) (hs j) (ht j) (hes j) (het j)
  have hb (j : Fin n) :
      |normalTerm ε (σ j) (a j) (p j) (b j) (s j) (c j) -
        normalTerm ε (τ j) (a j) (p' j) (b j) (t j) (c j)| ≤
      (if σ j ≠ τ j then 2 * A else 0) + D * |Real.tan (b j)| +
        C * (P * H + if σ j ≠ τ j then P ^ 2 else 0) := by
    apply (hpoint j).trans
    gcongr
    exact hst j
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hb j)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite,
    Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ, Fintype.card_fin] at hsum
  exact hsum.trans_eq (by ring)

theorem scaled_budget {n A D P H T k : ℝ} (hn : 0 < n)
    {X Y : ℝ} (hD : 0 ≤ D)
    (hX : X ≤ 2 * (A / n ^ 2) * k + (D / n) * Y +
      (16 / n ^ 2) * (P * (H / n) * n + P ^ 2 * k))
    (hY : Y / n ≤ T / n ^ 2) :
    X / n ≤ (2 * A * k + D * T + 16 * P * H + 16 * P ^ 2 * k) / n ^ 3 := by
  have hY' := (div_le_iff₀ hn).mp hY
  have hfirst := div_le_div_of_nonneg_right hX hn.le
  apply hfirst.trans
  calc
    _ ≤ (2 * (A / n ^ 2) * k + (D / n) * (T / n ^ 2 * n) +
        (16 / n ^ 2) * (P * (H / n) * n + P ^ 2 * k)) / n := by
      gcongr
    _ = _ := by field_simp; ring

end
end StructuralNote.FixedSchurNormalDifferenceSum
