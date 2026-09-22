import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

/-!
# Concrete point configurations and scale-invariant objective

The discriminant is the product over ordered distinct pairs of distances.
Each unordered distance therefore occurs twice, exactly as in the paper.
No perimeter, extremality, or regularity conclusion is assumed here.
-/

namespace Erdos1045.Configuration

open scoped BigOperators
noncomputable section

abbrev Points (n : ℕ) := Fin n → ℂ

def exponent (n : ℕ) : ℕ := n * (n - 1)

def discriminant {n : ℕ} (z : Points n) : ℝ :=
  ∏ i, ∏ j ∈ Finset.univ.erase i, ‖z i - z j‖

def boundaryLength {n : ℕ} (z : Points n) : ℝ :=
  ∑ i, ‖z (finRotate n i) - z i‖

def objective {n : ℕ} (z : Points n) : ℝ :=
  Real.log (discriminant z) - (exponent n : ℝ) * Real.log (boundaryLength z)

def regular (n : ℕ) : Points n :=
  fun j => Complex.exp (((2 * Real.pi * (j : ℝ) / n : ℝ) : ℂ) * Complex.I)

def IsRegular {n : ℕ} (z : Points n) : Prop :=
  ∃ a b : ℂ, b ≠ 0 ∧ ∃ σ : Equiv.Perm (Fin n),
    ∀ j, z j = a + b * regular n (σ j)

def DiameterAtMost {n : ℕ} (d : ℝ) (z : Points n) : Prop :=
  ∀ i j, ‖z i - z j‖ ≤ d

theorem discriminant_nonneg {n : ℕ} (z : Points n) : 0 ≤ discriminant z := by
  exact Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => norm_nonneg _

theorem discriminant_pos {n : ℕ} (z : Points n) (hz : Function.Injective z) :
    0 < discriminant z := by
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j hj
  apply norm_pos_iff.mpr
  exact sub_ne_zero.mpr (fun h => (Finset.ne_of_mem_erase hj) (hz h).symm)

theorem boundaryLength_nonneg {n : ℕ} (z : Points n) : 0 ≤ boundaryLength z :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem discriminant_affine {n : ℕ} (z : Points n) (a b : ℂ) :
    discriminant (fun i => a + b * z i) = ‖b‖ ^ exponent n * discriminant z := by
  have hdiff (i j : Fin n) : a + b * z i - (a + b * z j) = b * (z i - z j) := by ring
  simp_rw [discriminant, hdiff, norm_mul, Finset.prod_mul_distrib]
  have hcard (i : Fin n) : (Finset.univ.erase i).card = n - 1 := by simp
  simp only [Finset.prod_const, hcard, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul]
  simp only [exponent, Nat.mul_comm]

theorem boundaryLength_affine {n : ℕ} (z : Points n) (a b : ℂ) :
    boundaryLength (fun i => a + b * z i) = ‖b‖ * boundaryLength z := by
  have hdiff (i : Fin n) : a + b * z (finRotate n i) - (a + b * z i) =
      b * (z (finRotate n i) - z i) := by ring
  simp_rw [boundaryLength, hdiff, norm_mul]
  exact (Finset.mul_sum _ _ _).symm

theorem objective_affine {n : ℕ} (z : Points n) (a b : ℂ) (hb : b ≠ 0)
    (hD : 0 < discriminant z) (hL : 0 < boundaryLength z) :
    objective (fun i => a + b * z i) = objective z := by
  have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
  rw [objective, discriminant_affine, boundaryLength_affine,
    Real.log_mul (pow_pos hbpos _).ne' hD.ne', Real.log_pow,
    Real.log_mul hbpos.ne' hL.ne', objective]
  ring

theorem regular_isRegular (n : ℕ) : IsRegular (regular n) := by
  refine ⟨0, 1, one_ne_zero, Equiv.refl _, ?_⟩
  intro j
  simp

theorem isRegular_affine {n : ℕ} {z : Points n} (hz : IsRegular z)
    (a b : ℂ) (hb : b ≠ 0) : IsRegular (fun i => a + b * z i) := by
  rcases hz with ⟨c, d, hd, σ, hz⟩
  refine ⟨a + b * c, b * d, mul_ne_zero hb hd, σ, ?_⟩
  intro j
  dsimp only
  rw [hz j]
  ring

theorem isRegular_of_affine {n : ℕ} (z : Points n) (a b : ℂ) (hb : b ≠ 0)
    (hz : IsRegular (fun i => a + b * z i)) : IsRegular z := by
  rcases hz with ⟨c, d, hd, σ, hz⟩
  refine ⟨(c - a) / b, d / b, div_ne_zero hd hb, σ, ?_⟩
  intro j
  have h := hz j
  dsimp only at h
  field_simp
  linear_combination h

theorem diameter_affine {n : ℕ} {d : ℝ} {z : Points n}
    (hz : DiameterAtMost d z) (a b : ℂ) :
    DiameterAtMost (‖b‖ * d) (fun i => a + b * z i) := by
  intro i j
  rw [show a + b * z i - (a + b * z j) = b * (z i - z j) by ring, norm_mul]
  exact mul_le_mul_of_nonneg_left (hz i j) (norm_nonneg _)

end
end Erdos1045.Configuration
