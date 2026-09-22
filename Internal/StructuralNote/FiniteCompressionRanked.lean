import StructuralNote.FiniteCompressionEnergy
import StructuralNote.FiniteCompressionInteraction
import StructuralNote.FiniteCompressionOnePass

/-! Ordered site enumerations connect the one-pass score to the actual finite
Schur energy, with no assumed energy representation. -/

namespace StructuralNote.FiniteCompressionRanked

open Erdos1045.EventualExact FourierMultiplier FixedDualClassificationKernel
open FiniteCompressionEnergy FiniteCompressionGain FiniteCompressionInteraction
open FiniteCompressionOnePass
open scoped BigOperators
noncomputable section

def gridKernel (n : ℕ) (d : ℕ) : ℝ := finiteKernel n (2 * Real.pi * d / n)

theorem kernel_grid_distance {n : ℕ} (i j : Fin n) :
    finiteKernel n (gridAngle i - gridAngle j) = gridKernel n (Nat.dist i.val j.val) := by
  unfold gridKernel
  rcases le_total i.val j.val with hij | hij
  · rw [Nat.dist_eq_sub_of_le hij, Nat.cast_sub hij]
    rw [← finiteKernel_even n (gridAngle i - gridAngle j)]
    congr 1
    unfold gridAngle
    ring
  · rw [Nat.dist_eq_sub_of_le_right hij, Nat.cast_sub hij]
    congr 1
    unfold gridAngle
    ring

def site {m : ℕ} (hm : 0 < m) (k : ℕ) : Fin (2 * m) :=
  ⟨k % (2 * m), Nat.mod_lt _ (by omega)⟩

theorem site_val {m : ℕ} (hm : 0 < m) {k : ℕ} (hk : k < 2 * m) :
    (site hm k).val = k := Nat.mod_eq_of_lt hk

def sites {m : ℕ} (hm : 0 < m) (ℓ : ℕ) (e : ℕ → ℕ) : Finset (Fin (2 * m)) :=
  (Finset.range ℓ).image (fun j => site hm (e j))

theorem sum_sites {m ℓ : ℕ} (hm : 0 < m) (e : ℕ → ℕ)
    (he : StrictMonoOn e (Set.Iio ℓ)) (hbound : ∀ j < ℓ, e j < 2 * m)
    (f : Fin (2 * m) → ℝ) :
    (∑ i ∈ sites hm ℓ e, f i) = ∑ j ∈ Finset.range ℓ, f (site hm (e j)) := by
  apply Finset.sum_image
  intro i hi j hj hij
  apply he.injOn (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
  have h := congrArg Fin.val hij
  simpa only [site_val hm (hbound i (Finset.mem_range.mp hi)),
    site_val hm (hbound j (Finset.mem_range.mp hj))] using h

theorem self_sum_eq_interaction {m ℓ : ℕ} (hm : 0 < m) (e : ℕ → ℕ)
    (he : StrictMonoOn e (Set.Iio ℓ)) (hbound : ∀ j < ℓ, e j < 2 * m) :
    (∑ i ∈ sites hm ℓ e, ∑ j ∈ sites hm ℓ e,
      finiteKernel (2 * m) (gridAngle i - gridAngle j)) = interaction ℓ (gridKernel (2 * m)) e := by
  rw [sum_sites hm e he hbound]
  simp_rw [sum_sites hm e he hbound]
  rw [interaction_eq_double_sum _ e he]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [kernel_grid_distance, site_val hm (hbound i (Finset.mem_range.mp hi)),
    site_val hm (hbound j (Finset.mem_range.mp hj))]

theorem energy_eq_score {m ℓ : ℕ} (hm : 0 < m) (A : ℝ) (e : ℕ → ℕ)
    (he : StrictMonoOn e (Set.Iio ℓ)) (hbound : ∀ j < ℓ, e j < 2 * m)
    (b : Fin (2 * m) → ℝ) :
    normalizedBoxEnergy (operator (2 * m)) (b + patch hm A (sites hm ℓ e)) =
      normalizedBoxEnergy (operator (2 * m)) b +
        score ℓ (gridKernel (2 * m)) (fun k => operator (2 * m) b (site hm k))
          (4 * A / (2 * m : ℝ)) (16 * A ^ 2 / (2 * m : ℝ) ^ 2) e := by
  rw [energy_add_patch, sum_sites hm e he hbound, self_sum_eq_interaction hm e he hbound]
  unfold score
  ring

end
end StructuralNote.FiniteCompressionRanked
