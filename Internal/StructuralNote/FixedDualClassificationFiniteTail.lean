import StructuralNote.FixedDualClassificationKernel
import EventualExact.SchurOperatorBounds
import EventualExact.SchurWeightBounds
import Mathlib.Analysis.PSeries

/-! Uniform high-frequency bounds for the actual finite Schur multiplier.
Both reflected ends of the finite frequency interval are retained. -/

namespace StructuralNote.FixedDualClassificationFiniteTail

open Real Erdos1045.EventualExact FourierMultiplier SchurOperatorBounds
open SchurLiftBounds
open scoped BigOperators
noncomputable section

theorem reciprocal_square_sum_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (r : ι → ℕ) {P n : ℕ} (hinj : Set.InjOn r s)
    (hr : ∀ i ∈ s, P < r i ∧ r i ≤ n) :
    ∑ i ∈ s, ((r i : ℝ) ^ 2)⁻¹ ≤ 2 / ((P : ℝ) + 1) := by
  rw [← Finset.sum_image (f := fun k : ℕ => ((k : ℝ) ^ 2)⁻¹) hinj]
  apply le_trans _ (sum_Ioo_inv_sq_le (α := ℝ) P (n + 1))
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_Ioo.mpr ⟨(hr i hi).1, Nat.lt_succ_of_le (hr i hi).2⟩
  · intro k _ _
    positivity

theorem weight_square_le_reciprocal_ends {n : ℕ} (hn : Even n) (p : Fin n)
    (hp0 : 0 < (p : ℕ)) :
    SchurWeights.weight n p ^ 2 ≤
      2 * ((p : ℝ) ^ 2)⁻¹ + 2 * (((n - p : ℕ) : ℝ) ^ 2)⁻¹ := by
  have hnp : (0 : ℝ) < (n - p : ℕ) := by exact_mod_cast (Nat.sub_pos_of_lt p.isLt)
  have hp : (0 : ℝ) < p := by exact_mod_cast hp0
  have h := (SchurWeights.weight_le_endpoints p.isLt.le hn).trans
    (add_le_add (SchurWeights.endpointReciprocal_le n p)
      (SchurWeights.endpointReciprocal_le n (n - p)))
  have h1 : 1 / ((p : ℝ) + 1) ≤ 1 / p :=
    one_div_le_one_div_of_le hp (by linarith)
  have h2 : 1 / (((n - p : ℕ) : ℝ) + 1) ≤ 1 / ((n - p : ℕ) : ℝ) :=
    one_div_le_one_div_of_le hnp (by linarith)
  have hw : SchurWeights.weight n p ≤ 1 / p + 1 / ((n - p : ℕ) : ℝ) :=
    h.trans (add_le_add h1 h2)
  have hsq := (sq_le_sq₀ (SchurWeights.weight_nonneg n p)
    (add_nonneg (by positivity) (by positivity))).mpr hw
  have hid1 : (1 / (p : ℝ)) ^ 2 = ((p : ℝ) ^ 2)⁻¹ := by simp only [one_div, inv_pow]
  have hid2 : (1 / ((n - p : ℕ) : ℝ)) ^ 2 = (((n - p : ℕ) : ℝ) ^ 2)⁻¹ := by
    simp only [one_div, inv_pow]
  nlinarith [sq_nonneg (1 / (p : ℝ) - 1 / ((n - p : ℕ) : ℝ))]

theorem weight_tail_square_mass {n P : ℕ} (hn : Even n) (s : Finset (Fin n))
    (hs : ∀ p ∈ s, P < min (p : ℕ) (n - p)) :
    ∑ p ∈ s, SchurWeights.weight n p ^ 2 ≤ 8 / ((P : ℝ) + 1) := by
  have hpos := reciprocal_square_sum_le s (fun p : Fin n => p.val)
    (fun _ _ _ _ h => Fin.ext h)
    (fun p hp => ⟨lt_of_lt_of_le (hs p hp) (min_le_left _ _), p.isLt.le⟩)
  have hneg := reciprocal_square_sum_le s (fun p : Fin n => n - p.val)
    (fun p _ q _ h => Fin.ext (by
      dsimp only at h
      have hp := p.isLt
      have hq := q.isLt
      omega))
    (fun p hp => ⟨lt_of_lt_of_le (hs p hp) (min_le_right _ _), Nat.sub_le _ _⟩)
  have h := Finset.sum_le_sum (fun p hp => weight_square_le_reciprocal_ends hn p
    (by have hh := lt_of_lt_of_le (hs p hp) (min_le_left _ _); omega))
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h
  calc
    _ ≤ 2 * (2 / ((P : ℝ) + 1)) + 2 * (2 / ((P : ℝ) + 1)) := by linarith
    _ = _ := by ring

def partialPotential {n : ℕ} (q : Fin n → ℝ) (s : Finset (Fin n)) (j : Fin n) : ℂ :=
  ∑ p ∈ s, (SchurWeights.weight n p : ℂ) * realCoefficient q p * character n p j

theorem partialPotential_sq_le {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (s : Finset (Fin n)) (j : Fin n) :
    ‖partialPotential q s j‖ ^ 2 ≤
      (∑ p ∈ s, SchurWeights.weight n p ^ 2) * meanSquare q := by
  have hnorm : ‖partialPotential q s j‖ ≤
      ∑ p ∈ s, SchurWeights.weight n p * ‖realCoefficient q p‖ := by
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro p _
    simp [character, Erdos1045.ClosedFourier.root_norm, SchurWeights.weight_nonneg,
      abs_of_nonneg]
  have hpos : 0 ≤ ∑ p ∈ s, SchurWeights.weight n p * ‖realCoefficient q p‖ :=
    Finset.sum_nonneg (fun p _ => mul_nonneg (SchurWeights.weight_nonneg _ _) (norm_nonneg _))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun p => SchurWeights.weight n p) (fun p => ‖realCoefficient q p‖)
  have hb : ∑ p ∈ s, ‖realCoefficient q p‖ ^ 2 ≤ meanSquare q := by
    rw [← realCoefficient_parseval hn q]
    simp_rw [Complex.normSq_eq_norm_sq]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun _ _ _ => sq_nonneg _)
  exact ((sq_le_sq₀ (norm_nonneg _) hpos).mpr hnorm).trans
    (hcs.trans (mul_le_mul_of_nonneg_left hb (Finset.sum_nonneg (fun _ _ => sq_nonneg _))))

theorem partialPotential_tail_sq_le {n P : ℕ} (hn : 0 < n) (heven : Even n)
    (q : Fin n → ℝ) (s : Finset (Fin n))
    (hs : ∀ p ∈ s, P < min (p : ℕ) (n - p)) (j : Fin n) :
    ‖partialPotential q s j‖ ^ 2 ≤ 8 / ((P : ℝ) + 1) * meanSquare q :=
  (partialPotential_sq_le hn q s j).trans
    (mul_le_mul_of_nonneg_right (weight_tail_square_mass heven s hs) (meanSquare_nonneg q))

def lowFrequencies (n P : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => min (p : ℕ) (n - p) ≤ P)

theorem operator_lowFrequency_error {n P : ℕ} (hn : 0 < n) (heven : Even n)
    (q : Fin n → ℝ) (j : Fin n) :
    ‖(operator n q j : ℂ) - partialPotential q (lowFrequencies n P) j‖ ^ 2 ≤
      8 / ((P : ℝ) + 1) * meanSquare q := by
  classical
  have he : (operator n q j : ℂ) - partialPotential q (lowFrequencies n P) j =
      partialPotential q (Finset.univ \ lowFrequencies n P) j := by
    rw [operator_eq_synthesis hn heven]
    unfold synthesis partialPotential
    exact (Finset.sum_sdiff_eq_sub (Finset.subset_univ _)).symm
  rw [he]
  apply partialPotential_tail_sq_le hn heven q _ _ j
  intro p hp
  have h := (Finset.mem_sdiff.mp hp).2
  simpa only [lowFrequencies, Finset.mem_filter, Finset.mem_univ, true_and, not_le] using h

def partialEnergy {n : ℕ} (q : Fin n → ℝ) (s : Finset (Fin n)) : ℝ :=
  (1 / 2) * ∑ p ∈ s, SchurWeights.weight n p * Complex.normSq (realCoefficient q p)

theorem partialEnergy_nonneg {n : ℕ} (q : Fin n → ℝ) (s : Finset (Fin n)) :
    0 ≤ partialEnergy q s := by
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg (fun p _ => mul_nonneg (SchurWeights.weight_nonneg _ _)
    (Complex.normSq_nonneg _))

theorem partialEnergy_tail_le {n P : ℕ} (hn : 0 < n) (heven : Even n)
    (q : Fin n → ℝ) (s : Finset (Fin n))
    (hs : ∀ p ∈ s, P < min (p : ℕ) (n - p)) :
    partialEnergy q s ≤ meanSquare q / ((P : ℝ) + 1) := by
  have hw (p : Fin n) (hp : p ∈ s) : SchurWeights.weight n p ≤ 2 / ((P : ℝ) + 1) := by
    apply (SchurWeights.weight_le_two_div_min p.isLt.le heven).trans
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have h := hs p hp
    have hh : (P : ℝ) ≤ (min (p : ℕ) (n - p) : ℕ) := by exact_mod_cast h.le
    linarith
  have hb : ∑ p ∈ s, Complex.normSq (realCoefficient q p) ≤ meanSquare q := by
    rw [← realCoefficient_parseval hn q]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun _ _ _ => Complex.normSq_nonneg _)
  unfold partialEnergy
  calc
    _ ≤ (1 / 2 : ℝ) * ∑ p ∈ s, (2 / ((P : ℝ) + 1)) * Complex.normSq (realCoefficient q p) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum (fun p hp => mul_le_mul_of_nonneg_right (hw p hp) (Complex.normSq_nonneg _))
    _ = (∑ p ∈ s, Complex.normSq (realCoefficient q p)) / ((P : ℝ) + 1) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right hb (by positivity)

theorem energy_lowFrequency_error {n P : ℕ} (hn : 0 < n) (heven : Even n)
    (q : Fin n → ℝ) :
    0 ≤ normalizedBoxEnergy (operator n) q - partialEnergy q (lowFrequencies n P) ∧
    normalizedBoxEnergy (operator n) q - partialEnergy q (lowFrequencies n P) ≤
      meanSquare q / ((P : ℝ) + 1) := by
  classical
  have he : normalizedBoxEnergy (operator n) q - partialEnergy q (lowFrequencies n P) =
      partialEnergy q (Finset.univ \ lowFrequencies n P) := by
    rw [spectral_energy hn q]
    unfold partialEnergy
    rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ _)]
    ring
  rw [he]
  refine ⟨partialEnergy_nonneg q _, partialEnergy_tail_le hn heven q _ ?_⟩
  intro p hp
  have h := (Finset.mem_sdiff.mp hp).2
  simpa only [lowFrequencies, Finset.mem_filter, Finset.mem_univ, true_and, not_le] using h

end
end StructuralNote.FixedDualClassificationFiniteTail
