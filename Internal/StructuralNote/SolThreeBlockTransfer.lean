import StructuralNote.SolThreeBlockWord
import StructuralNote.SolUnitTransfer

namespace StructuralNote.SolThreeBlockTransfer

open Erdos1045.EventualExact.FiniteBox
open StructuralNote.SolWordHamming StructuralNote.SolThreeBlockWord
open StructuralNote.DiscreteConvexBalance StructuralNote.SolUnitTransfer Set
noncomputable section

private theorem support_subset_of_eq_outside {m : ℕ} {hm : 0 < m}
    (s t : SignPattern hm) (E : Finset (Fin m))
    (hout : ∀ j : Fin m, j ∉ E → patternSign s (first j) = patternSign t (first j)) :
    changedSupport s t ⊆ E := by
  intro j hj
  by_contra h
  have hne : patternSign s (first j) ≠ patternSign t (first j) := by
    simpa [changedSupport] using hj
  exact hne (hout j h)

private theorem transfer12_support {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m)
    (hgap : r₂ + 2 ≤ r₁) :
    changedSupport (threeBlockPattern hm hpos hsum)
      (threeBlockPattern (r₁ := r₁ - 1) (r₂ := r₂ + 1) (r₃ := r₃) hm
        (by omega) (by omega : (r₁ - 1) + (r₂ + 1) + r₃ = m)) ⊆
      {⟨r₁ - 1, by omega⟩} := by
  apply support_subset_of_eq_outside
  intro j hj
  simp only [Finset.mem_singleton] at hj
  have hjv : j.val ≠ r₁ - 1 := by
    intro h; apply hj; apply Fin.ext; exact h
  clear hj
  have hp : r₁ - 1 + 1 = r₁ := by omega
  have hup : (r₁ - 1) + (r₂ + 1) = r₁ + r₂ := by omega
  have hl : (j.val < r₁) ↔ (j.val < r₁ - 1) := by omega
  simp only [patternSign_threeBlockPattern, threeBlockRaw, first,
    Nat.mod_eq_of_lt j.isLt, if_pos j.isLt, halfValue]
  simp [hup, hl]

theorem transfer12 {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m)
    (hgap : r₂ + 2 ≤ r₁) :
    0 < r₁ - 1 ∧ 0 < r₂ + 1 ∧ 0 < r₃ ∧
    (r₁ - 1) + (r₂ + 1) + r₃ = m ∧
    hamming (threeBlockPattern hm hpos hsum)
      (threeBlockPattern (r₁ := r₁ - 1) (r₂ := r₂ + 1) (r₃ := r₃) hm
        (by omega) (by omega)) ≤ 2 := by
  refine ⟨by omega, by omega, hpos.2.2, by omega, ?_⟩
  have h := hamming_le_card_of_support_subset _ _ _
    (transfer12_support hm hpos hsum hgap)
  calc
    _ ≤ 1 := by simpa using h
    _ ≤ 2 := by omega

private theorem transfer23_support {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m)
    (hgap : r₃ + 2 ≤ r₂) :
    changedSupport (threeBlockPattern hm hpos hsum)
      (threeBlockPattern (r₁ := r₁) (r₂ := r₂ - 1) (r₃ := r₃ + 1) hm
        (by omega) (by omega : r₁ + (r₂ - 1) + (r₃ + 1) = m)) ⊆
      {⟨r₁ + r₂ - 1, by omega⟩} := by
  apply support_subset_of_eq_outside
  intro j hj
  simp only [Finset.mem_singleton] at hj
  have hjv : j.val ≠ r₁ + r₂ - 1 := by
    intro h; apply hj; apply Fin.ext; exact h
  clear hj
  have hp : r₁ + r₂ - 1 + 1 = r₁ + r₂ := by omega
  have hup : r₁ + (r₂ - 1) + 1 = r₁ + r₂ := by omega
  have hu : (r₁ + r₂ ≤ j.val) ↔ (r₁ + (r₂ - 1) ≤ j.val) := by omega
  simp only [patternSign_threeBlockPattern, threeBlockRaw, first,
    Nat.mod_eq_of_lt j.isLt, if_pos j.isLt, halfValue]
  simp [hu]

theorem transfer23 {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m)
    (hgap : r₃ + 2 ≤ r₂) :
    0 < r₁ ∧ 0 < r₂ - 1 ∧ 0 < r₃ + 1 ∧
    r₁ + (r₂ - 1) + (r₃ + 1) = m ∧
    hamming (threeBlockPattern hm hpos hsum)
      (threeBlockPattern (r₁ := r₁) (r₂ := r₂ - 1) (r₃ := r₃ + 1) hm
        (by omega) (by omega)) ≤ 2 := by
  refine ⟨hpos.1, by omega, by omega, by omega, ?_⟩
  have h := hamming_le_card_of_support_subset _ _ _
    (transfer23_support hm hpos hsum hgap)
  calc
    _ ≤ 1 := by simpa using h
    _ ≤ 2 := by omega

private theorem transfer13_support {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m)
    (hgap : r₃ + 2 ≤ r₁) :
    changedSupport (threeBlockPattern hm hpos hsum)
      (threeBlockPattern (r₁ := r₁ - 1) (r₂ := r₂) (r₃ := r₃ + 1) hm
        (by omega) (by omega : (r₁ - 1) + r₂ + (r₃ + 1) = m)) ⊆
      {⟨r₁ - 1, by omega⟩, ⟨r₁ + r₂ - 1, by omega⟩} := by
  apply support_subset_of_eq_outside
  intro j hj
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
  have hjv₁ : j.val ≠ r₁ - 1 := by
    intro h; apply hj.1; apply Fin.ext; exact h
  have hjv₂ : j.val ≠ r₁ + r₂ - 1 := by
    intro h; apply hj.2; apply Fin.ext; exact h
  clear hj
  have hp₁ : r₁ - 1 + 1 = r₁ := by omega
  have hp₂ : r₁ + r₂ - 1 + 1 = r₁ + r₂ := by omega
  have hup : (r₁ - 1) + r₂ + 1 = r₁ + r₂ := by omega
  have hl : (j.val < r₁) ↔ (j.val < r₁ - 1) := by omega
  have hu : (r₁ + r₂ ≤ j.val) ↔ ((r₁ - 1) + r₂ ≤ j.val) := by omega
  simp only [patternSign_threeBlockPattern, threeBlockRaw, first,
    Nat.mod_eq_of_lt j.isLt, if_pos j.isLt, halfValue]
  simp [hl, hu]

theorem transfer13 {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m)
    (hgap : r₃ + 2 ≤ r₁) :
    0 < r₁ - 1 ∧ 0 < r₂ ∧ 0 < r₃ + 1 ∧
    (r₁ - 1) + r₂ + (r₃ + 1) = m ∧
    hamming (threeBlockPattern hm hpos hsum)
      (threeBlockPattern (r₁ := r₁ - 1) (r₂ := r₂) (r₃ := r₃ + 1) hm
        (by omega) (by omega)) ≤ 2 := by
  refine ⟨by omega, hpos.2.1, by omega, by omega, ?_⟩
  have h := hamming_le_card_of_support_subset _ _ _
    (transfer13_support hm hpos hsum hgap)
  exact h.trans (Finset.card_insert_le _ _)

private theorem transfer21_support {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m)
    (hgap : r₁ + 2 ≤ r₂) :
    changedSupport (threeBlockPattern hm hpos hsum)
      (threeBlockPattern (r₁ := r₁ + 1) (r₂ := r₂ - 1) (r₃ := r₃) hm
        (by omega) (by omega)) ⊆ {⟨r₁, by omega⟩} := by
  apply support_subset_of_eq_outside
  intro j hj
  simp only [Finset.mem_singleton] at hj
  have hjv : j.val ≠ r₁ := by intro h; apply hj; exact Fin.ext h
  have hl : (j.val < r₁) ↔ (j.val < r₁ + 1) := by omega
  have hu : r₁ + r₂ = (r₁ + 1) + (r₂ - 1) := by omega
  simp only [patternSign_threeBlockPattern, threeBlockRaw, first,
    Nat.mod_eq_of_lt j.isLt, if_pos j.isLt, halfValue]
  simp [hl, hu]

theorem transfer21 {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m)
    (hgap : r₁ + 2 ≤ r₂) :
    0 < r₁ + 1 ∧ 0 < r₂ - 1 ∧ 0 < r₃ ∧
    (r₁ + 1) + (r₂ - 1) + r₃ = m ∧
    hamming (threeBlockPattern hm hpos hsum)
      (threeBlockPattern (r₁ := r₁ + 1) (r₂ := r₂ - 1) (r₃ := r₃) hm
        (by omega) (by omega)) ≤ 2 := by
  refine ⟨by omega, by omega, hpos.2.2, by omega, ?_⟩
  have h := hamming_le_card_of_support_subset _ _ _
    (transfer21_support hm hpos hsum hgap)
  calc _ ≤ 1 := by simpa using h
       _ ≤ 2 := by omega

private theorem transfer32_support {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m)
    (hgap : r₂ + 2 ≤ r₃) :
    changedSupport (threeBlockPattern hm hpos hsum)
      (threeBlockPattern (r₁ := r₁) (r₂ := r₂ + 1) (r₃ := r₃ - 1) hm
        (by omega) (by omega)) ⊆ {⟨r₁ + r₂, by omega⟩} := by
  apply support_subset_of_eq_outside
  intro j hj
  simp only [Finset.mem_singleton] at hj
  have hjv : j.val ≠ r₁ + r₂ := by intro h; apply hj; exact Fin.ext h
  have hu : (r₁ + r₂ ≤ j.val) ↔ (r₁ + (r₂ + 1) ≤ j.val) := by omega
  simp only [patternSign_threeBlockPattern, threeBlockRaw, first,
    Nat.mod_eq_of_lt j.isLt, if_pos j.isLt, halfValue]
  simp [hu]

theorem transfer32 {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m)
    (hgap : r₂ + 2 ≤ r₃) :
    0 < r₁ ∧ 0 < r₂ + 1 ∧ 0 < r₃ - 1 ∧
    r₁ + (r₂ + 1) + (r₃ - 1) = m ∧
    hamming (threeBlockPattern hm hpos hsum)
      (threeBlockPattern (r₁ := r₁) (r₂ := r₂ + 1) (r₃ := r₃ - 1) hm
        (by omega) (by omega)) ≤ 2 := by
  refine ⟨hpos.1, by omega, by omega, by omega, ?_⟩
  have h := hamming_le_card_of_support_subset _ _ _
    (transfer32_support hm hpos hsum hgap)
  calc _ ≤ 1 := by simpa using h
       _ ≤ 2 := by omega

private theorem transfer31_support {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m)
    (hgap : r₁ + 2 ≤ r₃) :
    changedSupport (threeBlockPattern hm hpos hsum)
      (threeBlockPattern (r₁ := r₁ + 1) (r₂ := r₂) (r₃ := r₃ - 1) hm
        (by omega) (by omega)) ⊆ {⟨r₁, by omega⟩, ⟨r₁ + r₂, by omega⟩} := by
  apply support_subset_of_eq_outside
  intro j hj
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
  have hjv₁ : j.val ≠ r₁ := by intro h; apply hj.1; exact Fin.ext h
  have hjv₂ : j.val ≠ r₁ + r₂ := by intro h; apply hj.2; exact Fin.ext h
  have hl : (j.val < r₁) ↔ (j.val < r₁ + 1) := by omega
  have hu : (r₁ + r₂ ≤ j.val) ↔ ((r₁ + 1) + r₂ ≤ j.val) := by omega
  simp only [patternSign_threeBlockPattern, threeBlockRaw, first,
    Nat.mod_eq_of_lt j.isLt, if_pos j.isLt, halfValue]
  simp [hl, hu]

theorem transfer31 {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m)
    (hgap : r₁ + 2 ≤ r₃) :
    0 < r₁ + 1 ∧ 0 < r₂ ∧ 0 < r₃ - 1 ∧
    (r₁ + 1) + r₂ + (r₃ - 1) = m ∧
    hamming (threeBlockPattern hm hpos hsum)
      (threeBlockPattern (r₁ := r₁ + 1) (r₂ := r₂) (r₃ := r₃ - 1) hm
        (by omega) (by omega)) ≤ 2 := by
  refine ⟨by omega, hpos.2.1, by omega, by omega, ?_⟩
  have h := hamming_le_card_of_support_subset _ _ _
    (transfer31_support hm hpos hsum hgap)
  exact h.trans (Finset.card_insert_le _ _)

/-- A genuine word move and its quantitative three-block-value gain, for the
ordered transfer from block 1 to block 2. -/
theorem transfer12_with_value_gain {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m)
    (hgap : r₂ + 2 ≤ r₁) {C κ : ℝ} {g : ℤ → ℝ} {l u : ℤ}
    (hκ : 0 ≤ κ) (hconv : ∀ x, l < x → x < u → κ ≤ secondDifference g x)
    (hI₁ : (r₁ : ℤ) ∈ Icc l u) (hI₂ : (r₂ : ℤ) ∈ Icc l u)
    (hI₃ : (r₃ : ℤ) ∈ Icc l u) :
    hamming (threeBlockPattern hm hpos hsum)
        (threeBlockPattern (r₁ := r₁ - 1) (r₂ := r₂ + 1) (r₃ := r₃) hm
          (by omega) (by omega)) ≤ 2 ∧
      2 * κ ≤ threeBlockValue C g ((r₁ - 1 : ℕ) : ℤ) ((r₂ + 1 : ℕ) : ℤ) r₃ -
        threeBlockValue C g r₁ r₂ r₃ := by
  constructor
  · exact (transfer12 hm hpos hsum hgap).2.2.2.2
  · have hv := one_unit_transfer (C := C) (f := g) hκ hconv hI₁ hI₂ hI₃
      (by exact_mod_cast hgap)
    have hpred : ((r₁ - 1 : ℕ) : ℤ) = (r₁ : ℤ) - 1 := by omega
    have hsucc : ((r₂ + 1 : ℕ) : ℤ) = (r₂ : ℤ) + 1 := by omega
    simpa only [hpred, hsucc] using hv.2.2.2

theorem transfer21_with_value_gain {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m)
    (hgap : r₁ + 2 ≤ r₂) {C κ : ℝ} {g : ℤ → ℝ} {l u : ℤ}
    (hκ : 0 ≤ κ) (hconv : ∀ x, l < x → x < u → κ ≤ secondDifference g x)
    (hI₁ : (r₁ : ℤ) ∈ Icc l u) (hI₂ : (r₂ : ℤ) ∈ Icc l u)
    (hI₃ : (r₃ : ℤ) ∈ Icc l u) :
    hamming (threeBlockPattern hm hpos hsum)
        (threeBlockPattern (r₁ := r₁ + 1) (r₂ := r₂ - 1) (r₃ := r₃) hm
          (by omega) (by omega)) ≤ 2 ∧
      2 * κ ≤ threeBlockValue C g ((r₁ + 1 : ℕ) : ℤ) ((r₂ - 1 : ℕ) : ℤ) r₃ -
        threeBlockValue C g r₁ r₂ r₃ := by
  constructor
  · exact (transfer21 hm hpos hsum hgap).2.2.2.2
  · have hv := one_unit_transfer (C := C) (f := g) hκ hconv hI₂ hI₁ hI₃
      (by exact_mod_cast hgap)
    have hp : ((r₂ - 1 : ℕ) : ℤ) = (r₂ : ℤ) - 1 := by omega
    have hs : ((r₁ + 1 : ℕ) : ℤ) = (r₁ : ℤ) + 1 := by omega
    rw [hp, hs]
    dsimp only [threeBlockValue] at hv ⊢
    linarith [hv.2.2.2]

theorem transfer23_with_value_gain {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m)
    (hgap : r₃ + 2 ≤ r₂) {C κ : ℝ} {g : ℤ → ℝ} {l u : ℤ}
    (hκ : 0 ≤ κ) (hconv : ∀ x, l < x → x < u → κ ≤ secondDifference g x)
    (hI₁ : (r₁ : ℤ) ∈ Icc l u) (hI₂ : (r₂ : ℤ) ∈ Icc l u)
    (hI₃ : (r₃ : ℤ) ∈ Icc l u) :
    hamming (threeBlockPattern hm hpos hsum)
        (threeBlockPattern (r₁ := r₁) (r₂ := r₂ - 1) (r₃ := r₃ + 1) hm
          (by omega) (by omega)) ≤ 2 ∧
      2 * κ ≤ threeBlockValue C g r₁ ((r₂ - 1 : ℕ) : ℤ) ((r₃ + 1 : ℕ) : ℤ) -
        threeBlockValue C g r₁ r₂ r₃ := by
  constructor
  · exact (transfer23 hm hpos hsum hgap).2.2.2.2
  · have hv := one_unit_transfer (C := C) (f := g) hκ hconv hI₂ hI₃ hI₁
      (by exact_mod_cast hgap)
    have hp : ((r₂ - 1 : ℕ) : ℤ) = (r₂ : ℤ) - 1 := by omega
    have hs : ((r₃ + 1 : ℕ) : ℤ) = (r₃ : ℤ) + 1 := by omega
    rw [hp, hs]
    dsimp only [threeBlockValue] at hv ⊢
    linarith [hv.2.2.2]

theorem transfer32_with_value_gain {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m)
    (hgap : r₂ + 2 ≤ r₃) {C κ : ℝ} {g : ℤ → ℝ} {l u : ℤ}
    (hκ : 0 ≤ κ) (hconv : ∀ x, l < x → x < u → κ ≤ secondDifference g x)
    (hI₁ : (r₁ : ℤ) ∈ Icc l u) (hI₂ : (r₂ : ℤ) ∈ Icc l u)
    (hI₃ : (r₃ : ℤ) ∈ Icc l u) :
    hamming (threeBlockPattern hm hpos hsum)
        (threeBlockPattern (r₁ := r₁) (r₂ := r₂ + 1) (r₃ := r₃ - 1) hm
          (by omega) (by omega)) ≤ 2 ∧
      2 * κ ≤ threeBlockValue C g r₁ ((r₂ + 1 : ℕ) : ℤ) ((r₃ - 1 : ℕ) : ℤ) -
        threeBlockValue C g r₁ r₂ r₃ := by
  constructor
  · exact (transfer32 hm hpos hsum hgap).2.2.2.2
  · have hv := one_unit_transfer (C := C) (f := g) hκ hconv hI₃ hI₂ hI₁
      (by exact_mod_cast hgap)
    have hp : ((r₃ - 1 : ℕ) : ℤ) = (r₃ : ℤ) - 1 := by omega
    have hs : ((r₂ + 1 : ℕ) : ℤ) = (r₂ : ℤ) + 1 := by omega
    rw [hp, hs]
    dsimp only [threeBlockValue] at hv ⊢
    linarith [hv.2.2.2]

theorem transfer13_with_value_gain {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m)
    (hgap : r₃ + 2 ≤ r₁) {C κ : ℝ} {g : ℤ → ℝ} {l u : ℤ}
    (hκ : 0 ≤ κ) (hconv : ∀ x, l < x → x < u → κ ≤ secondDifference g x)
    (hI₁ : (r₁ : ℤ) ∈ Icc l u) (hI₂ : (r₂ : ℤ) ∈ Icc l u)
    (hI₃ : (r₃ : ℤ) ∈ Icc l u) :
    hamming (threeBlockPattern hm hpos hsum)
        (threeBlockPattern (r₁ := r₁ - 1) (r₂ := r₂) (r₃ := r₃ + 1) hm
          (by omega) (by omega)) ≤ 2 ∧
      2 * κ ≤ threeBlockValue C g ((r₁ - 1 : ℕ) : ℤ) r₂ ((r₃ + 1 : ℕ) : ℤ) -
        threeBlockValue C g r₁ r₂ r₃ := by
  constructor
  · exact (transfer13 hm hpos hsum hgap).2.2.2.2
  · have hv := one_unit_transfer (C := C) (f := g) hκ hconv hI₁ hI₃ hI₂
      (by exact_mod_cast hgap)
    have hp : ((r₁ - 1 : ℕ) : ℤ) = (r₁ : ℤ) - 1 := by omega
    have hs : ((r₃ + 1 : ℕ) : ℤ) = (r₃ : ℤ) + 1 := by omega
    rw [hp, hs]
    dsimp only [threeBlockValue] at hv ⊢
    linarith [hv.2.2.2]

theorem transfer31_with_value_gain {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m)
    (hgap : r₁ + 2 ≤ r₃) {C κ : ℝ} {g : ℤ → ℝ} {l u : ℤ}
    (hκ : 0 ≤ κ) (hconv : ∀ x, l < x → x < u → κ ≤ secondDifference g x)
    (hI₁ : (r₁ : ℤ) ∈ Icc l u) (hI₂ : (r₂ : ℤ) ∈ Icc l u)
    (hI₃ : (r₃ : ℤ) ∈ Icc l u) :
    hamming (threeBlockPattern hm hpos hsum)
        (threeBlockPattern (r₁ := r₁ + 1) (r₂ := r₂) (r₃ := r₃ - 1) hm
          (by omega) (by omega)) ≤ 2 ∧
      2 * κ ≤ threeBlockValue C g ((r₁ + 1 : ℕ) : ℤ) r₂ ((r₃ - 1 : ℕ) : ℤ) -
        threeBlockValue C g r₁ r₂ r₃ := by
  constructor
  · exact (transfer31 hm hpos hsum hgap).2.2.2.2
  · have hv := one_unit_transfer (C := C) (f := g) hκ hconv hI₃ hI₁ hI₂
      (by exact_mod_cast hgap)
    have hp : ((r₃ - 1 : ℕ) : ℤ) = (r₃ : ℤ) - 1 := by omega
    have hs : ((r₁ + 1 : ℕ) : ℤ) = (r₁ : ℤ) + 1 := by omega
    rw [hp, hs]
    dsimp only [threeBlockValue] at hv ⊢
    linarith [hv.2.2.2]

/-- Any pair of block lengths separated by at least two admits a genuine
two-site word move with the quantitative convexity gain. -/
theorem exists_balancing_transfer_with_value_gain {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m)
    (hgap : r₂ + 2 ≤ r₁ ∨ r₁ + 2 ≤ r₂ ∨ r₃ + 2 ≤ r₂ ∨
      r₂ + 2 ≤ r₃ ∨ r₃ + 2 ≤ r₁ ∨ r₁ + 2 ≤ r₃)
    {C κ : ℝ} {g : ℤ → ℝ} {l u : ℤ}
    (hκ : 0 ≤ κ) (hconv : ∀ x, l < x → x < u → κ ≤ secondDifference g x)
    (hI₁ : (r₁ : ℤ) ∈ Icc l u) (hI₂ : (r₂ : ℤ) ∈ Icc l u)
    (hI₃ : (r₃ : ℤ) ∈ Icc l u) :
    ∃ s₁ s₂ s₃ : ℕ, ∃ hspos : 0 < s₁ ∧ 0 < s₂ ∧ 0 < s₃,
      ∃ hssum : s₁ + s₂ + s₃ = m,
        hamming (threeBlockPattern hm hpos hsum)
          (threeBlockPattern hm hspos hssum) ≤ 2 ∧
        2 * κ ≤ threeBlockValue C g s₁ s₂ s₃ - threeBlockValue C g r₁ r₂ r₃ := by
  rcases hgap with h12 | h21 | h23 | h32 | h13 | h31
  · refine ⟨r₁ - 1, r₂ + 1, r₃, by omega, by omega, ?_⟩
    exact transfer12_with_value_gain hm hpos hsum h12 hκ hconv hI₁ hI₂ hI₃
  · refine ⟨r₁ + 1, r₂ - 1, r₃, by omega, by omega, ?_⟩
    exact transfer21_with_value_gain hm hpos hsum h21 hκ hconv hI₁ hI₂ hI₃
  · refine ⟨r₁, r₂ - 1, r₃ + 1, by omega, by omega, ?_⟩
    exact transfer23_with_value_gain hm hpos hsum h23 hκ hconv hI₁ hI₂ hI₃
  · refine ⟨r₁, r₂ + 1, r₃ - 1, by omega, by omega, ?_⟩
    exact transfer32_with_value_gain hm hpos hsum h32 hκ hconv hI₁ hI₂ hI₃
  · refine ⟨r₁ - 1, r₂, r₃ + 1, by omega, by omega, ?_⟩
    exact transfer13_with_value_gain hm hpos hsum h13 hκ hconv hI₁ hI₂ hI₃
  · refine ⟨r₁ + 1, r₂, r₃ - 1, by omega, by omega, ?_⟩
    exact transfer31_with_value_gain hm hpos hsum h31 hκ hconv hI₁ hI₂ hI₃

/-- Exhaustion of the six ordered pairs, matching the six transfer endpoints above. -/
theorem arbitrary_pair_cases (a b : Fin 3) (hab : a ≠ b) :
    (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 1 ∧ b = 2) ∨
    (a = 2 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) := by
  fin_cases a <;> fin_cases b <;> omega

end
end StructuralNote.SolThreeBlockTransfer
