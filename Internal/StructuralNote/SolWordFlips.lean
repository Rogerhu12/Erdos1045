import StructuralNote.SolWordHamming

namespace StructuralNote.SolWordFlips

open Erdos1045.EventualExact.FiniteBox Erdos1045.EventualExact.FourierMultiplier
open Erdos1045.EventualExact
open StructuralNote.SolWordHamming
noncomputable section

def flipRaw {m : ℕ} {hm : 0 < m} (s : SignPattern hm) (i : Fin m)
    (j : Fin (2 * m)) : ℝ :=
  if j.val % m = i.val then -patternSign s j else patternSign s j

theorem halfTurn_mod {m : ℕ} (hm : 0 < m) (j : Fin (2 * m)) :
    (halfTurn hm j).val % m = j.val % m := by
  simp only [halfTurn]
  rw [Nat.mod_mod_of_dvd _ (by exact ⟨2, by omega⟩ : m ∣ 2 * m)]
  simp

theorem flipRaw_is_sign {m : ℕ} {hm : 0 < m} (s : SignPattern hm) (i : Fin m) :
    IsSignVector (flipRaw s i) := by
  intro j
  unfold flipRaw
  split <;> rcases patternSign_is_sign s j with h | h <;> simp [h]

theorem flipRaw_antiperiodic {m : ℕ} {hm : 0 < m} (s : SignPattern hm) (i : Fin m) :
    Antiperiodic hm (flipRaw s i) := by
  intro j
  unfold flipRaw
  rw [halfTurn_mod]
  split <;> rw [patternSign_antiperiodic]

def flip {m : ℕ} {hm : 0 < m} (s : SignPattern hm) (i : Fin m) : SignPattern hm :=
  encodeSign (flipRaw s i) (flipRaw_is_sign s i) (flipRaw_antiperiodic s i)

@[simp] theorem patternSign_flip {m : ℕ} {hm : 0 < m} (s : SignPattern hm)
    (i : Fin m) (j : Fin (2 * m)) :
    patternSign (flip s i) j =
      if j.val % m = i.val then -patternSign s j else patternSign s j := by
  rw [flip, patternSign_encodeSign]
  rfl

def flipTwo {m : ℕ} {hm : 0 < m} (s : SignPattern hm) (i k : Fin m) : SignPattern hm :=
  flip (flip s i) k

theorem changedSupport_flip_subset {m : ℕ} {hm : 0 < m} (s : SignPattern hm) (i : Fin m) :
    changedSupport s (flip s i) ⊆ {i} := by
  intro j hj
  simp only [changedSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton] at hj ⊢
  rw [patternSign_flip] at hj
  by_contra hji
  have hmod : (first j).val % m ≠ i.val := by
    simp only [first, Nat.mod_eq_of_lt j.isLt]
    exact fun h => hji (Fin.ext h)
  simp [hmod] at hj

theorem hamming_flip_le_one {m : ℕ} {hm : 0 < m} (s : SignPattern hm) (i : Fin m) :
    hamming s (flip s i) ≤ 1 := by
  have h := hamming_le_card_of_support_subset s (flip s i) {i} (changedSupport_flip_subset s i)
  simpa using h

theorem changedSupport_flipTwo_subset {m : ℕ} {hm : 0 < m}
    (s : SignPattern hm) (i k : Fin m) : changedSupport s (flipTwo s i k) ⊆ {i, k} := by
  intro j hj
  simp only [changedSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton] at hj ⊢
  by_contra h
  push Not at h
  have hi : (first j).val % m ≠ i.val := by
    simp only [first, Nat.mod_eq_of_lt j.isLt]
    exact fun e => h.1 (Fin.ext e)
  have hk : (first j).val % m ≠ k.val := by
    simp only [first, Nat.mod_eq_of_lt j.isLt]
    exact fun e => h.2 (Fin.ext e)
  simp [flipTwo, patternSign_flip, hi, hk] at hj

theorem hamming_flipTwo_le_two {m : ℕ} {hm : 0 < m}
    (s : SignPattern hm) (i k : Fin m) : hamming s (flipTwo s i k) ≤ 2 := by
  have h := hamming_le_card_of_support_subset s (flipTwo s i k) {i, k}
    (changedSupport_flipTwo_subset s i k)
  exact h.trans (Finset.card_insert_le i {k})

theorem flip_vertex_antiperiodic {m : ℕ} {hm : 0 < m} (A : ℝ)
    (s : SignPattern hm) (i : Fin m) : Antiperiodic hm (vertex A (flip s i)) :=
  by
    intro j
    change A * patternSign (flip s i) (halfTurn hm j) = -(A * patternSign (flip s i) j)
    rw [patternSign_antiperiodic, mul_neg]

theorem flipTwo_vertex_antiperiodic {m : ℕ} {hm : 0 < m} (A : ℝ)
    (s : SignPattern hm) (i k : Fin m) : Antiperiodic hm (vertex A (flipTwo s i k)) :=
  by
    intro j
    change A * patternSign (flipTwo s i k) (halfTurn hm j) =
      -(A * patternSign (flipTwo s i k) j)
    rw [patternSign_antiperiodic, mul_neg]

end
end StructuralNote.SolWordFlips
