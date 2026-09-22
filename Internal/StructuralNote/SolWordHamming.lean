import EventualExact.FiniteBoxMaximum

namespace StructuralNote.SolWordHamming

open Erdos1045.EventualExact.FiniteBox Erdos1045.EventualExact.FourierMultiplier
noncomputable section

def first {m : ℕ} (i : Fin m) : Fin (2 * m) := ⟨i, by omega⟩

def hamming {m : ℕ} {hm : 0 < m} (s t : SignPattern hm) : ℕ :=
  Finset.univ.filter (fun i : Fin m => patternSign s (first i) ≠ patternSign t (first i)) |>.card

def changedSupport {m : ℕ} {hm : 0 < m} (s t : SignPattern hm) : Finset (Fin m) :=
  Finset.univ.filter (fun i => patternSign s (first i) ≠ patternSign t (first i))

@[simp] theorem hamming_eq_card_changedSupport {m : ℕ} {hm : 0 < m}
    (s t : SignPattern hm) : hamming s t = (changedSupport s t).card := rfl

theorem hamming_le_card_of_support_subset {m : ℕ} {hm : 0 < m}
    (s t : SignPattern hm) (E : Finset (Fin m)) (hE : changedSupport s t ⊆ E) :
    hamming s t ≤ E.card := by
  simpa using Finset.card_le_card hE

theorem card_le_hamming_of_subset_support {m : ℕ} {hm : 0 < m}
    (s t : SignPattern hm) (E : Finset (Fin m)) (hE : E ⊆ changedSupport s t) :
    E.card ≤ hamming s t := by
  simpa using Finset.card_le_card hE

theorem hamming_symm {m : ℕ} {hm : 0 < m} (s t : SignPattern hm) :
    hamming s t = hamming t s := by
  simp only [hamming]
  congr 1
  ext i
  simp [ne_comm]

theorem hamming_eq_zero_iff {m : ℕ} {hm : 0 < m} (s t : SignPattern hm) :
    hamming s t = 0 ↔ s = t := by
  classical
  constructor
  · intro h
    have heq : ∀ i : Fin m, patternSign s (first i) = patternSign t (first i) := by
      intro i
      by_contra hn
      have : i ∈ Finset.univ.filter
          (fun j : Fin m => patternSign s (first j) ≠ patternSign t (first j)) := by simp [hn]
      have hp := Finset.card_pos.mpr ⟨i, this⟩
      change (Finset.univ.filter
        (fun j : Fin m => patternSign s (first j) ≠ patternSign t (first j))).card = 0 at h
      omega
    have hall : patternSign s = patternSign t := by
      funext i
      by_cases hi : i.val < m
      · simpa [first] using heq ⟨i.val, hi⟩
      · let j := halfTurn hm i
        have hj : j.val < m := (halfTurn_lt_iff hm i).2 hi
        have e := heq ⟨j.val, hj⟩
        have hs := patternSign_antiperiodic s i
        have ht := patternSign_antiperiodic t i
        change patternSign s i = patternSign t i
        change patternSign s j = patternSign t j at e
        linarith
    apply Subtype.ext
    funext i
    have e := congrFun hall i
    change boolSign (s.val i) = boolSign (t.val i) at e
    cases hsi : s.val i <;> cases hti : t.val i <;>
      simp [boolSign, hsi, hti] at e ⊢ <;> linarith
  · rintro rfl; simp [hamming]

theorem hamming_triangle {m : ℕ} {hm : 0 < m} (s t u : SignPattern hm) :
    hamming s u ≤ hamming s t + hamming t u := by
  classical
  let A := Finset.univ.filter (fun i : Fin m => patternSign s (first i) ≠ patternSign t (first i))
  let B := Finset.univ.filter (fun i : Fin m => patternSign t (first i) ≠ patternSign u (first i))
  let C := Finset.univ.filter (fun i : Fin m => patternSign s (first i) ≠ patternSign u (first i))
  have hsub : C ⊆ A ∪ B := by
    intro i hi
    simp only [C, A, B, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hi ⊢
    by_cases h : patternSign s (first i) = patternSign t (first i)
    · exact Or.inr (by simpa [h] using hi)
    · exact Or.inl h
  have hc := Finset.card_le_card hsub
  have hu := Finset.card_union_le A B
  simpa only [hamming, A, B, C] using hc.trans hu

end
end StructuralNote.SolWordHamming
