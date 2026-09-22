import StructuralNote.SolWordFlips
import Mathlib.Logic.Equiv.Fin.Rotate
import EventualExact.SchurLift

/-! Symmetries of the finite antiperiodic sign-pattern space.

The Hamming distance in `SolWordHamming` is recorded on one representative
of each half-turn orbit.  The auxiliary full support below makes this orbit
quotient explicit, so that arbitrary grid permutations commuting with the
half-turn preserve the stated Hamming distance.
-/

namespace StructuralNote.SignPatternSymmetry

open Finset
open Erdos1045.EventualExact
open Erdos1045.EventualExact.FiniteBox
open Erdos1045.EventualExact.FourierMultiplier
open StructuralNote.SolWordHamming
noncomputable section

def halfTurnCommuting {m : ℕ} (hm : 0 < m) (e : Equiv.Perm (Fin (2 * m))) : Prop :=
  ∀ j, e (halfTurn hm j) = halfTurn hm (e j)

def reindexRaw {m : ℕ} {hm : 0 < m} (e : Equiv.Perm (Fin (2 * m)))
    (s : SignPattern hm) : Fin (2 * m) → Bool :=
  fun j => s.val (e j)

theorem reindexRaw_antiperiodic {m : ℕ} {hm : 0 < m}
    (e : Equiv.Perm (Fin (2 * m))) (he : halfTurnCommuting hm e) (s : SignPattern hm) :
    Antiperiodic hm (fun j => boolSign (reindexRaw e s j)) := by
  intro j
  change boolSign (s.val (e (halfTurn hm j))) = -boolSign (s.val (e j))
  rw [he j]
  exact s.property (e j)

def reindex {m : ℕ} {hm : 0 < m} (e : Equiv.Perm (Fin (2 * m)))
    (he : halfTurnCommuting hm e) (s : SignPattern hm) : SignPattern hm :=
  ⟨reindexRaw e s, reindexRaw_antiperiodic e he s⟩

@[simp] theorem patternSign_reindex {m : ℕ} {hm : 0 < m}
    (e : Equiv.Perm (Fin (2 * m))) (he : halfTurnCommuting hm e) (s : SignPattern hm)
    (j : Fin (2 * m)) :
    patternSign (reindex e he s) j = patternSign s (e j) := rfl

theorem halfTurnCommuting_symm {m : ℕ} {hm : 0 < m}
    {e : Equiv.Perm (Fin (2 * m))} (he : halfTurnCommuting hm e) :
    halfTurnCommuting hm e.symm := by
  intro j
  apply e.injective
  rw [e.apply_symm_apply, he, e.apply_symm_apply]

theorem reindex_refl {m : ℕ} {hm : 0 < m} (s : SignPattern hm) :
    reindex (Equiv.refl (Fin (2 * m))) (by intro j; rfl) s = s := by
  apply Subtype.ext
  rfl

theorem reindex_inverse {m : ℕ} {hm : 0 < m}
    (e : Equiv.Perm (Fin (2 * m))) (he : halfTurnCommuting hm e) (s : SignPattern hm) :
    reindex e he (reindex e.symm (halfTurnCommuting_symm he) s) = s := by
  apply Subtype.ext
  funext j
  simp [reindex, reindexRaw]

def globalNegate {m : ℕ} {hm : 0 < m} (s : SignPattern hm) : SignPattern hm :=
  ⟨fun j => !(s.val j), by
    intro j
    have hnot (b : Bool) : boolSign (!b) = -boolSign b := by
      cases b <;> simp [boolSign]
    change boolSign (!(s.val (halfTurn hm j))) = -boolSign (!(s.val j))
    rw [hnot, hnot]
    have hs := s.property j
    change boolSign (s.val (halfTurn hm j)) = -boolSign (s.val j) at hs
    rw [hs]
  ⟩

@[simp] theorem patternSign_globalNegate {m : ℕ} {hm : 0 < m}
    (s : SignPattern hm) (j : Fin (2 * m)) :
    patternSign (globalNegate s) j = -patternSign s j := by
  change boolSign (!(s.val j)) = -boolSign (s.val j)
  cases s.val j <;> simp [boolSign]

theorem globalNegate_involutive {m : ℕ} {hm : 0 < m} (s : SignPattern hm) :
    globalNegate (globalNegate s) = s := by
  apply Subtype.ext
  funext j
  cases h : s.val j <;> simp [globalNegate, h]

theorem hamming_globalNegate {m : ℕ} {hm : 0 < m}
    (s t : SignPattern hm) :
    hamming (globalNegate s) (globalNegate t) = hamming s t := by
  unfold hamming
  congr 1
  ext i
  simp [patternSign_globalNegate]

theorem patternDiff_halfTurn_iff {m : ℕ} {hm : 0 < m}
    (s t : SignPattern hm) (j : Fin (2 * m)) :
    (patternSign s (halfTurn hm j) ≠ patternSign t (halfTurn hm j)) ↔
      (patternSign s j ≠ patternSign t j) := by
  rw [patternSign_antiperiodic s j, patternSign_antiperiodic t j]
  constructor
  · intro h heq
    apply h
    linarith
  · intro h heq
    apply h
    linarith

def fullChangedSupport {m : ℕ} {hm : 0 < m} (s t : SignPattern hm) :
    Finset (Fin (2 * m)) :=
  Finset.univ.filter (fun j => patternSign s j ≠ patternSign t j)

theorem fullChangedSupport_eq_union {m : ℕ} {hm : 0 < m} (s t : SignPattern hm) :
    fullChangedSupport s t =
      (changedSupport s t).image first ∪
        (changedSupport s t).image (fun i => halfTurn hm (first i)) := by
  classical
  ext j
  by_cases hj : j.val < m
  · let i : Fin m := ⟨j.val, hj⟩
    have hfirst : first i = j := by
      apply Fin.ext
      rfl
    have hmem : j ∈ fullChangedSupport s t ↔ i ∈ changedSupport s t := by
      simp only [fullChangedSupport, changedSupport, mem_filter, mem_univ, true_and]
      rw [hfirst]
    have hupper : j ∉ (changedSupport s t).image (fun i => halfTurn hm (first i)) := by
      intro h
      obtain ⟨k, hk, hkj⟩ := mem_image.mp h
      have hnot : ¬(halfTurn hm (first k)).val < m :=
        (halfTurn_lt_iff hm (first k)).not.mpr (by simp [first])
      exact hnot (by simpa [hkj] using hj)
    have hlowmem : j ∈ (changedSupport s t).image first ↔ i ∈ changedSupport s t := by
      constructor
      · intro h
        obtain ⟨k, hk, hkj⟩ := mem_image.mp h
        have hki : k = i := by
          exact Fin.ext (congrArg (fun x : Fin (2 * m) => x.val) (hkj.trans hfirst.symm))
        simpa [hki] using hk
      · intro hi
        exact mem_image.mpr ⟨i, hi, hfirst⟩
    rw [hmem, mem_union, hlowmem]
    constructor
    · intro hi
      exact Or.inl hi
    · intro h
      rcases h with hi | hj
      · exact hi
      · exact False.elim (hupper hj)
  · let i : Fin m := ⟨(halfTurn hm j).val, (halfTurn_lt_iff hm j).2 hj⟩
    have hhalf : halfTurn hm (first i) = j := by
      have hi : first i = halfTurn hm j := by
        exact Fin.ext rfl
      rw [hi, SchurLift.halfTurn_involutive hm j]
    have hmem : j ∈ fullChangedSupport s t ↔ i ∈ changedSupport s t := by
      simp only [fullChangedSupport, changedSupport, mem_filter, mem_univ, true_and]
      rw [← hhalf, patternDiff_halfTurn_iff]
    have hlower : j ∉ (changedSupport s t).image first := by
      intro h
      obtain ⟨k, hk, hkj⟩ := mem_image.mp h
      have hsmall : (first k).val < m := by simp [first]
      exact hj (by simpa [hkj] using hsmall)
    have huppermem : j ∈ (changedSupport s t).image
        (fun i => halfTurn hm (first i)) ↔ i ∈ changedSupport s t := by
      constructor
      · intro h
        obtain ⟨k, hk, hkj⟩ := mem_image.mp h
        have hki : k = i := by
          have hh := congrArg (halfTurn hm) (hkj.trans hhalf.symm)
          rw [SchurLift.halfTurn_involutive hm (first k),
            SchurLift.halfTurn_involutive hm (first i)] at hh
          exact Fin.ext (congrArg (fun x : Fin (2 * m) => x.val) hh)
        simpa [hki] using hk
      · intro hi
        exact mem_image.mpr ⟨i, hi, hhalf⟩
    rw [hmem, mem_union, huppermem]
    constructor
    · intro hi
      exact Or.inr hi
    · intro h
      rcases h with hj | hi
      · exact False.elim (hlower hj)
      · exact hi

theorem fullChangedSupport_card {m : ℕ} {hm : 0 < m} (s t : SignPattern hm) :
    (fullChangedSupport s t).card = 2 * hamming s t := by
  classical
  rw [fullChangedSupport_eq_union]
  have hfirst_inj : Function.Injective (first (m := m)) := by
    intro i k hik
    exact Fin.ext (congrArg (fun x : Fin (2 * m) => x.val) hik)
  have hhalf_inj : Function.Injective (fun i : Fin m => halfTurn hm (first i)) := by
    intro i k hik
    apply hfirst_inj
    have hh := congrArg (halfTurn hm) hik
    rw [SchurLift.halfTurn_involutive hm (first i),
      SchurLift.halfTurn_involutive hm (first k)] at hh
    exact hh
  have hdisj : Disjoint ((changedSupport s t).image first)
      ((changedSupport s t).image (fun i => halfTurn hm (first i))) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp hj
    obtain ⟨k, hk', hkj⟩ := Finset.mem_image.mp hk
    have hsmall : (first i).val < m := by simp [first]
    have hlarge : (halfTurn hm (first k)).val ≥ m := by
      exact le_of_not_gt ((halfTurn_lt_iff hm (first k)).not.mpr (by simp [first]))
    have : (first i).val = (halfTurn hm (first k)).val := by
      exact congrArg (fun x : Fin (2 * m) => x.val) (hij.trans hkj.symm)
    omega
  rw [card_union_of_disjoint hdisj, card_image_of_injective _ hfirst_inj,
    card_image_of_injective _ hhalf_inj, ← hamming_eq_card_changedSupport]
  omega

theorem fullChangedSupport_card_reindex {m : ℕ} {hm : 0 < m}
    (e : Equiv.Perm (Fin (2 * m))) (he : halfTurnCommuting hm e)
    (s t : SignPattern hm) :
    (fullChangedSupport (reindex e he s) (reindex e he t)).card =
      (fullChangedSupport s t).card := by
  classical
  unfold fullChangedSupport
  let p : Fin (2 * m) → Prop := fun j =>
    patternSign s j ≠ patternSign t j
  have hfilter :
      (Finset.univ.filter (p ∘ e)).map e.toEmbedding = Finset.univ.filter p := by
    rw [Finset.map_filter]
    simp [p, Function.comp_def]
  change (Finset.univ.filter (p ∘ e)).card = (Finset.univ.filter p).card
  rw [← hfilter, Finset.card_map]

theorem hamming_reindex {m : ℕ} {hm : 0 < m}
    (e : Equiv.Perm (Fin (2 * m))) (he : halfTurnCommuting hm e)
    (s t : SignPattern hm) :
    hamming (reindex e he s) (reindex e he t) = hamming s t := by
  have h₁ := fullChangedSupport_card (reindex e he s) (reindex e he t)
  have h₂ := fullChangedSupport_card s t
  have h₃ := fullChangedSupport_card_reindex e he s t
  omega

theorem halfTurnCommuting_finRotate {m : ℕ} (hm : 0 < m) :
    halfTurnCommuting hm (finRotate (2 * m)) := by
  let : NeZero (2 * m) := ⟨by omega⟩
  intro j
  apply Fin.ext
  simp only [halfTurn, Fin.val_add, Fin.val_one', finRotate_apply]
  rw [Nat.mod_add_mod, Nat.mod_add_mod]
  congr 1
  omega

theorem halfTurnCommuting_finRotate_pow {m : ℕ} (hm : 0 < m) (k : ℕ) :
    halfTurnCommuting hm ((finRotate (2 * m)) ^ k) := by
  induction k with
  | zero =>
      intro j
      rfl
  | succ k ih =>
      intro j
      rw [pow_succ]
      change ((finRotate (2 * m)) ^ k) (finRotate (2 * m) (halfTurn hm j)) =
        halfTurn hm (((finRotate (2 * m)) ^ k) (finRotate (2 * m) j))
      rw [halfTurnCommuting_finRotate hm]
      rw [ih]

def rotatePattern {m : ℕ} {hm : 0 < m} (k : ℕ) (s : SignPattern hm) :
    SignPattern hm :=
  reindex ((finRotate (2 * m)) ^ k) (halfTurnCommuting_finRotate_pow hm k) s

@[simp] theorem patternSign_rotatePattern {m : ℕ} {hm : 0 < m}
    (k : ℕ) (s : SignPattern hm) (j : Fin (2 * m)) :
    patternSign (rotatePattern k s) j = patternSign s (((finRotate (2 * m)) ^ k) j) :=
  patternSign_reindex _ _ _ _

theorem hamming_rotatePattern {m : ℕ} {hm : 0 < m} (k : ℕ)
    (s t : SignPattern hm) :
    hamming (rotatePattern k s) (rotatePattern k t) = hamming s t := by
  exact hamming_reindex _ _ _ _

end
end StructuralNote.SignPatternSymmetry
