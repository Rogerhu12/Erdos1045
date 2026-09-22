import StructuralNote.SolWordFlips

namespace StructuralNote.SolThreeBlockWord

open Erdos1045.EventualExact Erdos1045.EventualExact.FiniteBox
open Erdos1045.EventualExact.FourierMultiplier StructuralNote.SolWordFlips
noncomputable section

def halfValue (r₁ r₂ x : ℕ) : ℝ := if x < r₁ ∨ r₁ + r₂ ≤ x then 1 else -1

def threeBlockRaw {m : ℕ} (r₁ r₂ : ℕ) (j : Fin (2 * m)) : ℝ :=
  if j.val < m then halfValue r₁ r₂ (j.val % m)
  else -halfValue r₁ r₂ (j.val % m)

theorem threeBlockRaw_is_sign {m r₁ r₂ : ℕ} :
    IsSignVector (threeBlockRaw (m := m) r₁ r₂) := by
  intro j
  unfold threeBlockRaw halfValue
  split <;> split <;> simp

theorem threeBlockRaw_antiperiodic {m r₁ r₂ : ℕ} (hm : 0 < m) :
    Antiperiodic hm (threeBlockRaw (m := m) r₁ r₂) := by
  intro j
  unfold threeBlockRaw
  rw [StructuralNote.SolWordFlips.halfTurn_mod]
  by_cases hj : j.val < m
  · have hh : ¬(halfTurn hm j).val < m := by
      simpa using (halfTurn_lt_iff hm j).not.mpr (not_not.mpr hj)
    simp [hj, hh]
  · have hh : (halfTurn hm j).val < m := (halfTurn_lt_iff hm j).2 hj
    simp [hj, hh]

def threeBlockPattern {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (_hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (_hsum : r₁ + r₂ + r₃ = m) : SignPattern hm :=
  encodeSign (threeBlockRaw (m := m) r₁ r₂) threeBlockRaw_is_sign
    (threeBlockRaw_antiperiodic hm)

@[simp] theorem patternSign_threeBlockPattern {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m)
    (j : Fin (2 * m)) :
    patternSign (threeBlockPattern hm hpos hsum) j = threeBlockRaw (m := m) r₁ r₂ j := by
  rw [threeBlockPattern, patternSign_encodeSign]

def threeBlockVertex {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m) (A : ℝ) :
    Fin (2 * m) → ℝ := vertex A (threeBlockPattern hm hpos hsum)

theorem threeBlockVertex_antiperiodic {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m) (A : ℝ) :
    Antiperiodic hm (threeBlockVertex hm hpos hsum A) := by
  intro j
  change A * patternSign (threeBlockPattern hm hpos hsum) (halfTurn hm j) =
    -(A * patternSign (threeBlockPattern hm hpos hsum) j)
  rw [patternSign_antiperiodic, mul_neg]

theorem three_half_period_jumps {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m) :
    let s := threeBlockPattern hm hpos hsum
    patternSign s ⟨r₁ - 1, by omega⟩ = 1 ∧
    patternSign s ⟨r₁, by omega⟩ = -1 ∧
    patternSign s ⟨r₁ + r₂ - 1, by omega⟩ = -1 ∧
    patternSign s ⟨r₁ + r₂, by omega⟩ = 1 ∧
    patternSign s ⟨m - 1, by omega⟩ = 1 ∧
    patternSign s (halfTurn hm ⟨0, by omega⟩) = -1 := by
  rcases hpos with ⟨h₁, h₂, h₃⟩
  have e₁ : (r₁ - 1) % m = r₁ - 1 := Nat.mod_eq_of_lt (by omega)
  have e₂ : r₁ % m = r₁ := Nat.mod_eq_of_lt (by omega)
  have e₃ : (r₁ + r₂ - 1) % m = r₁ + r₂ - 1 := Nat.mod_eq_of_lt (by omega)
  have e₄ : (r₁ + r₂) % m = r₁ + r₂ := Nat.mod_eq_of_lt (by omega)
  have e₅ : (m - 1) % m = m - 1 := Nat.mod_eq_of_lt (by omega)
  have e₆ : m % (2 * m) = m := Nat.mod_eq_of_lt (by omega)
  dsimp
  simp only [patternSign_threeBlockPattern, threeBlockRaw, halfValue, halfTurn]
  simp only [Nat.zero_add]
  rw [e₁, e₂, e₃, e₄, e₅, e₆, Nat.mod_self]
  repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
  norm_num

end
end StructuralNote.SolThreeBlockWord
