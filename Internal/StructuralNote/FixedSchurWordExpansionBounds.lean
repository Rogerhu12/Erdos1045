import StructuralNote.FixedSchurQuadraticExpansion
import StructuralNote.FixedSchurPairingBounds
import StructuralNote.FixedSchurWordPotential

/-! The scalar comparison budget after an actual normal-coordinate expansion.
The normal-error estimates remain explicit inputs here; this module does not
assert that every maximizer has entered the fixed-Schur chart. -/

namespace StructuralNote.FixedSchurWordExpansionBounds

open Erdos1045.EventualExact FourierMultiplier SchurLiftBounds FiniteBox
open FixedSchurQuadraticExpansion FixedSchurPairingBounds FixedSchurWordPotential
open FixedSchurDomainSmallness SolWordHamming
open scoped BigOperators

noncomputable section

theorem quadratic_budget {n : ℕ} (hn : 0 < n) (heven : Even n)
    (σ η e : Fin n → ℝ) (hσ : ∀ j, σ j = 1 ∨ σ j = -1)
    {K E : ℝ} (hη : meanSquare η ≤ K / (n : ℝ) ^ 5)
    (he : meanSquare e ≤ E ^ 2 / (n : ℝ) ^ 4) :
    |normalizedBoxEnergy (operator n) (angularField σ η + e)| ≤
      K / (8 * (n : ℝ) ^ 3) + E ^ 2 / (2 * (n : ℝ) ^ 4) := by
  apply (quadratic_error_le hn heven σ η e hσ).trans
  calc
    _ ≤ (n : ℝ) ^ 2 / 8 * (K / (n : ℝ) ^ 5) +
        (E ^ 2 / (n : ℝ) ^ 4) / 2 := by gcongr
    _ = _ := by
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp

theorem error_pairing_budget {m : ℕ} (hm : 2048 ≤ 2 * m)
    (s t : SignPattern (by omega)) (e e' : Fin (2 * m) → ℝ)
    {E D S : ℝ} (hE : 0 ≤ E) (hS : 0 ≤ S)
    (hd : (hamming s t : ℝ) ≤ S)
    (he : meanSquare e ≤ E ^ 2 / (2 * m : ℝ) ^ 4)
    (hed : (∑ j, |e j - e' j|) / (2 * m : ℝ) ≤ D / (2 * m : ℝ) ^ 3) :
    |finitePairing (operator (2 * m) (baseWord (patternSign s))) e / (2 * m : ℝ) -
      finitePairing (operator (2 * m) (baseWord (patternSign t))) e' / (2 * m : ℝ)| ≤
        (12 * S * E + 3 * D) / (2 * m : ℝ) ^ 3 := by
  have he2 : Real.sqrt (meanSquare e) ≤ E / (2 * m : ℝ) ^ 2 := by
    apply (Real.sqrt_le_iff).2
    refine ⟨by positivity, he.trans_eq ?_⟩
    ring
  have hg := potential_l2_difference hm s t
  have hg' : Real.sqrt (meanSquare (operator (2 * m) (baseWord (patternSign s)) -
      operator (2 * m) (baseWord (patternSign t)))) ≤ 12 * S / (2 * m : ℝ) :=
    hg.trans (by gcongr)
  have hp := error_pairing_difference_le (show 0 < 2 * m by omega)
    (operator (2 * m) (baseWord (patternSign s)))
    (operator (2 * m) (baseWord (patternSign t))) e e' (potential_abs_le_three hm t)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hp
  apply hp.trans
  calc
    _ ≤ (12 * S / (2 * m : ℝ)) * (E / (2 * m : ℝ) ^ 2) +
        3 * (D / (2 * m : ℝ) ^ 3) := by
      apply add_le_add (mul_le_mul hg' he2 (Real.sqrt_nonneg _) (by positivity))
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hed (by norm_num : (0 : ℝ) ≤ 3)
    _ = _ := by ring

theorem scalar_word_comparison {m : ℕ} (hm : 2048 ≤ 2 * m)
    (s t : SignPattern (by omega)) (η e e' : Fin (2 * m) → ℝ)
    {K E D S : ℝ} (hE : 0 ≤ E) (hS : 0 ≤ S)
    (hd : (hamming s t : ℝ) ≤ S)
    (hη : meanSquare η ≤ K / (2 * m : ℝ) ^ 5)
    (he : meanSquare e ≤ E ^ 2 / (2 * m : ℝ) ^ 4)
    (he' : meanSquare e' ≤ E ^ 2 / (2 * m : ℝ) ^ 4)
    (hed : (∑ j, |e j - e' j|) / (2 * m : ℝ) ≤ D / (2 * m : ℝ) ^ 3) :
    |(normalizedBoxEnergy (operator (2 * m))
          (baseWord (patternSign s) + angularField (patternSign s) η + e) -
        normalizedBoxEnergy (operator (2 * m))
          (baseWord (patternSign t) + angularField (patternSign t) η + e')) -
      (normalizedBoxEnergy (operator (2 * m)) (baseWord (patternSign s)) -
        normalizedBoxEnergy (operator (2 * m)) (baseWord (patternSign t))) -
      (∑ j, (patternSign s j * operator (2 * m) (baseWord (patternSign s)) j -
        patternSign t j * operator (2 * m) (baseWord (patternSign t)) j) * η j) / 2| ≤
      (12 * S * E + 3 * D + K / 4 + E ^ 2) / (2 * m : ℝ) ^ 3 := by
  have hn : 0 < 2 * m := by omega
  have hnR : (1 : ℝ) ≤ 2 * m := by exact_mod_cast (show 1 ≤ 2 * m by omega)
  have hnpos : (0 : ℝ) < 2 * m := lt_of_lt_of_le (by norm_num) hnR
  have heven : Even (2 * m) := ⟨m, by omega⟩
  have hη' : meanSquare η ≤ K / (↑(2 * m) : ℝ) ^ 5 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hη
  have he1 : meanSquare e ≤ E ^ 2 / (↑(2 * m) : ℝ) ^ 4 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using he
  have he2 : meanSquare e' ≤ E ^ 2 / (↑(2 * m) : ℝ) ^ 4 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using he'
  have hs := quadratic_budget hn heven (patternSign s) η e (patternSign_is_sign s) hη' he1
  have ht := quadratic_budget hn heven (patternSign t) η e' (patternSign_is_sign t) hη' he2
  have hp := error_pairing_budget hm s t e e' hE hS hd he hed
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hs ht
  rw [exact_expansion hn, exact_expansion hn]
  have hsum : (∑ j, (patternSign s j * operator (2 * m) (baseWord (patternSign s)) j -
      patternSign t j * operator (2 * m) (baseWord (patternSign t)) j) * η j) =
      (∑ j, patternSign s j * operator (2 * m) (baseWord (patternSign s)) j * η j) -
      (∑ j, patternSign t j * operator (2 * m) (baseWord (patternSign t)) j * η j) := by
    simp only [sub_mul, Finset.sum_sub_distrib]
  rw [hsum]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  have hdecomp (a b c d f g h i : ℝ) :
      (a + b / 2 + c + d - (f + g / 2 + h + i)) - (a - f) - (b - g) / 2 =
        (c - h) + d - i := by ring
  rw [hdecomp]
  apply (abs_sub _ _).trans
  apply (add_le_add (abs_add_le _ _) le_rfl).trans
  have hnum : (2 * m : ℝ) ^ 3 ≤ (2 * m : ℝ) ^ 4 := by
    nlinarith [pow_pos hnpos 3, mul_le_mul_of_nonneg_left hnR (pow_nonneg hnpos.le 3)]
  have hepow : E ^ 2 / (2 * m : ℝ) ^ 4 ≤ E ^ 2 / (2 * m : ℝ) ^ 3 :=
    div_le_div_of_nonneg_left (sq_nonneg E) (pow_pos hnpos 3) hnum
  have hbound := add_le_add (add_le_add hp hs) ht
  apply hbound.trans
  calc
    _ = (12 * S * E + 3 * D + K / 4) / (2 * m : ℝ) ^ 3 +
        E ^ 2 / (2 * m : ℝ) ^ 4 := by ring
    _ ≤ (12 * S * E + 3 * D + K / 4) / (2 * m : ℝ) ^ 3 +
        E ^ 2 / (2 * m : ℝ) ^ 3 := add_le_add le_rfl hepow
    _ = _ := by ring

end
end StructuralNote.FixedSchurWordExpansionBounds
