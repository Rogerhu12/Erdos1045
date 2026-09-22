import StructuralNote.FixedSchurBalancedAlignment
import StructuralNote.FixedSchurThreeBlockDegrees

/-! A reflection-symmetric canonical balanced word and the symmetries forced
on its unique actual fixed-Schur extremizer.

The outer two half-period blocks are chosen equal.  When `3 ∣ m`, all three
blocks are equal and the full word also has the `2 * m / 3` cyclic period.
-/

namespace StructuralNote.FixedSchurCanonicalWordSymmetry

open Filter
open Erdos1045 Erdos1045.EventualExact
open Erdos1045.EventualExact.FiniteBox Erdos1045.EventualExact.FourierMultiplier
open FixedSchurChart FixedSchurEquationSmooth FixedSchurChartSmooth
open FixedSchurCyclicEquivariance FixedSchurReflectionEquivariance
open FixedSchurExtremalSymmetry FixedSchurBalancedAlignment
open FixedSchurThreeBlockDegrees SignPatternSymmetry SignPatternGridShift
open FiniteCompressionRanked SolThreeBlockWord IntegerBalance
open scoped Topology

noncomputable section

def symmetricOuter (m : ℕ) : ℕ :=
  if m % 3 = 2 then m / 3 + 1 else m / 3

def symmetricMiddle (m : ℕ) : ℕ :=
  if m % 3 = 1 then m / 3 + 1 else m / 3

theorem symmetric_sum (m : ℕ) :
    symmetricOuter m + symmetricMiddle m + symmetricOuter m = m := by
  unfold symmetricOuter symmetricMiddle
  have hmod := Nat.mod_lt m (by omega : 0 < 3)
  have hdiv := Nat.mod_add_div m 3
  split_ifs <;> omega

theorem symmetric_pos {m : ℕ} (hm : 3 ≤ m) :
    0 < symmetricOuter m ∧ 0 < symmetricMiddle m ∧ 0 < symmetricOuter m := by
  unfold symmetricOuter symmetricMiddle
  have hmod := Nat.mod_lt m (by omega : 0 < 3)
  split_ifs <;> omega

theorem symmetric_balanced (m : ℕ) :
    BalancedAt (m / 3) (symmetricOuter m) (symmetricMiddle m) (symmetricOuter m) := by
  unfold symmetricOuter symmetricMiddle BalancedAt
  split_ifs <;> simp

def canonicalPattern {m : ℕ} (hm : 3 ≤ m) : SignPattern (by omega : 0 < m) :=
  threeBlockPattern (by omega) (symmetric_pos hm) (symmetric_sum m)

theorem signPattern_ext {m : ℕ} {hm : 0 < m} {s t : SignPattern hm}
    (h : ∀ j, patternSign s j = patternSign t j) : s = t := by
  apply Subtype.ext
  funext j
  have hp := h j
  change boolSign (s.val j) = boolSign (t.val j) at hp
  cases hs : s.val j <;> cases ht : t.val j <;>
    simp [boolSign, hs, ht] at hp ⊢ <;> norm_num at hp

theorem edgeReflection_val {n : ℕ} (hn : 2 ≤ n) (j : Fin n) :
    (edgeReflection n j).val =
      if j.val + 1 = n then 0 else n - (j.val + 1) := by
  let _ : NeZero n := ⟨by omega⟩
  simp only [edgeReflection_apply, finRotate_apply]
  rw [Fin.val_neg]
  by_cases hj : j.val + 1 = n
  · have hrot : (j + 1 : Fin n) = 0 := by
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_one', Fin.val_zero]
      rw [Nat.mod_eq_of_lt (by omega : 1 < n)]
      rw [hj, Nat.mod_self]
    rw [if_pos hj, if_pos hrot]
  · have hlt : j.val + 1 < n := by omega
    have hval : (j + 1 : Fin n).val = j.val + 1 := by
      simp only [Fin.val_add, Fin.val_one']
      rw [Nat.mod_eq_of_lt (by omega : 1 < n), Nat.mod_eq_of_lt hlt]
    have hrot : j + 1 ≠ (0 : Fin n) := by
      intro h
      have hv := congrArg Fin.val h
      rw [hval] at hv
      simp only [Fin.val_zero] at hv
      omega
    rw [if_neg hj, if_neg hrot, hval]

theorem reflectPattern_threeBlock_symmetric {m a b : ℕ} (hm : 2 ≤ m)
    (hp : 0 < a ∧ 0 < b ∧ 0 < a) (hs : a + b + a = m) :
    reflectPattern (threeBlockPattern (by omega) hp hs) =
      threeBlockPattern (by omega) hp hs := by
  apply signPattern_ext
  intro j
  rw [patternSign_reflectPattern]
  simp only [patternSign_threeBlockPattern, raw_formula hp hs,
    edgeReflection_val (show 2 ≤ 2 * m by omega)]
  split_ifs <;> norm_num <;> omega

theorem canonicalPattern_reflect {m : ℕ} (hm : 3 ≤ m) :
    reflectPattern (canonicalPattern hm) = canonicalPattern hm := by
  exact reflectPattern_threeBlock_symmetric (by omega) (symmetric_pos hm)
    (symmetric_sum m)

theorem cyclicIndex_even_val {m : ℕ} (hm : 0 < m) (k : ℕ)
    (j : Fin (2 * m)) :
    (cyclicIndex (2 * m) k j).val = (j.val + k) % (2 * m) := by
  have hj : site hm j.val = j := by
    apply Fin.ext
    simp only [site, Nat.mod_eq_of_lt j.isLt]
  calc
    (cyclicIndex (2 * m) k j).val =
        (cyclicIndex (2 * m) k (site hm j.val)).val := by rw [hj]
    _ = (site hm (j.val + k)).val := by
      exact congrArg Fin.val (finRotate_pow_site hm j.val k)
    _ = (j.val + k) % (2 * m) := rfl

theorem rotatePattern_threeBlock_equal {a : ℕ} (ha : 0 < a) :
    let m := 3 * a
    let hp : 0 < a ∧ 0 < a ∧ 0 < a := ⟨ha, ha, ha⟩
    let hs : a + a + a = m := by omega
    rotatePattern (2 * a) (threeBlockPattern (by omega) hp hs) =
      threeBlockPattern (by omega) hp hs := by
  dsimp only
  apply signPattern_ext
  intro j
  rw [patternSign_rotatePattern]
  simp only [patternSign_threeBlockPattern]
  rw [raw_formula (⟨ha, ha, ha⟩) (by omega),
    raw_formula (⟨ha, ha, ha⟩) (by omega)]
  have hidx : (((finRotate (2 * (3 * a))) ^ (2 * a)) j).val =
      (j.val + 2 * a) % (2 * (3 * a)) := by
    exact cyclicIndex_even_val (show 0 < 3 * a by omega) (2 * a) j
  rw [hidx]
  have hmod : (j.val + 2 * a) % (2 * (3 * a)) =
      if j.val < 4 * a then j.val + 2 * a else j.val - 4 * a := by
    by_cases hj : j.val < 4 * a
    · rw [if_pos hj, Nat.mod_eq_of_lt (by omega)]
    · rw [if_neg hj]
      have heq : j.val + 2 * a = (j.val - 4 * a) + 2 * (3 * a) := by omega
      rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rw [hmod]
  split_ifs <;> norm_num <;> omega

theorem symmetricOuter_eq_third {m : ℕ} (hm : 3 ∣ m) :
    symmetricOuter m = m / 3 := by
  obtain ⟨a, rfl⟩ := hm
  simp [symmetricOuter]

theorem symmetricMiddle_eq_third {m : ℕ} (hm : 3 ∣ m) :
    symmetricMiddle m = m / 3 := by
  obtain ⟨a, rfl⟩ := hm
  simp [symmetricMiddle]

theorem canonicalPattern_third_shift {m : ℕ} (hm : 3 ≤ m) (hdiv : 3 ∣ m) :
    rotatePattern (2 * (m / 3)) (canonicalPattern hm) = canonicalPattern hm := by
  obtain ⟨a, ha⟩ := hdiv
  have ha0 : 0 < a := by omega
  subst m
  have ho : symmetricOuter (3 * a) = a := by
    rw [symmetricOuter_eq_third (by exact ⟨a, rfl⟩)]
    omega
  have hi : symmetricMiddle (3 * a) = a := by
    rw [symmetricMiddle_eq_third (by exact ⟨a, rfl⟩)]
    omega
  unfold canonicalPattern
  have hk : 3 * a / 3 = a := by omega
  simpa only [ho, hi, hk] using
    rotatePattern_threeBlock_equal ha0

theorem eventual_canonical_reflection_symmetry : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 3 ≤ m) (x : SchurParameters m),
      x ∈ domain (by omega) →
      ExtremalNormalization.DiameterExtremal
        (configuration (by omega) (canonicalPattern hm) x.1 x.2) →
      configuration (by omega) (canonicalPattern hm) x.1 x.2 =
        reflectCenter (configuration (by omega) (canonicalPattern hm) x.1 x.2) := by
  filter_upwards [eventual_reflection_forced_configuration] with m hforce
  intro hm x hx hmax
  exact hforce (by omega) (canonicalPattern hm) x hx hmax
    (canonicalPattern_reflect hm)

theorem eventual_canonical_third_turn_symmetry : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 3 ≤ m) (hdiv : 3 ∣ m) (x : SchurParameters m),
      x ∈ domain (by omega) →
      ExtremalNormalization.DiameterExtremal
        (configuration (by omega) (canonicalPattern hm) x.1 x.2) →
      configuration (by omega) (canonicalPattern hm) x.1 x.2 =
        cyclicCenter (2 * (m / 3))
          (configuration (by omega) (canonicalPattern hm) x.1 x.2) := by
  filter_upwards [eventual_cyclic_forced_configuration] with m hforce
  intro hm hdiv x hx hmax
  exact hforce (by omega) (2 * (m / 3)) (canonicalPattern hm) x hx hmax
    (canonicalPattern_third_shift hm hdiv)

end
end StructuralNote.FixedSchurCanonicalWordSymmetry
