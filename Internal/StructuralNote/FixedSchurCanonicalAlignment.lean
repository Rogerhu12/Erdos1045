import StructuralNote.FixedSchurCanonicalWordSymmetry

/-! Canonical cyclic alignment of every balanced word.

Balanced block lengths contain one distinguished value and two equal values.
Cyclically moving the distinguished block to the middle produces the fixed
reflection-symmetric `canonicalPattern`.  The same relabeling is then applied
to the actual fixed-Schur parameters and configuration.
-/

namespace StructuralNote.FixedSchurCanonicalAlignment

open Filter
open Erdos1045 Erdos1045.EventualExact
open Erdos1045.EventualExact.FiniteBox Erdos1045.EventualExact.FourierMultiplier
open FixedSchurChart FixedSchurEquationSmooth FixedSchurChartSmooth
open FixedSchurCyclicEquivariance FixedSchurExtremalSymmetry
open FixedSchurBalancedAlignment FixedSchurCanonicalWordSymmetry
open FixedSchurThreeBlockDegrees SignPatternSymmetry
open FiniteWordClassification SolThreeBlockWord IntegerBalance
open scoped Topology

noncomputable section

theorem rotatePattern_threeBlock_right {m a b c : ℕ} (hm : 2 ≤ m)
    (hp : 0 < a ∧ 0 < b ∧ 0 < c) (hs : a + b + c = m) :
    let hp' : 0 < c ∧ 0 < a ∧ 0 < b := ⟨hp.2.2, hp.1, hp.2.1⟩
    let hs' : c + a + b = m := by omega
    rotatePattern (a + b) (threeBlockPattern (by omega) hp hs) =
      threeBlockPattern (by omega) hp' hs' := by
  dsimp only
  apply signPattern_ext
  intro j
  rw [patternSign_rotatePattern]
  simp only [patternSign_threeBlockPattern]
  rw [raw_formula hp hs,
    raw_formula (⟨hp.2.2, hp.1, hp.2.1⟩) (by omega)]
  have hidx : (((finRotate (2 * m)) ^ (a + b)) j).val =
      (j.val + (a + b)) % (2 * m) := by
    exact cyclicIndex_even_val (by omega) (a + b) j
  rw [hidx]
  have hmod : (j.val + (a + b)) % (2 * m) =
      if j.val < m + c then j.val + (a + b) else j.val - (m + c) := by
    by_cases hj : j.val < m + c
    · rw [if_pos hj, Nat.mod_eq_of_lt (by omega)]
    · rw [if_neg hj]
      have heq : j.val + (a + b) = (j.val - (m + c)) + 2 * m := by omega
      rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rw [hmod]
  split_ifs <;> norm_num <;> omega

theorem rotatePattern_threeBlock_left {m a b c : ℕ} (hm : 2 ≤ m)
    (hp : 0 < a ∧ 0 < b ∧ 0 < c) (hs : a + b + c = m) :
    let hp' : 0 < b ∧ 0 < c ∧ 0 < a := ⟨hp.2.1, hp.2.2, hp.1⟩
    let hs' : b + c + a = m := by omega
    rotatePattern (m + a) (threeBlockPattern (by omega) hp hs) =
      threeBlockPattern (by omega) hp' hs' := by
  dsimp only
  apply signPattern_ext
  intro j
  rw [patternSign_rotatePattern]
  simp only [patternSign_threeBlockPattern]
  rw [raw_formula hp hs,
    raw_formula (⟨hp.2.1, hp.2.2, hp.1⟩) (by omega)]
  have hidx : (((finRotate (2 * m)) ^ (m + a)) j).val =
      (j.val + (m + a)) % (2 * m) := by
    exact cyclicIndex_even_val (by omega) (m + a) j
  rw [hidx]
  have hmod : (j.val + (m + a)) % (2 * m) =
      if j.val < b + c then j.val + (m + a) else j.val - (b + c) := by
    by_cases hj : j.val < b + c
    · rw [if_pos hj, Nat.mod_eq_of_lt (by omega)]
    · rw [if_neg hj]
      have heq : j.val + (m + a) = (j.val - (b + c)) + 2 * m := by omega
      rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rw [hmod]
  split_ifs <;> norm_num <;> omega

theorem balanced_lengths_cyclic_cases {m a b c : ℕ}
    (hs : a + b + c = m) (hbal : BalancedAt (m / 3) a b c) :
    (a = symmetricOuter m ∧ b = symmetricMiddle m ∧ c = symmetricOuter m) ∨
    (a = symmetricMiddle m ∧ b = symmetricOuter m ∧ c = symmetricOuter m) ∨
    (a = symmetricOuter m ∧ b = symmetricOuter m ∧ c = symmetricMiddle m) := by
  unfold BalancedAt at hbal
  simp only [symmetricOuter, symmetricMiddle]
  have hmod := Nat.mod_lt m (by omega : 0 < 3)
  have hdiv := Nat.mod_add_div m 3
  split_ifs <;> omega

theorem balancedThreeBlock_canonical_alignment {m a b c : ℕ} (hm : 3 ≤ m)
    (hp : 0 < a ∧ 0 < b ∧ 0 < c) (hs : a + b + c = m)
    (hbal : BalancedAt (m / 3) a b c) :
    ∃ k : ℕ, rotatePattern k (threeBlockPattern (by omega) hp hs) =
      canonicalPattern hm := by
  rcases balanced_lengths_cyclic_cases hs hbal with hcase | hcase | hcase
  · obtain ⟨ha, hb, hc⟩ := hcase
    subst a
    subst b
    subst c
    refine ⟨0, ?_⟩
    apply signPattern_ext
    intro j
    unfold canonicalPattern
    simp only [patternSign_rotatePattern, pow_zero, Equiv.Perm.one_apply,
      patternSign_threeBlockPattern]
  · obtain ⟨ha, hb, hc⟩ := hcase
    subst a
    subst b
    subst c
    refine ⟨symmetricMiddle m + symmetricOuter m, ?_⟩
    rw [rotatePattern_threeBlock_right (by omega) hp hs]
    rfl
  · obtain ⟨ha, hb, hc⟩ := hcase
    subst a
    subst b
    subst c
    refine ⟨m + symmetricOuter m, ?_⟩
    rw [rotatePattern_threeBlock_left (by omega) hp hs]
    rfl

theorem balancedWord_canonical_alignment {m : ℕ} (hm : 3 ≤ m)
    (s : SignPattern (by omega)) (hs : BalancedWord (by omega) s) :
    ∃ k : ℕ, rotatePattern k s = canonicalPattern hm := by
  obtain ⟨k₀, a, b, c, hp, hsum, hword, hbal⟩ :=
    balancedWord_cyclic_alignment s hs
  obtain ⟨k₁, hcan⟩ := balancedThreeBlock_canonical_alignment hm hp hsum hbal
  refine ⟨k₀ + k₁, ?_⟩
  rw [← rotatePattern_compose k₀ k₁ s, hword, hcan]

/-- Every balanced actual extremizer has a representative in the one fixed
canonical word fiber. -/
theorem eventual_balanced_extremal_canonical_alignment : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 3 ≤ m) (s : SignPattern (by omega)) (x : SchurParameters m),
      x ∈ domain (by omega) →
      ExtremalNormalization.DiameterExtremal
        (configuration (by omega) s x.1 x.2) →
      BalancedWord (by omega) s →
      ∃ k : ℕ,
        rotatePattern k s = canonicalPattern hm ∧
        (cyclicReal k x.1, cyclicCenter k x.2) ∈ domain (by omega) ∧
        ExtremalNormalization.DiameterExtremal
          (configuration (by omega) (canonicalPattern hm)
            (cyclicReal k x.1) (cyclicCenter k x.2)) ∧
        configuration (by omega) (canonicalPattern hm)
            (cyclicReal k x.1) (cyclicCenter k x.2) =
          cyclicCenter k (configuration (by omega) s x.1 x.2) := by
  filter_upwards [eventual_configuration_cyclic] with m hcfg
  intro hm s x hx hmax hbal
  obtain ⟨k, hword⟩ := balancedWord_canonical_alignment hm s hbal
  have hdom : (cyclicReal k x.1, cyclicCenter k x.2) ∈ domain (by omega) :=
    inDomain_cyclic (by omega) k x.1 x.2 hx
  have hc := hcfg (by omega) k s x.1 x.2 hx
  rw [hword] at hc
  have hext : ExtremalNormalization.DiameterExtremal
      (configuration (by omega) (canonicalPattern hm)
        (cyclicReal k x.1) (cyclicCenter k x.2)) := by
    rw [hc]
    exact diameterExtremal_cyclicCenter k hmax
  exact ⟨k, hword, hdom, hext, hc⟩

/-- Two balanced extremizers are identical after their genuine cyclic
alignment into the canonical word fiber. -/
theorem eventual_balanced_extremal_rigid_unique : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 3 ≤ m) (s t : SignPattern (by omega)) (x y : SchurParameters m),
      x ∈ domain (by omega) → y ∈ domain (by omega) →
      ExtremalNormalization.DiameterExtremal
        (configuration (by omega) s x.1 x.2) →
      ExtremalNormalization.DiameterExtremal
        (configuration (by omega) t y.1 y.2) →
      BalancedWord (by omega) s → BalancedWord (by omega) t →
      ∃ k l : ℕ,
        rotatePattern k s = canonicalPattern hm ∧
        rotatePattern l t = canonicalPattern hm ∧
        (cyclicReal k x.1, cyclicCenter k x.2) =
          (cyclicReal l y.1, cyclicCenter l y.2) := by
  filter_upwards [eventual_rigid_unique_after_cyclic_alignment] with m huniq
  intro hm s t x y hx hy hxmax hymax hs ht
  obtain ⟨k, hk⟩ := balancedWord_canonical_alignment hm s hs
  obtain ⟨l, hl⟩ := balancedWord_canonical_alignment hm t ht
  exact ⟨k, l, hk, hl,
    huniq (by omega) s t (canonicalPattern hm) k l x y hx hy hxmax hymax hk hl⟩

end
end StructuralNote.FixedSchurCanonicalAlignment
