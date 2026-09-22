import StructuralNote.FixedSchurExtremalSymmetry
import StructuralNote.FiniteWordClassification
import StructuralNote.SignPatternGridShift

/-! Cyclic alignment of balanced selected words and their actual extremizers.

The `globalNegate` occurring in the finite classification is realized by a
half-period cyclic relabeling.  Thus a balanced-word witness yields an honest
cyclic alignment of both the word and the fixed-Schur configuration.
-/

namespace StructuralNote.FixedSchurBalancedAlignment

open Filter
open Erdos1045 Erdos1045.EventualExact
open Erdos1045.EventualExact.FiniteBox Erdos1045.EventualExact.FourierMultiplier
open FixedSchurChart FixedSchurEquationSmooth FixedSchurChartSmooth
open FixedSchurCyclicEquivariance FixedSchurExtremalSymmetry
open FixedSchurGeometricStationarity FixedDualClassificationStep
open FiniteCompressionRanked
open SignPatternSymmetry SignPatternGridShift FiniteWordClassification
open SolThreeBlockWord IntegerBalance
open scoped Topology

noncomputable section

theorem cyclicIndex_halfTurn {m : ℕ} (hm : 0 < m) (j : Fin (2 * m)) :
    cyclicIndex (2 * m) m j = halfTurn hm j := by
  have hj : site hm j.val = j := by
    apply Fin.ext
    simp only [site, Nat.mod_eq_of_lt j.isLt]
  rw [← hj]
  rw [cyclicIndex, finRotate_pow_site hm]
  apply Fin.ext
  simp only [site, halfTurn]
  rw [Nat.mod_eq_of_lt j.isLt]

theorem rotatePattern_halfPeriod {m : ℕ} {hm : 0 < m} (s : SignPattern hm) :
    rotatePattern m s = globalNegate s := by
  apply Subtype.ext
  funext j
  have hp : patternSign (rotatePattern m s) j =
      patternSign (globalNegate s) j := by
    rw [patternSign_rotatePattern,
      show ((finRotate (2 * m)) ^ m) j = halfTurn hm j by
        exact cyclicIndex_halfTurn hm j,
      patternSign_antiperiodic, patternSign_globalNegate]
  change boolSign ((rotatePattern m s).val j) =
      boolSign ((globalNegate s).val j) at hp
  cases hs : (rotatePattern m s).val j <;>
    cases ht : (globalNegate s).val j <;>
    simp [boolSign, hs, ht] at hp ⊢ <;> norm_num at hp

/-- The finite balanced-word witness can be chosen as a pure cyclic
relabeling, because its apparent global sign change is the half-period shift. -/
theorem balancedWord_cyclic_alignment {m : ℕ} {hm : 0 < m}
    (s : SignPattern hm) (hs : BalancedWord hm s) :
    ∃ k a b c : ℕ, ∃ hp : 0 < a ∧ 0 < b ∧ 0 < c,
      ∃ hsum : a + b + c = m,
        rotatePattern k s = threeBlockPattern hm hp hsum ∧
          BalancedAt (m / 3) a b c := by
  obtain ⟨k, a, b, c, hp, hsum, heq, hbal⟩ := hs
  refine ⟨k + m, a, b, c, hp, hsum, ?_, hbal⟩
  calc
    rotatePattern (k + m) s = rotatePattern m (rotatePattern k s) :=
      (rotatePattern_compose k m s).symm
    _ = globalNegate (rotatePattern k s) := rotatePattern_halfPeriod _
    _ = threeBlockPattern hm hp hsum := heq

/-- An extremizer in a balanced selected-word fiber admits an actual
three-block aligned representative.  Every item in the conclusion is the
result of the same cyclic action. -/
theorem eventual_balanced_extremal_alignment : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : SignPattern (by omega)) (x : SchurParameters m),
      x ∈ domain (by omega) →
      ExtremalNormalization.DiameterExtremal
        (configuration (by omega) s x.1 x.2) →
      BalancedWord (by omega) s →
      ∃ k a b c : ℕ, ∃ hp : 0 < a ∧ 0 < b ∧ 0 < c,
        ∃ hsum : a + b + c = m,
          BalancedAt (m / 3) a b c ∧
          rotatePattern k s = threeBlockPattern (by omega) hp hsum ∧
          (cyclicReal k x.1, cyclicCenter k x.2) ∈ domain (by omega) ∧
          ExtremalNormalization.DiameterExtremal
            (configuration (by omega) (threeBlockPattern (by omega) hp hsum)
              (cyclicReal k x.1) (cyclicCenter k x.2)) ∧
          configuration (by omega) (threeBlockPattern (by omega) hp hsum)
              (cyclicReal k x.1) (cyclicCenter k x.2) =
            cyclicCenter k (configuration (by omega) s x.1 x.2) := by
  filter_upwards [eventual_configuration_cyclic] with m hcfg
  intro hm s x hx hmax hbal
  obtain ⟨k, a, b, c, hp, hsum, hword, hbalanced⟩ :=
    balancedWord_cyclic_alignment s hbal
  have hdom : (cyclicReal k x.1, cyclicCenter k x.2) ∈ domain (by omega) :=
    inDomain_cyclic (by omega) k x.1 x.2 hx
  have hconfig := hcfg hm k s x.1 x.2 hx
  rw [hword] at hconfig
  have hext : ExtremalNormalization.DiameterExtremal
      (configuration (by omega) (threeBlockPattern (by omega) hp hsum)
        (cyclicReal k x.1) (cyclicCenter k x.2)) := by
    rw [hconfig]
    exact diameterExtremal_cyclicCenter k hmax
  exact ⟨k, a, b, c, hp, hsum, hbalanced, hword, hdom, hext, hconfig⟩

/-- Once two extremizers have been genuinely relabeled into the same word
fiber, strict concavity makes their aligned chart parameters identical. -/
theorem eventual_rigid_unique_after_cyclic_alignment : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s t u : SignPattern (by omega)) (k l : ℕ)
      (x y : SchurParameters m),
      x ∈ domain (by omega) → y ∈ domain (by omega) →
      ExtremalNormalization.DiameterExtremal
        (configuration (by omega) s x.1 x.2) →
      ExtremalNormalization.DiameterExtremal
        (configuration (by omega) t y.1 y.2) →
      rotatePattern k s = u → rotatePattern l t = u →
      (cyclicReal k x.1, cyclicCenter k x.2) =
        (cyclicReal l y.1, cyclicCenter l y.2) := by
  filter_upwards [eventual_same_word_extremal_unique,
    eventual_configuration_cyclic] with m huniq hcfg
  intro hm s t u k l x y hx hy hxmax hymax hsu htu
  have hxdom : (cyclicReal k x.1, cyclicCenter k x.2) ∈ domain (by omega) :=
    inDomain_cyclic (by omega) k x.1 x.2 hx
  have hydom : (cyclicReal l y.1, cyclicCenter l y.2) ∈ domain (by omega) :=
    inDomain_cyclic (by omega) l y.1 y.2 hy
  have hxcfg := hcfg hm k s x.1 x.2 hx
  have hycfg := hcfg hm l t y.1 y.2 hy
  rw [hsu] at hxcfg
  rw [htu] at hycfg
  have hxext : ExtremalNormalization.DiameterExtremal
      (configuration (by omega) u (cyclicReal k x.1) (cyclicCenter k x.2)) := by
    rw [hxcfg]
    exact diameterExtremal_cyclicCenter k hxmax
  have hyext : ExtremalNormalization.DiameterExtremal
      (configuration (by omega) u (cyclicReal l y.1) (cyclicCenter l y.2)) := by
    rw [hycfg]
    exact diameterExtremal_cyclicCenter l hymax
  exact huniq hm u _ hxdom _ hydom hxext hyext

end
end StructuralNote.FixedSchurBalancedAlignment
