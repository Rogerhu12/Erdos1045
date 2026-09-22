import StructuralNote.ThreeArcCanonicalWord
import StructuralNote.ThreeBlockBalancedMaximum

/-! Classification of all actual near-maximal words. The alternatives and
their quantitative improvements no longer assume localization or block structure. -/

namespace StructuralNote.FiniteWordClassification

open Real Set Filter Erdos1045.EventualExact FourierMultiplier FiniteBox
open FixedDualClassificationFinite SignPatternSymmetry SignPatternEnergySymmetry
open LocalizedTerminalImprovement LocalizedThreeArcDichotomy ThreeArcCanonicalWord
open FiniteCompressionArcAngles ThreeBlockKernelMargin ThreeBlockLocalImprovement
open ThreeBlockBalancedMaximum SolThreeBlockWord SolThreeBlockEnergy
open DiscreteConvexBalance IntegerBalance SolWordHamming
open scoped Topology
noncomputable section

def BalancedWord {m : ℕ} (hm : 0 < m) (s : SignPattern hm) : Prop :=
  ∃ k a b c : ℕ, ∃ hp : 0 < a ∧ 0 < b ∧ 0 < c, ∃ hsum : a + b + c = m,
    globalNegate (rotatePattern k s) = threeBlockPattern hm hp hsum ∧
      BalancedAt (m / 3) a b c

theorem rotatePattern_compose {m : ℕ} {hm : 0 < m} (k l : ℕ) (s : SignPattern hm) :
    rotatePattern l (rotatePattern k s) = rotatePattern (k + l) s := by
  apply Subtype.ext
  funext j
  simp only [rotatePattern, reindex, reindexRaw, pow_add, Equiv.Perm.mul_apply]

theorem balancedWord_of_rotate {m : ℕ} {hm : 0 < m} {s : SignPattern hm}
    (k : ℕ) (h : BalancedWord hm (rotatePattern k s)) : BalancedWord hm s := by
  obtain ⟨l, a, b, c, hp, hsum, heq, hbal⟩ := h
  refine ⟨k + l, a, b, c, hp, hsum, ?_, hbal⟩
  rwa [rotatePattern_compose] at heq

theorem improvement_mono {m : ℕ} {hm : 0 < m} {s : SignPattern hm} {η η' : ℝ}
    (hle : η' ≤ η) (h : TwoSiteImprovement hm η s) : TwoSiteImprovement hm η' s := by
  obtain ⟨t, hh, hg⟩ := h
  exact ⟨t, hh, (div_le_div_of_nonneg_right hle (by positivity)).trans hg⟩

theorem eventually_near_maximum_classification (C₀ : ℝ) : ∃ η : ℝ, 0 < η ∧
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 0 < m) (s : SignPattern hm),
      deficit hm s ≤ C₀ / (2 * m : ℝ) ^ 2 →
        BalancedWord hm s ∨ TwoSiteImprovement hm η s := by
  obtain ⟨η₁, hη₁, hlocal⟩ := eventually_near_maximum_three_arcs C₀
  obtain ⟨α, β, η₂, _, hα, hβ, _, hη₂, hbalance⟩ := eventually_uniform_two_site_improvement
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, ?_⟩
  filter_upwards [hlocal, hbalance, eventually_small_grid_step] with m hloc hbal hstep
  intro hm s hdef
  rcases hloc hm s hdef with himp | ⟨q, γ, hγ, hsign, hthree⟩
  · exact Or.inr (improvement_mono (min_le_left _ _) himp)
  · obtain ⟨k, a, b, c, hp, hsum, heq, ha, hb, hc⟩ :=
      three_arcs_reconstruct hm (rotatePattern q s) hγ.1 hγ.2.le hstep hsign hthree
    by_cases hB : BalancedAt (m / 3) a b c
    · exact Or.inl (balancedWord_of_rotate q ⟨k, a, b, c, hp, hsum, heq, hB⟩)
    · have ha' : angle m a ∈ Icc α β := ⟨hα.le.trans ha.1, ha.2.trans hβ.le⟩
      have hb' : angle m b ∈ Icc α β := ⟨hα.le.trans hb.1, hb.2.trans hβ.le⟩
      have hc' : angle m c ∈ Icc α β := ⟨hα.le.trans hc.1, hc.2.trans hβ.le⟩
      obtain ⟨a', b', c', hp', hs', hh, hg, _⟩ := hbal hm a b c hp hsum ha' hb' hc' hB
      have hcan : TwoSiteImprovement hm η₂ (threeBlockPattern hm hp hsum) :=
        ⟨threeBlockPattern hm hp' hs', hh, hg⟩
      rw [← heq] at hcan
      exact Or.inr (improvement_mono (min_le_right _ _)
        (improvement_of_rotate q (improvement_of_rotate k (improvement_of_negate hcan))))

/-- The two-site form of Proposition 8.1, for the actual finite operator and B. -/
theorem eventually_nonbalanced_improvement (C₀ : ℝ) : ∃ η : ℝ, 0 < η ∧
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 0 < m) (s : SignPattern hm),
      deficit hm s ≤ C₀ / (2 * m : ℝ) ^ 2 → ¬ BalancedWord hm s →
      ∃ t : SignPattern hm, hamming s t ≤ 2 ∧
        η / (2 * m : ℕ) ^ 2 ≤
          normalizedBoxEnergy (operator (2 * m)) (vertex (amplitude (2 * m)) t) -
            normalizedBoxEnergy (operator (2 * m)) (vertex (amplitude (2 * m)) s) ∧
        0 ≤ deficit hm t ∧ deficit hm t + η / (2 * m : ℕ) ^ 2 ≤ deficit hm s := by
  obtain ⟨η, hη, hevent⟩ := eventually_near_maximum_classification C₀
  refine ⟨η, hη, ?_⟩
  filter_upwards [hevent] with m hclass hm s hdef hnot
  obtain ⟨t, hh, hg⟩ := (hclass hm s hdef).resolve_left hnot
  have hupper := energy_le_B hm (vertex_mem_box (amplitude_pos (by omega)).le t)
  refine ⟨t, hh, hg, sub_nonneg.mpr hupper, ?_⟩
  dsimp only [deficit]
  linarith

theorem eventually_maximizer_balanced : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (s : SignPattern hm),
      normalizedBoxEnergy (operator (2 * m)) (vertex (amplitude (2 * m)) s) = B hm →
        BalancedWord hm s := by
  obtain ⟨η, hη, hevent⟩ := eventually_near_maximum_classification 0
  filter_upwards [hevent] with m hclass hm s hmax
  have hd : deficit hm s ≤ (0 : ℝ) / (2 * m : ℝ) ^ 2 := by simp [deficit, hmax]
  rcases hclass hm s hd with hbal | himp
  · exact hbal
  · obtain ⟨t, _, hg⟩ := himp
    have hu := energy_le_B hm (vertex_mem_box (amplitude_pos (by omega)).le t)
    have hp : 0 < η / (2 * m : ℕ) ^ 2 := by positivity
    rw [hmax] at hg
    linarith

theorem balancedWord_energy {m : ℕ} (hm : 3 ≤ m) (s : SignPattern (by omega : 0 < m))
    (h : BalancedWord (by omega) s) :
    normalizedBoxEnergy (operator (2 * m)) (vertex (amplitude (2 * m)) s) =
      balancedEnergy m hm := by
  obtain ⟨k, a, b, c, hp, hs, heq, hbal⟩ := h
  have he := congrArg (fun t : SignPattern (by omega : 0 < m) =>
    normalizedBoxEnergy (operator (2 * m)) (vertex (amplitude (2 * m)) t)) heq
  rw [energy_globalNegate, energy_rotatePattern] at he
  exact he.trans (energy_eq_of_balanced hm hp hs hbal)

/-- Corollary 8.6: the whole-box maximum equals the actual balanced-word energy. -/
theorem eventually_B_eq_balancedEnergy : ∀ᶠ m : ℕ in atTop, ∀ hm : 3 ≤ m,
    B (by omega : 0 < m) = balancedEnergy m hm := by
  filter_upwards [eventually_maximizer_balanced] with m hclass hm
  obtain ⟨s, hs, _⟩ := B_attained_at_vertex (by omega : 0 < m)
  exact hs.symm.trans (balancedWord_energy hm s (hclass _ s hs))

theorem eventually_maximizer_iff_balanced : ∀ᶠ m : ℕ in atTop, ∀ (hm : 3 ≤ m)
    (s : SignPattern (by omega : 0 < m)),
    normalizedBoxEnergy (operator (2 * m)) (vertex (amplitude (2 * m)) s) =
      B (by omega : 0 < m) ↔ BalancedWord (by omega) s := by
  filter_upwards [eventually_maximizer_balanced, eventually_B_eq_balancedEnergy] with m hclass hB
  intro hm s
  constructor
  · exact hclass _ s
  · intro hs
    exact (balancedWord_energy hm s hs).trans (hB hm).symm

end
end StructuralNote.FiniteWordClassification
