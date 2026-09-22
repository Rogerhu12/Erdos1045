import StructuralNote.ThreeBlockKernelMargin
import StructuralNote.SolThreeBlockEnergy

/-! Uniform two-site improvement for nonbalanced three-block words, with no
kernel-margin hypothesis. Only the geometric block-length window remains. -/

namespace StructuralNote.ThreeBlockLocalImprovement

open Real Filter Set Erdos1045.EventualExact FourierMultiplier FiniteBox
open ThreeBlockKernelMargin SolThreeBlockWord SolThreeBlockEnergy
open SolThreeBlockTransfer SolWordHamming SolIntegratedKernel
open DiscreteConvexBalance IntegerBalance FixedDualClassificationFinite
open scoped Topology
noncomputable section

theorem not_balanced_iff_gap {m a b c : ℕ} (hs : a + b + c = m) :
    ¬ BalancedAt (m / 3) a b c ↔
      b + 2 ≤ a ∨ a + 2 ≤ b ∨ c + 2 ≤ b ∨ b + 2 ≤ c ∨
        c + 2 ≤ a ∨ a + 2 ≤ c := by
  simp only [BalancedAt]
  omega

theorem actual_energy_le_B {m a b c : ℕ} (hm : 0 < m)
    (hp : 0 < a ∧ 0 < b ∧ 0 < c) (hs : a + b + c = m) :
    actualThreeBlockEnergy hm hp hs ≤ B hm := by
  exact energy_le_B hm (vertex_mem_box (amplitude_pos (by omega)).le _)

theorem deficit_eq {m a b c : ℕ} (hm : 0 < m)
    (hp : 0 < a ∧ 0 < b ∧ 0 < c) (hs : a + b + c = m) :
    deficit hm (threeBlockPattern hm hp hs) = B hm - actualThreeBlockEnergy hm hp hs := rfl

theorem two_site_improvement_of_strong_convexity {m a b c : ℕ} (hm : 0 < m)
    (hp : 0 < a ∧ 0 < b ∧ 0 < c) (hs : a + b + c = m)
    {α β κ : ℝ} (hκ : 0 ≤ κ)
    (hconv : ∀ r : ℤ, angle m r ∈ Icc α β →
      κ ≤ secondDifference (S (2 * m)) r)
    (ha : angle m a ∈ Icc α β) (hb : angle m b ∈ Icc α β)
    (hc : angle m c ∈ Icc α β) (hne : ¬ BalancedAt (m / 3) a b c) :
    ∃ a' b' c' : ℕ, ∃ hp' : 0 < a' ∧ 0 < b' ∧ 0 < c',
      ∃ hs' : a' + b' + c' = m,
        hamming (threeBlockPattern hm hp hs) (threeBlockPattern hm hp' hs') ≤ 2 ∧
        2 * κ ≤ actualThreeBlockEnergy hm hp' hs' - actualThreeBlockEnergy hm hp hs ∧
        0 ≤ deficit hm (threeBlockPattern hm hp' hs') ∧
        deficit hm (threeBlockPattern hm hp' hs') + 2 * κ ≤
          deficit hm (threeBlockPattern hm hp hs) := by
  let l : ℤ := min a (min b c)
  let u : ℤ := max a (max b c)
  have hl : α ≤ angle m l := by
    dsimp only [l]
    simp only [min_def]
    split_ifs <;> first | exact ha.1 | exact hb.1 | exact hc.1
  have hu : angle m u ≤ β := by
    dsimp only [u]
    simp only [max_def]
    split_ifs <;> first | exact ha.2 | exact hb.2 | exact hc.2
  have ha' : (a : ℤ) ∈ Icc l u := by dsimp [l, u]; constructor <;> omega
  have hb' : (b : ℤ) ∈ Icc l u := by dsimp [l, u]; constructor <;> omega
  have hc' : (c : ℤ) ∈ Icc l u := by dsimp [l, u]; constructor <;> omega
  obtain ⟨a', b', c', hp', hs', hh, hv⟩ :=
    exists_balancing_transfer_with_value_gain hm hp hs ((not_balanced_iff_gap hs).mp hne)
      (C := 3 * S (2 * m) 0) hκ (strong_convexity_on_span hconv hl hu) ha' hb' hc'
  have henergy : 2 * κ ≤
      actualThreeBlockEnergy hm hp' hs' - actualThreeBlockEnergy hm hp hs := by
    rw [actualThreeBlockEnergy_eq, actualThreeBlockEnergy_eq]
    dsimp only [threeBlockValue] at hv
    linarith only [hv]
  refine ⟨a', b', c', hp', hs', hh, henergy, ?_, ?_⟩
  · rw [deficit_eq]
    exact sub_nonneg.mpr (actual_energy_le_B hm hp' hs')
  · rw [deficit_eq, deficit_eq]
    linarith

/-- The interval and improvement constant are independent of the word and of
the order. This supplies the three-block alternative of Proposition 8.1. -/
theorem eventually_uniform_two_site_improvement :
    ∃ α β η : ℝ, 0 < α ∧ α < Real.pi / 4 ∧
      5 * Real.pi / 12 < β ∧ β < Real.pi / 2 ∧ 0 < η ∧
      ∀ᶠ m : ℕ in atTop, ∀ (hm : 0 < m) (a b c : ℕ)
        (hp : 0 < a ∧ 0 < b ∧ 0 < c) (hs : a + b + c = m),
        angle m a ∈ Icc α β → angle m b ∈ Icc α β → angle m c ∈ Icc α β →
        ¬ BalancedAt (m / 3) a b c →
        ∃ a' b' c' : ℕ, ∃ hp' : 0 < a' ∧ 0 < b' ∧ 0 < c',
          ∃ hs' : a' + b' + c' = m,
            hamming (threeBlockPattern hm hp hs) (threeBlockPattern hm hp' hs') ≤ 2 ∧
            η / (2 * m : ℕ) ^ 2 ≤
              actualThreeBlockEnergy hm hp' hs' - actualThreeBlockEnergy hm hp hs ∧
            0 ≤ deficit hm (threeBlockPattern hm hp' hs') ∧
            deficit hm (threeBlockPattern hm hp' hs') + η / (2 * m : ℕ) ^ 2 ≤
              deficit hm (threeBlockPattern hm hp hs) := by
  obtain ⟨α, β, κ, hα, hαlo, hβlo, hβhi, hκ, hevent⟩ :=
    exists_uniform_strong_convexity
  refine ⟨α, β, 2 * κ, hα, hαlo, hβlo, hβhi, by positivity, ?_⟩
  filter_upwards [hevent] with m hmarg hm a b c hp hs ha hb hc hne
  simpa only [mul_div_assoc] using two_site_improvement_of_strong_convexity
    hm hp hs (by positivity : 0 ≤ κ / (2 * m : ℕ) ^ 2) hmarg ha hb hc hne

end
end StructuralNote.ThreeBlockLocalImprovement
