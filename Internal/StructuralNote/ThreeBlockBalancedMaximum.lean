import StructuralNote.ThreeBlockLocalImprovement

/-! Exact balanced selection within the localized three-block family. The
finite-kernel conditions are discharged by the previously proved analytic bounds. -/

namespace StructuralNote.ThreeBlockBalancedMaximum

open Real Filter Set Erdos1045.EventualExact
open ThreeBlockKernelMargin ThreeBlockLocalImprovement SolThreeBlockEnergy
open SolIntegratedKernel DiscreteConvexBalance IntegerBalance
open scoped Topology
noncomputable section

theorem canonical_sum (m : ℕ) : m / 3 + (m + 1) / 3 + (m + 2) / 3 = m := by omega

theorem canonical_pos {m : ℕ} (hm : 3 ≤ m) :
    0 < m / 3 ∧ 0 < (m + 1) / 3 ∧ 0 < (m + 2) / 3 := by omega

theorem canonical_balanced (m : ℕ) :
    BalancedAt (m / 3) (m / 3 : ℕ) ((m + 1) / 3 : ℕ) ((m + 2) / 3 : ℕ) := by
  dsimp [BalancedAt]
  omega

def balancedEnergy (m : ℕ) (hm : 3 ≤ m) : ℝ :=
  actualThreeBlockEnergy (by omega : 0 < m) (canonical_pos hm) (canonical_sum m)

theorem balanced_sum_eq (f : ℤ → ℝ) {k a b c p q r : ℤ}
    (ha : BalancedAt k a b c) (hp : BalancedAt k p q r) (hs : a + b + c = p + q + r) :
    f a + f b + f c = f p + f q + f r := by
  rcases ha with ⟨ha, hb, hc⟩
  rcases hp with ⟨hp, hq, hr⟩
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hp with rfl | rfl <;>
    rcases hq with rfl | rfl <;> rcases hr with rfl | rfl <;> first | omega | ring

theorem energy_eq_of_balanced {m a b c : ℕ} (hm : 3 ≤ m)
    (hp : 0 < a ∧ 0 < b ∧ 0 < c) (hs : a + b + c = m)
    (hbal : BalancedAt (m / 3) a b c) :
    actualThreeBlockEnergy (by omega : 0 < m) hp hs = balancedEnergy m hm := by
  unfold balancedEnergy
  rw [actualThreeBlockEnergy_eq, actualThreeBlockEnergy_eq]
  have hsum : (a : ℤ) + b + c =
      (m / 3 : ℕ) + ((m + 1) / 3 : ℕ) + ((m + 2) / 3 : ℕ) := by
    exact_mod_cast hs.trans (canonical_sum m).symm
  have hh := balanced_sum_eq (S (2 * m)) hbal (canonical_balanced m) hsum
  linarith only [hh]

theorem canonical_cut_angles {m : ℕ} (hm : 12 ≤ m) :
    Real.pi / 4 ≤ angle m (m / 3 : ℕ) ∧
      angle m ((m / 3 : ℕ) + 1) ≤ 5 * Real.pi / 12 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlo : (m : ℝ) ≤ 4 * (m / 3 : ℕ) := by
    exact_mod_cast (show m ≤ 4 * (m / 3) by omega)
  have hhi : 12 * ((m / 3 : ℕ) + 1 : ℝ) ≤ 5 * m := by
    exact_mod_cast (show 12 * (m / 3 + 1) ≤ 5 * m by omega)
  have he (r : ℤ) : angle m r = (r : ℝ) * Real.pi / m := by
    dsimp [angle]
    push_cast
    ring
  simp only [he, Int.cast_natCast, Int.cast_add, Int.cast_one]
  constructor
  · apply (le_div_iff₀ hmR).2
    nlinarith [mul_le_mul_of_nonneg_right hlo pi_pos.le]
  · apply (div_le_iff₀ hmR).2
    nlinarith [mul_le_mul_of_nonneg_right hhi pi_pos.le]

/-- The canonical balanced word itself belongs to every enlarged window used
below, so the upper bound is attained within the compared family. -/
theorem canonical_angles {m : ℕ} (hm : 12 ≤ m) {α β : ℝ}
    (hα : α ≤ Real.pi / 4) (hβ : 5 * Real.pi / 12 ≤ β) :
    angle m (m / 3 : ℕ) ∈ Icc α β ∧
      angle m ((m + 1) / 3 : ℕ) ∈ Icc α β ∧
      angle m ((m + 2) / 3 : ℕ) ∈ Icc α β := by
  have hcut := canonical_cut_angles hm
  have hentry (r : ℕ) (hr : m / 3 ≤ r ∧ r ≤ m / 3 + 1) : angle m r ∈ Icc α β := by
    exact ⟨hα.trans (hcut.1.trans (angle_mono m (by exact_mod_cast hr.1))),
      ((angle_mono m (by exact_mod_cast hr.2)).trans hcut.2).trans hβ⟩
  exact ⟨hentry _ (by omega), hentry _ (by omega), hentry _ (by omega)⟩

theorem comparison_of_strong_convexity {m a b c : ℕ} (hm : 12 ≤ m)
    (hp : 0 < a ∧ 0 < b ∧ 0 < c) (hs : a + b + c = m)
    {α β κ : ℝ} (hα : α < Real.pi / 4) (hβ : 5 * Real.pi / 12 < β)
    (hκ : 0 ≤ κ)
    (hconv : ∀ r : ℤ, angle m r ∈ Icc α β →
      κ ≤ secondDifference (S (2 * m)) r)
    (ha : angle m a ∈ Icc α β) (hb : angle m b ∈ Icc α β)
    (hc : angle m c ∈ Icc α β) :
    actualThreeBlockEnergy (by omega : 0 < m) hp hs ≤ balancedEnergy m (by omega) ∧
    (¬ BalancedAt (m / 3) a b c →
      2 * κ ≤ balancedEnergy m (by omega) - actualThreeBlockEnergy (by omega : 0 < m) hp hs) := by
  let k : ℤ := (m / 3 : ℕ)
  let l : ℤ := min k (min a (min b c))
  let u : ℤ := max (k + 1) (max a (max b c))
  have hcut := canonical_cut_angles hm
  have hklow : α ≤ angle m k := hα.le.trans hcut.1
  have hkup : angle m (k + 1) ≤ β := hcut.2.trans hβ.le
  have hl : α ≤ angle m l := by
    dsimp only [l]
    simp only [min_def]
    split_ifs <;> first | exact hklow | exact ha.1 | exact hb.1 | exact hc.1
  have hu : angle m u ≤ β := by
    dsimp only [u]
    simp only [max_def]
    split_ifs <;> first | exact hkup | exact ha.2 | exact hb.2 | exact hc.2
  have hspan := strong_convexity_on_span hconv hl hu
  have hkl : l ≤ k := min_le_left _ _
  have hku : k + 1 ≤ u := by dsimp [u]; omega
  have ha' : (a : ℤ) ∈ Icc l u := by dsimp [l, u]; constructor <;> omega
  have hb' : (b : ℤ) ∈ Icc l u := by dsimp [l, u]; constructor <;> omega
  have hc' : (c : ℤ) ∈ Icc l u := by dsimp [l, u]; constructor <;> omega
  have hk : k = (m : ℤ) / 3 := by dsimp [k]
  have hbal := canonical_balanced m
  rw [← hk] at hbal
  have hsum : (a : ℤ) + b + c =
      (m / 3 : ℕ) + ((m + 1) / 3 : ℕ) + ((m + 2) / 3 : ℕ) := by
    exact_mod_cast hs.trans (canonical_sum m).symm
  constructor
  · have hh := three_point_convex_minimum (fun j hj hj' => hκ.trans (hspan j hj hj'))
      hkl hku ha' hb' hc' hbal hsum
    unfold balancedEnergy
    rw [actualThreeBlockEnergy_eq, actualThreeBlockEnergy_eq]
    linarith only [hh]
  · intro hne
    rw [← hk] at hne
    have hh := three_block_value_nonbalanced_gap (C := 3 * S (2 * m) 0)
      hκ hspan hkl hku ha' hb' hc' hbal hsum hne
    unfold balancedEnergy
    rw [actualThreeBlockEnergy_eq, actualThreeBlockEnergy_eq]
    dsimp only [threeBlockValue] at hh
    linarith only [hh]

/-- Exact maximum, equality classification, and a uniform gap inside the
localized three-block family. This does not classify arbitrary box words. -/
theorem eventually_balanced_maximum :
    ∃ α β η : ℝ, 0 < α ∧ α < Real.pi / 4 ∧
      5 * Real.pi / 12 < β ∧ β < Real.pi / 2 ∧ 0 < η ∧
      ∀ᶠ m : ℕ in atTop, ∀ (hm : 12 ≤ m) (a b c : ℕ)
        (hp : 0 < a ∧ 0 < b ∧ 0 < c) (hs : a + b + c = m),
        angle m a ∈ Icc α β → angle m b ∈ Icc α β → angle m c ∈ Icc α β →
        actualThreeBlockEnergy (by omega : 0 < m) hp hs ≤ balancedEnergy m (by omega) ∧
        (actualThreeBlockEnergy (by omega : 0 < m) hp hs = balancedEnergy m (by omega) ↔
          BalancedAt (m / 3) a b c) ∧
        (¬ BalancedAt (m / 3) a b c → η / (2 * m : ℕ) ^ 2 ≤
          balancedEnergy m (by omega) - actualThreeBlockEnergy (by omega : 0 < m) hp hs) := by
  obtain ⟨α, β, κ, hα, hαlo, hβlo, hβhi, hκ, hevent⟩ := exists_uniform_strong_convexity
  refine ⟨α, β, 2 * κ, hα, hαlo, hβlo, hβhi, by positivity, ?_⟩
  filter_upwards [hevent] with m hconv hm a b c hp hs ha hb hc
  have hh := comparison_of_strong_convexity hm hp hs hαlo hβlo
    (by positivity : 0 ≤ κ / (2 * m : ℕ) ^ 2) hconv ha hb hc
  refine ⟨hh.1, ⟨?_, energy_eq_of_balanced (by omega) hp hs⟩, ?_⟩
  · intro he
    by_contra hne
    have hg := hh.2 hne
    have hpos : 0 < κ / (2 * m : ℕ) ^ 2 := by positivity
    rw [he, sub_self] at hg
    linarith
  · intro hne
    simpa only [mul_div_assoc] using hh.2 hne

end
end StructuralNote.ThreeBlockBalancedMaximum
