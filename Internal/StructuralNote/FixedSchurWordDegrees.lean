import StructuralNote.FixedSchurChartGeometry

/-! The exact vertex degrees of the diameter graph, derived from its actual
cyclic-offset edge relation. -/

namespace StructuralNote.FixedSchurWordDegrees

open Erdos1045 Erdos1045.EventualExact Filter
open FiniteBox FourierMultiplier
open FixedSchurOffsetGeometry FixedSchurChartGeometry
open scoped BigOperators Topology

noncomputable section

def previous {m : ℕ} (j : Fin (2 * m)) : Fin (2 * m) :=
  cyclicAdvance j (2 * m - 1)

def neighbors {m : ℕ} (σ : Fin (2 * m) → ℝ) (j : Fin (2 * m)) : Finset (Fin (2 * m)) := by
  classical
  exact Finset.univ.filter (fun i => WordEdge σ i j)

theorem advance_injective_offset {n : ℕ} (j : Fin n) {a b : ℕ}
    (ha : a < n) (hb : b < n) (h : cyclicAdvance j a = cyclicAdvance j b) : a = b := by
  have he := congrArg (cyclicForwardDistance j) h
  simpa only [cyclicForwardDistance_advance j ha, cyclicForwardDistance_advance j hb] using he

theorem previous_crossing {m : ℕ} (hm : 2 ≤ m) (j : Fin (2 * m)) :
    cyclicAdvance j (m - 1) = halfTurn (by omega) (previous j) := by
  apply Fin.ext
  simp only [cyclicAdvance, halfTurn, previous, Nat.mod_add_mod]
  have he : j.val + (2 * m - 1) + m = (j.val + (m - 1)) + 2 * m := by omega
  rw [he, Nat.add_mod_right]

theorem wordEdge_iff {m : ℕ} (hm : 2 ≤ m) (σ : Fin (2 * m) → ℝ)
    (hσ : Antiperiodic (by omega) σ) (i j : Fin (2 * m)) :
    WordEdge σ i j ↔
      i = cyclicAdvance j m ∨
      (i = cyclicAdvance j (m + 1) ∧ σ j = -1) ∨
      (i = cyclicAdvance j (m - 1) ∧ σ (previous j) = 1) := by
  have hback : σ (cyclicAdvance j (m - 1)) = -σ (previous j) := by
    rw [previous_crossing hm, hσ]
  have he (r : ℕ) (hr : r < 2 * m) :
      cyclicForwardDistance j i = r ↔ i = cyclicAdvance j r := by
    constructor
    · intro h
      rw [← h, CommonFiberNonlocalFeasibility.cyclicAdvance_forwardDistance]
    · rintro rfl
      exact cyclicForwardDistance_advance j hr
  unfold WordEdge OffsetEdge
  constructor
  · rintro (h | ⟨h, hs⟩ | ⟨h, hs⟩)
    · exact Or.inl ((he m (by omega)).1 h)
    · exact Or.inr (Or.inl ⟨(he (m + 1) (by omega)).1 h, hs⟩)
    · right; right
      refine ⟨(he (m - 1) (by omega)).1 h, ?_⟩
      rw [h, hback] at hs
      linarith
  · rintro (h | ⟨h, hs⟩ | ⟨h, hs⟩)
    · exact Or.inl ((he m (by omega)).2 h)
    · exact Or.inr (Or.inl ⟨(he (m + 1) (by omega)).2 h, hs⟩)
    · right; right
      have hd := (he (m - 1) (by omega)).2 h
      refine ⟨hd, ?_⟩
      rw [hd, hback, hs]

theorem neighbors_eq {m : ℕ} (hm : 2 ≤ m) (σ : Fin (2 * m) → ℝ)
    (hσ : Antiperiodic (by omega) σ) (j : Fin (2 * m)) :
    neighbors σ j = insert (cyclicAdvance j m)
      ((if σ j = -1 then {cyclicAdvance j (m + 1)} else ∅) ∪
        (if σ (previous j) = 1 then {cyclicAdvance j (m - 1)} else ∅)) := by
  classical
  ext i
  simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and, wordEdge_iff hm σ hσ,
    Finset.mem_insert, Finset.mem_union]
  by_cases hnext : σ j = -1 <;> by_cases hprev : σ (previous j) = 1 <;> simp [hnext, hprev]

/-- Formula (7.16), with the two indicator terms in the manuscript order. -/
theorem neighbors_card {m : ℕ} (hm : 2 ≤ m) (σ : Fin (2 * m) → ℝ)
    (hσ : Antiperiodic (by omega) σ) (j : Fin (2 * m)) :
    (neighbors σ j).card = 1 + (if σ (previous j) = 1 then 1 else 0) +
      (if σ j = -1 then 1 else 0) := by
  classical
  have hmn : cyclicAdvance j m ≠ cyclicAdvance j (m + 1) := by
    intro h; have := advance_injective_offset j (by omega) (by omega) h; omega
  have hmp : cyclicAdvance j m ≠ cyclicAdvance j (m - 1) := by
    intro h; have := advance_injective_offset j (by omega) (by omega) h; omega
  have hnp : cyclicAdvance j (m + 1) ≠ cyclicAdvance j (m - 1) := by
    intro h; have := advance_injective_offset j (by omega) (by omega) h; omega
  rw [neighbors_eq hm σ hσ]
  by_cases hnext : σ j = -1 <;> by_cases hprev : σ (previous j) = 1 <;>
    simp [hnext, hprev, hmn, hmp, hnp]

theorem degree_one_iff {m : ℕ} (hm : 2 ≤ m) (s : SignPattern (by omega : 0 < m))
    (j : Fin (2 * m)) :
    (neighbors (patternSign s) j).card = 1 ↔
      patternSign s (previous j) = -1 ∧ patternSign s j = 1 := by
  rw [neighbors_card hm _ (patternSign_antiperiodic s)]
  rcases patternSign_is_sign s (previous j) with hp | hp <;>
    rcases patternSign_is_sign s j with hj | hj <;> norm_num [hp, hj]

theorem degree_three_iff {m : ℕ} (hm : 2 ≤ m) (s : SignPattern (by omega : 0 < m))
    (j : Fin (2 * m)) :
    (neighbors (patternSign s) j).card = 3 ↔
      patternSign s (previous j) = 1 ∧ patternSign s j = -1 := by
  rw [neighbors_card hm _ (patternSign_antiperiodic s)]
  rcases patternSign_is_sign s (previous j) with hp | hp <;>
    rcases patternSign_is_sign s j with hj | hj <;> norm_num [hp, hj]

theorem previous_halfTurn {m : ℕ} (hm : 0 < m) (j : Fin (2 * m)) :
    previous (halfTurn hm j) = halfTurn hm (previous j) := by
  apply Fin.ext
  simp only [previous, cyclicAdvance, halfTurn, Nat.mod_add_mod]
  congr 1
  omega

/-- Each leaf is joined by its matching diameter to a degree-three vertex. -/
theorem leaf_partner_degree_three {m : ℕ} (hm : 2 ≤ m)
    (s : SignPattern (by omega : 0 < m)) (j : Fin (2 * m))
    (hj : (neighbors (patternSign s) j).card = 1) :
    (neighbors (patternSign s) (halfTurn (by omega) j)).card = 3 := by
  obtain ⟨hp, hn⟩ := (degree_one_iff hm s j).1 hj
  apply (degree_three_iff hm s _).2
  rw [previous_halfTurn, patternSign_antiperiodic, patternSign_antiperiodic, hp, hn]
  norm_num

/-- The same count for the actual geometric configuration, not just its word. -/
theorem eventual_diameter_neighbor_count : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : SignPattern (by omega : 0 < m))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      CommonDomainClosure.InDomain (by omega) θ v → ∀ j,
      (Finset.univ.filter (fun i =>
        ‖FixedSchurChart.configuration (by omega) s θ v i -
          FixedSchurChart.configuration (by omega) s θ v j‖ = 2)).card =
        1 + (if patternSign s (previous j) = 1 then 1 else 0) +
          (if patternSign s j = -1 then 1 else 0) := by
  filter_upwards [eventual_geometric_properties] with m hgeo
  intro hm s θ v hdom j
  have hg := (hgeo hm s θ v hdom).graph
  have he : (Finset.univ.filter (fun i =>
      ‖FixedSchurChart.configuration (by omega) s θ v i -
        FixedSchurChart.configuration (by omega) s θ v j‖ = 2)) =
        neighbors (patternSign s) j := by
    classical
    ext i
    simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hg i j
  rw [he]
  exact neighbors_card hm _ (patternSign_antiperiodic s) j

end
end StructuralNote.FixedSchurWordDegrees
