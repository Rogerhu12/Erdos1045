import StructuralNote.FixedSchurWordDegrees
import Mathlib.Logic.Relation

/-! Connectivity of every antiperiodic selected-crossing graph. Each step in
the cyclic order is replaced by at most two actual diameter edges. -/

namespace StructuralNote.FixedSchurWordConnected

open Erdos1045 Erdos1045.EventualExact Filter
open FiniteBox FourierMultiplier SchurLift
open FixedSchurWordDegrees FixedSchurChartGeometry
open scoped Topology

noncomputable section

theorem advance_add {n : ℕ} (j : Fin n) (a b : ℕ) :
    cyclicAdvance (cyclicAdvance j a) b = cyclicAdvance j (a + b) := by
  apply Fin.ext
  simp only [cyclicAdvance, Nat.mod_add_mod, Nat.add_assoc]

theorem advance_half_next {m : ℕ} (hm : 0 < m) (j : Fin (2 * m)) :
    cyclicAdvance (halfTurn hm j) (m + 1) = cyclicAdvance j 1 := by
  change cyclicAdvance (cyclicAdvance j m) (m + 1) = _
  rw [advance_add]
  apply Fin.ext
  simp only [cyclicAdvance]
  have he : j.val + (m + (m + 1)) = (j.val + 1) + 2 * m := by omega
  rw [he, Nat.add_mod_right]

theorem matching_edge {m : ℕ} (hm : 2 ≤ m) (s : SignPattern (by omega : 0 < m))
    (j : Fin (2 * m)) : WordEdge (patternSign s) (halfTurn (by omega) j) j := by
  apply (wordEdge_iff hm _ (patternSign_antiperiodic s) _ _).2
  exact Or.inl rfl

theorem reach_next {m : ℕ} (hm : 2 ≤ m) (s : SignPattern (by omega : 0 < m))
    (j : Fin (2 * m)) :
    Relation.ReflTransGen (fun a b => WordEdge (patternSign s) b a) j (cyclicAdvance j 1) := by
  have hanti := patternSign_antiperiodic s
  rcases patternSign_is_sign s j with hj | hj
  · have hfirst := matching_edge hm s j
    have hsecond : WordEdge (patternSign s) (cyclicAdvance j 1) (halfTurn (by omega) j) := by
      apply (wordEdge_iff hm _ hanti _ _).2
      right; left
      exact ⟨(advance_half_next (by omega) j).symm, by rw [hanti, hj]⟩
    exact Relation.ReflTransGen.head hfirst (Relation.ReflTransGen.single hsecond)
  · have hfirst : WordEdge (patternSign s) (halfTurn (by omega) (cyclicAdvance j 1)) j := by
      apply (wordEdge_iff hm _ hanti _ _).2
      right; left
      refine ⟨?_, hj⟩
      change cyclicAdvance (cyclicAdvance j 1) m = _
      rw [advance_add, Nat.add_comm 1 m]
    have hsecond : WordEdge (patternSign s) (cyclicAdvance j 1)
        (halfTurn (by omega) (cyclicAdvance j 1)) := by
      have h := matching_edge hm s (halfTurn (by omega) (cyclicAdvance j 1))
      rwa [halfTurn_involutive (by omega) (cyclicAdvance j 1)] at h
    exact Relation.ReflTransGen.head hfirst (Relation.ReflTransGen.single hsecond)

theorem reach_advance {m : ℕ} (hm : 2 ≤ m) (s : SignPattern (by omega : 0 < m))
    (j : Fin (2 * m)) (k : ℕ) :
    Relation.ReflTransGen (fun a b => WordEdge (patternSign s) b a) j (cyclicAdvance j k) := by
  induction k with
  | zero =>
    have he : cyclicAdvance j 0 = j := by
      apply Fin.ext
      simp only [cyclicAdvance, Nat.add_zero, Nat.mod_eq_of_lt j.isLt]
    rw [he]
  | succ k ih =>
    have hn := reach_next hm s (cyclicAdvance j k)
    rw [advance_add] at hn
    exact ih.trans hn

/-- Connectedness of the complete selected-word diameter relation. -/
theorem word_connected {m : ℕ} (hm : 2 ≤ m) (s : SignPattern (by omega : 0 < m))
    (i j : Fin (2 * m)) :
    Relation.ReflTransGen (fun a b => WordEdge (patternSign s) b a) i j := by
  have h := reach_advance hm s i (cyclicForwardDistance i j)
  rwa [CommonFiberNonlocalFeasibility.cyclicAdvance_forwardDistance] at h

/-- The same connectivity statement for actual diameter edges on the chart. -/
theorem eventual_diameter_connected : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : SignPattern (by omega : 0 < m))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      CommonDomainClosure.InDomain (by omega) θ v → ∀ i j,
      Relation.ReflTransGen (fun a b =>
        ‖FixedSchurChart.configuration (by omega) s θ v b -
          FixedSchurChart.configuration (by omega) s θ v a‖ = 2) i j := by
  filter_upwards [eventual_geometric_properties] with m hgeo
  intro hm s θ v hdom i j
  have hg := (hgeo hm s θ v hdom).graph
  have he : (fun a b =>
      ‖FixedSchurChart.configuration (by omega) s θ v b -
        FixedSchurChart.configuration (by omega) s θ v a‖ = 2) =
        (fun a b => WordEdge (patternSign s) b a) := by
    funext a b
    exact propext (hg b a)
  rw [he]
  exact word_connected hm s i j

end
end StructuralNote.FixedSchurWordConnected
