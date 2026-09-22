import StructuralNote.FixedSchurDiameterCycle
import StructuralNote.FixedSchurThreeBlockDegrees
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-! Exact lengths of the three arcs in the nonleaf diameter cycle.

A negative sign block of length `r` gives an alternating walk with `r`
selected crossing edges and `r - 1` matching edges.  The construction below
lives in the actual selected-word graph and is then lifted to the graph
induced on nonleaves.
-/

namespace StructuralNote.FixedSchurCycleArcLengths

open Erdos1045.EventualExact FiniteBox FourierMultiplier SchurLift
open FixedSchurWordDegrees FixedSchurWordConnected FixedSchurSimpleGraph
open FixedSchurNonleafGraph FixedSchurDiameterCycle FixedSchurThreeBlockDegrees
open FixedSchurChartGeometry SolThreeBlockWord

noncomputable section

theorem advance_one_half {m : ℕ} (hm : 0 < m) (j : Fin (2 * m)) :
    cyclicAdvance j (m + 1) = halfTurn hm (cyclicAdvance j 1) := by
  apply Fin.ext
  simp only [cyclicAdvance, halfTurn, Nat.mod_add_mod]
  congr 1
  omega

theorem previous_advance_one {m : ℕ} (hm : 0 < m) (j : Fin (2 * m)) :
    previous (cyclicAdvance j 1) = j := by
  apply Fin.ext
  simp only [previous, cyclicAdvance, Nat.mod_add_mod]
  have he : j.val + 1 + (2 * m - 1) = j.val + 2 * m := by omega
  rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]

theorem advance_zero {m : ℕ} (j : Fin (2 * m)) :
    cyclicAdvance j 0 = j := by
  apply Fin.ext
  simp only [cyclicAdvance, Nat.add_zero, Nat.mod_eq_of_lt j.isLt]

theorem halfTurn_advance {m : ℕ} (hm : 0 < m) (j : Fin (2 * m)) (t : ℕ) :
    halfTurn hm (cyclicAdvance j t) = cyclicAdvance j (t + m) := by
  apply Fin.ext
  simp only [halfTurn, cyclicAdvance, Nat.mod_add_mod, Nat.add_assoc]

def ArcSupport {m : ℕ} (hm : 0 < m) (j : Fin (2 * m)) (r : ℕ)
    (x : Fin (2 * m)) : Prop :=
  (∃ t < r, x = cyclicAdvance j t) ∨
    ∃ t < r, x = halfTurn hm (cyclicAdvance j (t + 1))

private theorem negativeRun_nonleaf_walk_aux {m : ℕ} (hm : 2 ≤ m)
    (s : SignPattern (by omega : 0 < m)) (j : Fin (2 * m)) (r : ℕ)
    (hr : 0 < r) (hrm : r < m)
    (hneg : ∀ t < r, patternSign s (cyclicAdvance j t) = -1)
    (hafter : patternSign s (cyclicAdvance j r) = 1) :
    let S : Set (Fin (2 * m)) :=
      {x | (neighbors (patternSign s) x).card ≠ 1}
    let G := (graph hm (patternSign s)).induce S
    ∃ e : Fin (2 * m),
      ∃ hj : (neighbors (patternSign s) j).card ≠ 1,
        ∃ he : (neighbors (patternSign s) e).card ≠ 1,
          ∃ p : G.Walk ⟨j, hj⟩ ⟨e, he⟩,
            p.IsPath ∧
              (∀ x, x ∈ p.support ↔ ArcSupport (by omega) j r x.1) ∧
              e = halfTurn (by omega) (cyclicAdvance j r) ∧
              p.length = 2 * r - 1 := by
  induction r generalizing j with
  | zero => omega
  | succ r ih =>
      by_cases hr0 : r = 0
      · subst r
        let e := cyclicAdvance j (m + 1)
        have heq : e = halfTurn (by omega) (cyclicAdvance j 1) :=
          advance_one_half (by omega) j
        have hjneg : patternSign s j = -1 := by
          rw [← advance_zero j]
          exact hneg 0 (by omega)
        have hcross : (graph hm (patternSign s)).Adj j e := by
          change WordEdge (patternSign s) e j
          apply (wordEdge_iff hm _ (patternSign_antiperiodic s) e j).2
          exact Or.inr (Or.inl ⟨rfl, hjneg⟩)
        have hj : (neighbors (patternSign s) j).card ≠ 1 := by
          intro hleaf
          have hs := (degree_one_iff hm s j).1 hleaf
          linarith [hs.2, hjneg]
        have hend : (neighbors (patternSign s)
            (halfTurn (by omega) (cyclicAdvance j 1))).card ≠ 1 := by
          intro hleaf
          have hs := (degree_one_iff hm s _).1 hleaf
          have hv := patternSign_antiperiodic s (cyclicAdvance j 1)
          rw [hafter] at hv
          linarith [hs.2, hv]
        let S : Set (Fin (2 * m)) :=
          {x | (neighbors (patternSign s) x).card ≠ 1}
        let G := (graph hm (patternSign s)).induce S
        have hcross' : (graph hm (patternSign s)).Adj j
            (halfTurn (by omega) (cyclicAdvance j 1)) := by
          rw [← heq]
          exact hcross
        have hadj : G.Adj ⟨j, hj⟩
            ⟨halfTurn (by omega) (cyclicAdvance j 1), hend⟩ :=
          SimpleGraph.induce_adj.2 hcross'
        let p : G.Walk ⟨j, hj⟩
            ⟨halfTurn (by omega) (cyclicAdvance j 1), hend⟩ :=
          SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil
        refine ⟨halfTurn (by omega) (cyclicAdvance j 1), hj, hend, p, ?_, ?_, rfl, ?_⟩
        · exact hadj.isPath_toWalk
        · intro x
          constructor
          · intro hx
            have hxs : x = ⟨j, hj⟩ ∨
                x = ⟨halfTurn (by omega) (cyclicAdvance j 1), hend⟩ := by
              simpa only [p, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
                List.mem_cons, List.not_mem_nil, or_false] using hx
            rcases hxs with rfl | rfl
            · exact Or.inl ⟨0, by omega, (advance_zero j).symm⟩
            · exact Or.inr ⟨0, by omega, rfl⟩
          · intro hx
            rcases hx with ⟨t, ht, hval⟩ | ⟨t, ht, hval⟩
            · have ht0 : t = 0 := by omega
              subst t
              have hxj : x = ⟨j, hj⟩ := by
                apply Subtype.ext
                simpa only [advance_zero] using hval
              rw [hxj]
              simp [p]
            · have ht0 : t = 0 := by omega
              subst t
              have hxe : x =
                  ⟨halfTurn (by omega) (cyclicAdvance j 1), hend⟩ := by
                apply Subtype.ext
                exact hval
              rw [hxe]
              simp [p]
        · simp [p]
      · have hr' : 0 < r := Nat.pos_of_ne_zero hr0
        let j' := cyclicAdvance j 1
        have hneg' : ∀ t < r, patternSign s (cyclicAdvance j' t) = -1 := by
          intro t ht
          rw [show cyclicAdvance j' t = cyclicAdvance j (t + 1) by
            dsimp only [j']
            rw [advance_add]
            congr 1
            omega]
          exact hneg (t + 1) (by omega)
        have hafter' : patternSign s (cyclicAdvance j' r) = 1 := by
          rw [show cyclicAdvance j' r = cyclicAdvance j (r + 1) by
            dsimp only [j']
            rw [advance_add]
            congr 1
            omega]
          exact hafter
        obtain ⟨eend, hj', hend, p', hpath', hsupp', heend, hp'⟩ :=
          ih j' hr' (by omega) hneg' hafter'
        let e := cyclicAdvance j (m + 1)
        have heq : e = halfTurn (by omega) j' := by
          exact advance_one_half (by omega) j
        have hjneg : patternSign s j = -1 := by
          rw [← advance_zero j]
          exact hneg 0 (by omega)
        have hcross : (graph hm (patternSign s)).Adj j e := by
          change WordEdge (patternSign s) e j
          apply (wordEdge_iff hm _ (patternSign_antiperiodic s) e j).2
          exact Or.inr (Or.inl ⟨rfl, hjneg⟩)
        have hmatch : (graph hm (patternSign s)).Adj e j' := by
          change WordEdge (patternSign s) j' e
          rw [heq]
          exact wordEdge_symmetric hm _ (matching_edge hm s j')
        have hj : (neighbors (patternSign s) j).card ≠ 1 := by
          intro hleaf
          have hs := (degree_one_iff hm s j).1 hleaf
          linarith [hs.2, hjneg]
        have he : (neighbors (patternSign s) e).card ≠ 1 := by
          intro hleaf
          have hs := (degree_one_iff hm s e).1 hleaf
          have hprev : previous e = halfTurn (by omega) j := by
            rw [heq, previous_halfTurn (show 0 < m by omega),
              previous_advance_one (show 0 < m by omega)]
          have hv := patternSign_antiperiodic s j
          rw [hprev] at hs
          rw [hjneg] at hv
          norm_num at hv
          linarith [hs.1, hv, hjneg]
        let S : Set (Fin (2 * m)) :=
          {x | (neighbors (patternSign s) x).card ≠ 1}
        let G := (graph hm (patternSign s)).induce S
        have hadj₁ : G.Adj ⟨j, hj⟩ ⟨e, he⟩ :=
          SimpleGraph.induce_adj.2 hcross
        have hadj₂ : G.Adj ⟨e, he⟩ ⟨j', hj'⟩ :=
          SimpleGraph.induce_adj.2 hmatch
        have hstep : halfTurn (by omega) (cyclicAdvance j' r) =
            halfTurn (by omega) (cyclicAdvance j (r + 1)) := by
          congr 1
          dsimp only [j']
          rw [advance_add]
          congr 1
          omega
        have hshift (t : ℕ) : cyclicAdvance j' t = cyclicAdvance j (t + 1) := by
          dsimp only [j']
          rw [advance_add]
          congr 1
          omega
        have hturn (t : ℕ) :
            halfTurn (by omega) (cyclicAdvance j' (t + 1)) =
              cyclicAdvance j (m + t + 2) := by
          rw [hshift, halfTurn_advance]
          congr 1
          omega
        have hjnot : (⟨j, hj⟩ : S) ∉ p'.support := by
          intro hx
          rcases (hsupp' _).1 hx with ⟨t, ht, hval⟩ | ⟨t, ht, hval⟩
          · have hoff : cyclicAdvance j 0 = cyclicAdvance j (t + 1) := by
              calc
                cyclicAdvance j 0 = j := advance_zero j
                _ = cyclicAdvance j' t := hval
                _ = cyclicAdvance j (t + 1) := hshift t
            have heqoff := advance_injective_offset j
              (show 0 < 2 * m by omega) (show t + 1 < 2 * m by omega) hoff
            omega
          · have hoff : cyclicAdvance j 0 = cyclicAdvance j (m + t + 2) := by
              calc
                cyclicAdvance j 0 = j := advance_zero j
                _ = halfTurn (by omega) (cyclicAdvance j' (t + 1)) := hval
                _ = cyclicAdvance j (m + t + 2) := hturn t
            have heqoff := advance_injective_offset j
              (show 0 < 2 * m by omega) (show m + t + 2 < 2 * m by omega) hoff
            omega
        have henot : (⟨e, he⟩ : S) ∉ p'.support := by
          intro hx
          rcases (hsupp' _).1 hx with ⟨t, ht, hval⟩ | ⟨t, ht, hval⟩
          · have hoff : cyclicAdvance j (m + 1) = cyclicAdvance j (t + 1) := by
              calc
                cyclicAdvance j (m + 1) = e := rfl
                _ = cyclicAdvance j' t := hval
                _ = cyclicAdvance j (t + 1) := hshift t
            have heqoff := advance_injective_offset j
              (show m + 1 < 2 * m by omega) (show t + 1 < 2 * m by omega) hoff
            omega
          · have hoff : cyclicAdvance j (m + 1) = cyclicAdvance j (m + t + 2) := by
              calc
                cyclicAdvance j (m + 1) = e := rfl
                _ = halfTurn (by omega) (cyclicAdvance j' (t + 1)) := hval
                _ = cyclicAdvance j (m + t + 2) := hturn t
            have heqoff := advance_injective_offset j
              (show m + 1 < 2 * m by omega) (show m + t + 2 < 2 * m by omega) hoff
            omega
        have hje : (⟨j, hj⟩ : S) ≠ ⟨e, he⟩ := by
          intro h
          have hval : j = e := congrArg Subtype.val h
          apply (cyclicAdvance_ne_self j (show 0 < m + 1 by omega)
            (show m + 1 < 2 * m by omega))
          exact (show e = j from hval.symm)
        let p : G.Walk ⟨j, hj⟩ ⟨eend, hend⟩ :=
          SimpleGraph.Walk.cons hadj₁ (SimpleGraph.Walk.cons hadj₂ p')
        have hpath₂ : (SimpleGraph.Walk.cons hadj₂ p').IsPath :=
          hpath'.cons henot
        have hjnot₂ : (⟨j, hj⟩ : S) ∉
            (SimpleGraph.Walk.cons hadj₂ p').support := by
          simpa only [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] using
            And.intro hje hjnot
        have hpath : p.IsPath := by
          dsimp only [p]
          exact hpath₂.cons hjnot₂
        have hsupp : ∀ x, x ∈ p.support ↔
            ArcSupport (by omega) j (r + 1) x.1 := by
          intro x
          constructor
          · intro hx
            have hcases : x = ⟨j, hj⟩ ∨ x = ⟨e, he⟩ ∨ x ∈ p'.support := by
              simpa only [p, SimpleGraph.Walk.support_cons, List.mem_cons] using hx
            rcases hcases with rfl | rfl | hx'
            · exact Or.inl ⟨0, by omega, (advance_zero j).symm⟩
            · exact Or.inr ⟨0, by omega, heq⟩
            · rcases (hsupp' x).1 hx' with ⟨t, ht, hval⟩ | ⟨t, ht, hval⟩
              · exact Or.inl ⟨t + 1, by omega, hval.trans (hshift t)⟩
              · refine Or.inr ⟨t + 1, by omega, hval.trans ?_⟩
                congr 1
                rw [hshift]
          · intro hx
            rcases hx with ⟨t, ht, hval⟩ | ⟨t, ht, hval⟩
            · rcases t with _ | t
              · have hxj : x = ⟨j, hj⟩ := by
                  apply Subtype.ext
                  simpa only [advance_zero] using hval
                rw [hxj]
                simp [p]
              · have hx' : x ∈ p'.support := (hsupp' x).2 <|
                  Or.inl ⟨t, by omega, hval.trans (hshift t).symm⟩
                simp only [p, SimpleGraph.Walk.support_cons, List.mem_cons]
                exact Or.inr (Or.inr hx')
            · rcases t with _ | t
              · have hxe : x = ⟨e, he⟩ := by
                  apply Subtype.ext
                  exact hval.trans heq.symm
                rw [hxe]
                simp [p]
              · have hval' : x.1 =
                    halfTurn (by omega) (cyclicAdvance j' (t + 1)) := by
                  calc
                    x.1 = halfTurn (by omega) (cyclicAdvance j (t + 1 + 1)) := hval
                    _ = halfTurn (by omega) (cyclicAdvance j' (t + 1)) := by
                      congr 1
                      exact (hshift (t + 1)).symm
                have hx' : x ∈ p'.support := (hsupp' x).2 <|
                  Or.inr ⟨t, by omega, hval'⟩
                simp only [p, SimpleGraph.Walk.support_cons, List.mem_cons]
                exact Or.inr (Or.inr hx')
        refine ⟨eend, hj, hend, p, hpath, hsupp, heend.trans hstep, ?_⟩
        dsimp only [p]
        rw [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_cons, hp']
        omega

set_option maxHeartbeats 1000000 in
/-- A proper negative run gives a simple nonleaf path with exactly `2*r-1` edges. -/
theorem negativeRun_nonleaf_path {m : ℕ} (hm : 2 ≤ m)
    (s : SignPattern (by omega : 0 < m)) (j : Fin (2 * m)) (r : ℕ)
    (hr : 0 < r) (hrm : r < m)
    (hneg : ∀ t < r, patternSign s (cyclicAdvance j t) = -1)
    (hafter : patternSign s (cyclicAdvance j r) = 1) :
    let S : Set (Fin (2 * m)) :=
      {x | (neighbors (patternSign s) x).card ≠ 1}
    let G := (graph hm (patternSign s)).induce S
    ∃ hj : (neighbors (patternSign s) j).card ≠ 1,
      ∃ he : (neighbors (patternSign s)
          (halfTurn (by omega) (cyclicAdvance j r))).card ≠ 1,
        ∃ p : G.Walk ⟨j, hj⟩
            ⟨halfTurn (by omega) (cyclicAdvance j r), he⟩,
          p.IsPath ∧
            (∀ x, x ∈ p.support ↔ ArcSupport (by omega) j r x.1) ∧
            p.length = 2 * r - 1 := by
  obtain ⟨e, hj, he, p, hpath, hsupp, hend, hp⟩ :=
    negativeRun_nonleaf_walk_aux hm s j r hr hrm hneg hafter
  have htarget : (neighbors (patternSign s)
      (halfTurn (by omega) (cyclicAdvance j r))).card ≠ 1 := by
    rw [← hend]
    exact he
  refine ⟨hj, htarget, p.copy rfl (Subtype.ext hend), ?_, ?_, ?_⟩
  · exact (SimpleGraph.Walk.isPath_copy _ _ _).2 hpath
  · intro x
    rw [SimpleGraph.Walk.support_copy]
    exact hsupp x
  · simpa only [SimpleGraph.Walk.length_copy] using hp

theorem advance_val_no_wrap {m : ℕ} (j t : ℕ) (h : j + t < 2 * m) :
    (cyclicAdvance (⟨j, by omega⟩ : Fin (2 * m)) t).val = j + t := by
  simp only [cyclicAdvance, Nat.mod_eq_of_lt h]

theorem firstArc_support_bounds {m a b c : ℕ}
    (hp : 0 < a ∧ 0 < b ∧ 0 < c) (hs : a + b + c = m)
    (x : Fin (2 * m))
    : ArcSupport (by omega) (⟨m, by omega⟩ : Fin (2 * m)) a x ↔
      (m ≤ x.val ∧ x.val < m + a) ∨ (1 ≤ x.val ∧ x.val ≤ a) := by
  constructor
  · intro hx
    rcases hx with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · left
      rw [advance_val_no_wrap (m := m) m t (by omega)]
      omega
    · right
      have he : halfTurn (by omega)
          (cyclicAdvance (⟨m, by omega⟩ : Fin (2 * m)) (t + 1)) =
            (⟨t + 1, by omega⟩ : Fin (2 * m)) := by
        apply Fin.ext
        simp only [halfTurn, cyclicAdvance, Nat.mod_add_mod]
        have hsum : m + (t + 1) + m = t + 1 + 2 * m := by omega
        rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [he]
      change 1 ≤ t + 1 ∧ t + 1 ≤ a
      omega
  · rintro (hx | hx)
    · exact Or.inl ⟨x.val - m, by omega, by
        apply Fin.ext
        rw [advance_val_no_wrap (m := m) m (x.val - m) (by omega)]
        omega⟩
    · exact Or.inr ⟨x.val - 1, by omega, by
        apply Fin.ext
        simp only [halfTurn, cyclicAdvance, Nat.mod_add_mod]
        have hsum : m + (x.val - 1 + 1) + m = x.val + 2 * m := by omega
        rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt x.isLt]⟩

theorem secondArc_support_bounds {m a b c : ℕ}
    (hp : 0 < a ∧ 0 < b ∧ 0 < c) (hs : a + b + c = m)
    (x : Fin (2 * m))
    : ArcSupport (by omega) (⟨a, by omega⟩ : Fin (2 * m)) b x ↔
      (a ≤ x.val ∧ x.val < a + b) ∨
        (m + a + 1 ≤ x.val ∧ x.val ≤ m + a + b) := by
  constructor
  · intro hx
    rcases hx with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · left
      rw [advance_val_no_wrap (m := m) a t (by omega)]
      omega
    · right
      have he : halfTurn (by omega)
          (cyclicAdvance (⟨a, by omega⟩ : Fin (2 * m)) (t + 1)) =
            (⟨m + a + t + 1, by omega⟩ : Fin (2 * m)) := by
        apply Fin.ext
        simp only [halfTurn, cyclicAdvance, Nat.mod_add_mod]
        rw [Nat.mod_eq_of_lt (by omega : a + (t + 1) + m < 2 * m)]
        omega
      rw [he]
      change m + a + 1 ≤ m + a + t + 1 ∧ m + a + t + 1 ≤ m + a + b
      omega
  · rintro (hx | hx)
    · exact Or.inl ⟨x.val - a, by omega, by
        apply Fin.ext
        rw [advance_val_no_wrap (m := m) a (x.val - a) (by omega)]
        omega⟩
    · exact Or.inr ⟨x.val - (m + a + 1), by omega, by
        apply Fin.ext
        simp only [halfTurn, cyclicAdvance, Nat.mod_add_mod]
        rw [Nat.mod_eq_of_lt (by omega :
          a + (x.val - (m + a + 1) + 1) + m < 2 * m)]
        omega⟩

theorem thirdArc_support_bounds {m a b c : ℕ}
    (hp : 0 < a ∧ 0 < b ∧ 0 < c) (hs : a + b + c = m)
    (x : Fin (2 * m))
    : ArcSupport (by omega) (⟨m + a + b, by omega⟩ : Fin (2 * m)) c x ↔
      (m + a + b ≤ x.val ∧ x.val < 2 * m) ∨
        (a + b + 1 ≤ x.val ∧ x.val ≤ m) := by
  constructor
  · intro hx
    rcases hx with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · left
      rw [advance_val_no_wrap (m := m) (m + a + b) t (by omega)]
      omega
    · right
      have he : halfTurn (by omega)
          (cyclicAdvance (⟨m + a + b, by omega⟩ : Fin (2 * m)) (t + 1)) =
            (⟨a + b + t + 1, by omega⟩ : Fin (2 * m)) := by
        apply Fin.ext
        simp only [halfTurn, cyclicAdvance, Nat.mod_add_mod]
        have hsum : m + a + b + (t + 1) + m =
            a + b + t + 1 + 2 * m := by omega
        rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [he]
      change a + b + 1 ≤ a + b + t + 1 ∧ a + b + t + 1 ≤ m
      omega
  · rintro (hx | hx)
    · exact Or.inl ⟨x.val - (m + a + b), by omega, by
        apply Fin.ext
        rw [advance_val_no_wrap (m := m) (m + a + b)
          (x.val - (m + a + b)) (by omega)]
        omega⟩
    · exact Or.inr ⟨x.val - (a + b + 1), by omega, by
        apply Fin.ext
        simp only [halfTurn, cyclicAdvance, Nat.mod_add_mod]
        have hsum : m + a + b + (x.val - (a + b + 1) + 1) + m =
            x.val + 2 * m := by omega
        rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt x.isLt]⟩

/-- For a three-block word, the three exact branch-to-branch walks in the
nonleaf cycle have lengths `2*a-1`, `2*b-1`, and `2*c-1`. -/
theorem threeBlock_nonleaf_arc_lengths {m a b c : ℕ} (hm : 2 ≤ m)
    (hp : 0 < a ∧ 0 < b ∧ 0 < c) (hs : a + b + c = m) :
    let s := threeBlockPattern (by omega) hp hs
    let S : Set (Fin (2 * m)) :=
      {x | (neighbors (patternSign s) x).card ≠ 1}
    let G := (graph hm (patternSign s)).induce S
    let A : Fin (2 * m) := ⟨a, by omega⟩
    let B : Fin (2 * m) := ⟨m, by omega⟩
    let C : Fin (2 * m) := ⟨m + a + b, by omega⟩
    ∃ hA : (neighbors (patternSign s) A).card ≠ 1,
      ∃ hB : (neighbors (patternSign s) B).card ≠ 1,
        ∃ hC : (neighbors (patternSign s) C).card ≠ 1,
          (∃ p : G.Walk ⟨B, hB⟩ ⟨A, hA⟩,
            p.IsPath ∧ (∀ x, x ∈ p.support ↔ ArcSupport (by omega) B a x.1) ∧
              p.length = 2 * a - 1) ∧
          (∃ p : G.Walk ⟨A, hA⟩ ⟨C, hC⟩,
            p.IsPath ∧ (∀ x, x ∈ p.support ↔ ArcSupport (by omega) A b x.1) ∧
              p.length = 2 * b - 1) ∧
          (∃ p : G.Walk ⟨C, hC⟩ ⟨B, hB⟩,
            p.IsPath ∧ (∀ x, x ∈ p.support ↔ ArcSupport (by omega) C c x.1) ∧
              p.length = 2 * c - 1) := by
  dsimp only
  let s := threeBlockPattern (by omega) hp hs
  let A : Fin (2 * m) := ⟨a, by omega⟩
  let B : Fin (2 * m) := ⟨m, by omega⟩
  let C : Fin (2 * m) := ⟨m + a + b, by omega⟩
  have hA3 : (neighbors (patternSign s) A).card = 3 := by
    apply (branch_iff hm hp hs A).2
    exact Or.inl rfl
  have hB3 : (neighbors (patternSign s) B).card = 3 := by
    apply (branch_iff hm hp hs B).2
    exact Or.inr (Or.inl rfl)
  have hC3 : (neighbors (patternSign s) C).card = 3 := by
    apply (branch_iff hm hp hs C).2
    exact Or.inr (Or.inr rfl)
  have hA : (neighbors (patternSign s) A).card ≠ 1 := by omega
  have hB : (neighbors (patternSign s) B).card ≠ 1 := by omega
  have hC : (neighbors (patternSign s) C).card ≠ 1 := by omega
  have hnegA : ∀ t < a, patternSign s (cyclicAdvance B t) = -1 := by
    intro t ht
    rw [patternSign_threeBlockPattern, raw_formula hp hs]
    have hv : (cyclicAdvance B t).val = m + t := by
      exact advance_val_no_wrap (m := m) m t (by omega)
    rw [hv]
    split_ifs <;> norm_num <;> omega
  have hafterA : patternSign s (cyclicAdvance B a) = 1 := by
    rw [patternSign_threeBlockPattern, raw_formula hp hs]
    have hv : (cyclicAdvance B a).val = m + a := by
      exact advance_val_no_wrap (m := m) m a (by omega)
    rw [hv]
    split_ifs <;> norm_num <;> omega
  have hnegB : ∀ t < b, patternSign s (cyclicAdvance A t) = -1 := by
    intro t ht
    rw [patternSign_threeBlockPattern, raw_formula hp hs]
    have hv : (cyclicAdvance A t).val = a + t := by
      exact advance_val_no_wrap (m := m) a t (by omega)
    rw [hv]
    split_ifs <;> norm_num <;> omega
  have hafterB : patternSign s (cyclicAdvance A b) = 1 := by
    rw [patternSign_threeBlockPattern, raw_formula hp hs]
    have hv : (cyclicAdvance A b).val = a + b := by
      exact advance_val_no_wrap (m := m) a b (by omega)
    rw [hv]
    split_ifs <;> norm_num <;> omega
  have hnegC : ∀ t < c, patternSign s (cyclicAdvance C t) = -1 := by
    intro t ht
    rw [patternSign_threeBlockPattern, raw_formula hp hs]
    have hv : (cyclicAdvance C t).val = m + a + b + t := by
      exact advance_val_no_wrap (m := m) (m + a + b) t (by omega)
    rw [hv]
    split_ifs <;> norm_num <;> omega
  have hafterC : patternSign s (cyclicAdvance C c) = 1 := by
    have he : cyclicAdvance C c = (⟨0, by omega⟩ : Fin (2 * m)) := by
      apply Fin.ext
      simp only [C, cyclicAdvance]
      rw [show m + a + b + c = 2 * m by omega, Nat.mod_self]
    rw [he, patternSign_threeBlockPattern]
    simp only [raw_formula hp hs, if_pos hp.1]
  obtain ⟨hB', hA', pA, hpathA, hsuppA, hpA⟩ :=
    negativeRun_nonleaf_path hm s B a hp.1 (by omega) hnegA hafterA
  obtain ⟨hA'', hC', pB, hpathB, hsuppB, hpB⟩ :=
    negativeRun_nonleaf_path hm s A b hp.2.1 (by omega) hnegB hafterB
  obtain ⟨hC'', hB'', pC, hpathC, hsuppC, hpC⟩ :=
    negativeRun_nonleaf_path hm s C c hp.2.2 (by omega) hnegC hafterC
  have hendA : halfTurn (by omega) (cyclicAdvance B a) = A := by
    apply Fin.ext
    simp only [B, A, cyclicAdvance, halfTurn, Nat.mod_add_mod]
    have he : m + a + m = a + 2 * m := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hendB : halfTurn (by omega) (cyclicAdvance A b) = C := by
    apply Fin.ext
    simp only [A, C, cyclicAdvance, halfTurn, Nat.mod_add_mod]
    rw [Nat.mod_eq_of_lt (by omega : a + b + m < 2 * m)]
    omega
  have hendC : halfTurn (by omega) (cyclicAdvance C c) = B := by
    rw [show cyclicAdvance C c = (⟨0, by omega⟩ : Fin (2 * m)) by
      apply Fin.ext
      simp only [C, cyclicAdvance]
      rw [show m + a + b + c = 2 * m by omega, Nat.mod_self]]
    apply Fin.ext
    simp only [halfTurn, B, Nat.zero_add, Nat.mod_eq_of_lt (by omega : m < 2 * m)]
  refine ⟨hA, hB, hC, ?_, ?_, ?_⟩
  · exact ⟨pA.copy (Subtype.ext rfl) (Subtype.ext hendA),
      (SimpleGraph.Walk.isPath_copy _ _ _).2 hpathA, (fun x => by
        rw [SimpleGraph.Walk.support_copy]
        exact hsuppA x), by
        simpa only [SimpleGraph.Walk.length_copy] using hpA⟩
  · exact ⟨pB.copy (Subtype.ext rfl) (Subtype.ext hendB),
      (SimpleGraph.Walk.isPath_copy _ _ _).2 hpathB, (fun x => by
        rw [SimpleGraph.Walk.support_copy]
        exact hsuppB x), by
        simpa only [SimpleGraph.Walk.length_copy] using hpB⟩
  · exact ⟨pC.copy (Subtype.ext rfl) (Subtype.ext hendC),
      (SimpleGraph.Walk.isPath_copy _ _ _).2 hpathC, (fun x => by
        rw [SimpleGraph.Walk.support_copy]
        exact hsuppC x), by
        simpa only [SimpleGraph.Walk.length_copy] using hpC⟩

end
end StructuralNote.FixedSchurCycleArcLengths
