import StructuralNote.CommonFiberBounds
import StructuralNote.CommonFiberGeometry

/-! Actual adjacent feasibility and exact selected-edge identities, uniformly
on the common energy domain. Nonlocal pair constraints are not asserted here. -/

namespace StructuralNote.CommonFiberAdjacent

open Erdos1045.EventualExact Complex
open FourierMultiplier FiniteFourierLift LensClosure
open CommonClosureEnergy CommonTangentialParameters CommonDomainClosure
open CommonFiberBounds CommonFiberGeometry
noncomputable section

def plusDistance {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ) (j : Fin m) : ℝ :=
  ‖configuration hm θ v σ ξ (successor (by omega) (halfIndex j)) -
    configuration hm θ v σ ξ (halfTurn hm (halfIndex j))‖

def minusDistance {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ) (j : Fin m) : ℝ :=
  ‖configuration hm θ v σ ξ (halfIndex j) -
    configuration hm θ v σ ξ (halfTurn hm (successor (by omega) (halfIndex j)))‖

def AdjacentGeometry {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ) : Prop :=
  (∀ j : Fin (2 * m), ‖configuration hm θ v σ ξ j -
    configuration hm θ v σ ξ (halfTurn hm j)‖ = 2) ∧
  ∀ j : Fin m, plusDistance hm θ v σ ξ j ≤ 2 ∧ minusDistance hm θ v σ ξ j ≤ 2 ∧
    (plusDistance hm θ v σ ξ j = 2 ↔ σ j = 1) ∧
    (minusDistance hm θ v σ ξ j = 2 ↔ σ j = -1)

theorem adjacent_geometry {m : ℕ} (hm : 8 ≤ m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ)
    (hdom : InDomain (by omega) θ v) (hσ : ∀ j, |σ j| ≤ 1)
    (hξ : ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2)
    (hz : closure (phase (by omega) θ) (fun j => 2 * Real.cos (halfAngle (by omega) θ j))
      σ (coordinates (by omega) v) ξ = 0)
    (horder : 10 * (CommonDomainRadius.logOrder (2 * m) : ℝ) + 1024 ≤ 2 * m) :
    AdjacentGeometry (by omega) θ v σ ξ := by
  refine ⟨matching_length (by omega) θ v σ ξ hdom.1 hz, ?_⟩
  intro j
  obtain ⟨hL, ht, hwidth⟩ := domain_lens_positive hm θ v hdom hξ horder j
  have hR : 0 < Lens.width (2 * Real.cos (halfAngle (by omega) θ j))
      (heightParameter (coordinates (by omega) v) ξ j) := lt_of_lt_of_le (by positivity) hwidth
  have hp := crossing_plus_squared (by omega) θ v σ ξ hdom.1 hz j
  have hn := crossing_minus_squared (by omega) θ v σ ξ hdom.1 hz j
  change plusDistance (by omega) θ v σ ξ j ^ 2 = _ at hp
  change minusDistance (by omega) θ v σ ξ j ^ 2 = _ at hn
  have hp0 : 0 ≤ plusDistance (by omega) θ v σ ξ j := norm_nonneg _
  have hn0 : 0 ≤ minusDistance (by omega) θ v σ ξ j := norm_nonneg _
  have hc := (Lens.normalized_constraints_iff hL.le ht hR).mpr (hσ j)
  refine ⟨by nlinarith only [hp, hc.1, hp0], by nlinarith only [hn, hc.2, hn0], ?_, ?_⟩
  · have he := Lens.plus_active_iff hL ht hR (hσ j)
    constructor
    · intro h
      apply he.mp
      nlinarith only [hp, h]
    · intro h
      have heq := he.mpr h
      nlinarith only [hp, heq, hp0]
  · have he := Lens.minus_active_iff hL ht hR (hσ j)
    constructor
    · intro h
      apply he.mp
      nlinarith only [hn, h]
    · intro h
      have heq := he.mpr h
      nlinarith only [hn, heq, hn0]

/-- Every actual common-domain parameter and every bounded word gives a closed
configuration with feasible adjacent crossings; endpoint words select exactly one. -/
theorem eventual_adjacent_geometry :
    ∃ m₀ : ℕ, ∀ (m : ℕ) (hm : m₀ + 128 ≤ m)
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ),
      InDomain (by omega) θ v → (∀ j, |σ j| ≤ 1) →
      ∃ ξ : ℂ, ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2 ∧
        closure (phase (by omega) θ) (fun j => 2 * Real.cos (halfAngle (by omega) θ j))
          σ (coordinates (by omega) v) ξ = 0 ∧ AdjacentGeometry (by omega) θ v σ ξ := by
  obtain ⟨Nr, hr⟩ := eventual_common_domain_root
  obtain ⟨No, ho⟩ := Filter.eventually_atTop.mp eventual_order_bound
  refine ⟨Nr + No, ?_⟩
  intro m hm θ v σ hdom hσ
  obtain ⟨ξ, hξ, _⟩ := hr m (by omega) θ v σ hdom hσ
  have horder := ho (2 * m) (by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at horder
  exact ⟨ξ, hξ.1, hξ.2, adjacent_geometry (by omega) θ v σ ξ hdom hσ hξ.1 hξ.2 horder⟩

theorem selected_other_strict {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ)
    (h : AdjacentGeometry hm θ v σ ξ) (j : Fin m) :
    (σ j = 1 → minusDistance hm θ v σ ξ j < 2) ∧
      (σ j = -1 → plusDistance hm θ v σ ξ j < 2) := by
  constructor
  · intro hs
    apply lt_of_le_of_ne (h.2 j).2.1
    intro he
    have hz := (h.2 j).2.2.2.mp he
    linarith
  · intro hs
    apply lt_of_le_of_ne (h.2 j).1
    intro he
    have hz := (h.2 j).2.2.1.mp he
    linarith

end
end StructuralNote.CommonFiberAdjacent
