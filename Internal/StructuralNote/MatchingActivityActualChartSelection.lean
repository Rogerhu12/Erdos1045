import StructuralNote.MatchingActivityActualChart
import StructuralNote.SolWordFlips

/-! The physical active crossing at each matching site determines an actual
antiperiodic sign pattern.  No sign is imported from the corrected polar
center. -/

namespace StructuralNote.MatchingActivityActualChartSelection

open Erdos1045 Erdos1045.EventualExact Complex
open FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum FiniteBox
open CommonClosureEnergy CommonTangentialParameters CommonFiberGeometry
open MatchingActivityRadialGeometry MatchingActivityCrossingExclusivity
open MatchingActivityRadialClosure
open FixedSchurEdgeGeometry
open MatchingActivityActualChart
open scoped BigOperators
noncomputable section

/-- The sign selected by the active physical crossing in the first half. -/
def activeHalfSign {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (r : Fin m → ℝ) (C : Fin (2 * m) → ℂ) (i : Fin m) : ℝ :=
  if ‖plusCrossingVector hm θ r C i‖ = 2 then 1 else -1

/-- Extend the physical first-half choices antiperiodically. -/
def activeIndex {m : ℕ} (hm : 0 < m) (j : Fin (2 * m)) : Fin m :=
  ⟨j.val % m, Nat.mod_lt _ hm⟩

theorem activeIndex_halfTurn {m : ℕ} (hm : 0 < m) (j : Fin (2 * m)) :
    activeIndex hm (halfTurn hm j) = activeIndex hm j := by
  apply Fin.ext
  exact StructuralNote.SolWordFlips.halfTurn_mod hm j

def activeRaw {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (r : Fin m → ℝ) (C : Fin (2 * m) → ℂ) (j : Fin (2 * m)) : ℝ :=
  if j.val < m then
    activeHalfSign hm θ r C (activeIndex hm j)
  else
    -activeHalfSign hm θ r C (activeIndex hm j)

theorem activeRaw_is_sign {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (r : Fin m → ℝ) (C : Fin (2 * m) → ℂ) :
    IsSignVector (activeRaw hm θ r C) := by
  intro j
  unfold activeRaw activeHalfSign
  split <;> split <;> simp

theorem activeRaw_antiperiodic {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (r : Fin m → ℝ) (C : Fin (2 * m) → ℂ) :
    Antiperiodic hm (activeRaw hm θ r C) := by
  intro j
  unfold activeRaw
  rw [activeIndex_halfTurn]
  by_cases hj : j.val < m
  · have hh : ¬(halfTurn hm j).val < m := by
      simpa using (halfTurn_lt_iff hm j).not.mpr (not_not.mpr hj)
    simp [hj, hh]
  · have hh : (halfTurn hm j).val < m := (halfTurn_lt_iff hm j).2 hj
    simp [hj, hh]

/-- The finite sign word selected by the actual physical crossing activity. -/
def activePattern {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (r : Fin m → ℝ) (C : Fin (2 * m) → ℂ) : SignPattern hm :=
  encodeSign (activeRaw hm θ r C) (activeRaw_is_sign hm θ r C)
    (activeRaw_antiperiodic hm θ r C)

@[simp] theorem patternSign_activePattern {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (r : Fin m → ℝ) (C : Fin (2 * m) → ℂ)
    (j : Fin (2 * m)) :
    patternSign (activePattern hm θ r C) j = activeRaw hm θ r C j := by
  rw [activePattern, patternSign_encodeSign]

@[simp] theorem activeRaw_halfIndex {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (r : Fin m → ℝ) (C : Fin (2 * m) → ℂ)
    (i : Fin m) :
    activeRaw hm θ r C (CommonClosureEnergy.halfIndex i) =
      activeHalfSign hm θ r C i := by
  simp [activeRaw, CommonClosureEnergy.halfIndex, i.isLt,
    activeIndex, Nat.mod_eq_of_lt i.isLt]

theorem crossingVector_halfTurn_neg {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (C : Fin (2 * m) → ℂ)
    (σ : Fin (2 * m) → ℝ)
    (hθ : HalfPeriodic (by omega) (fun j => (θ j : ℂ)))
    (hC : HalfPeriodic (by omega) C)
    (hσ : Antiperiodic (by omega) σ) (j : Fin (2 * m)) :
    crossingVector hm θ C σ (halfTurn (by omega) j) =
      -crossingVector hm θ C σ j := by
  unfold crossingVector
  rw [diameterVector_halfTurn (by omega) θ hθ,
    ← halfTurn_successor,
    diameterVector_halfTurn (by omega) θ hθ,
    hC (successor (by omega) j), hC j, hσ j]
  push_cast
  ring

/-- On the first half, the pattern selected from the actual crossing activity
selects a crossing of length two. -/
theorem selected_crossing_halfIndex {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (r : Fin m → ℝ) (C : Fin (2 * m) → ℂ)
    (hr : ∀ i, r i = 1)
    (hactive : ∀ i : Fin m,
      (‖plusCrossingVector (by omega) θ r C i‖ = 2 ∧
        ‖minusCrossingVector (by omega) θ r C i‖ < 2) ∨
      (‖plusCrossingVector (by omega) θ r C i‖ < 2 ∧
        ‖minusCrossingVector (by omega) θ r C i‖ = 2))
    (i : Fin m) :
    ‖crossingVector hm θ (centerZero C)
      (patternSign (activePattern (by omega) θ r C))
      (CommonClosureEnergy.halfIndex i)‖ = 2 := by
  have hsum := weighted_diameter_sum (show 0 < m by omega) θ r i
  rw [radiusFull_halfIndex, radiusFull_next, hr i,
    hr (nextIndex (by omega) i)] at hsum
  simp only [Complex.ofReal_one, one_mul] at hsum
  unfold crossingVector
  rw [patternSign_activePattern, activeRaw_halfIndex]
  rcases hactive i with hp | hmns
  · have hs : activeHalfSign (by omega) θ r C i = 1 := by
      unfold activeHalfSign
      rw [if_pos hp.1]
    rw [hs]
    simp only [Complex.ofReal_one, one_mul]
    have hd : centerZero C (successor (by omega) (CommonClosureEnergy.halfIndex i)) -
        centerZero C (CommonClosureEnergy.halfIndex i) =
        C (successor (by omega) (CommonClosureEnergy.halfIndex i)) -
          C (CommonClosureEnergy.halfIndex i) := by
      simp only [centerZero]
      ring
    rw [hd, hsum]
    simpa only [plusCrossingVector, difference] using hp.1
  · have hs : activeHalfSign (by omega) θ r C i = -1 := by
      unfold activeHalfSign
      rw [if_neg (ne_of_lt hmns.1)]
    rw [hs]
    norm_num
    have hd : centerZero C (CommonClosureEnergy.halfIndex i) -
        centerZero C (successor (by omega) (CommonClosureEnergy.halfIndex i)) =
        C (CommonClosureEnergy.halfIndex i) -
          C (successor (by omega) (CommonClosureEnergy.halfIndex i)) := by
      simp only [centerZero]
      ring
    rw [hd, hsum]
    rw [show C (CommonClosureEnergy.halfIndex i) -
        C (successor (by omega) (CommonClosureEnergy.halfIndex i)) =
        -(C (successor (by omega) (CommonClosureEnergy.halfIndex i)) -
          C (CommonClosureEnergy.halfIndex i)) by ring]
    simpa only [minusCrossingVector, difference, sub_eq_add_neg] using hmns.2

/-- The actual sign pattern selects a saturated crossing at every full-period
site. -/
theorem selected_crossing_all {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (r : Fin m → ℝ) (C : Fin (2 * m) → ℂ)
    (hθ : HalfPeriodic (by omega) (fun j => (θ j : ℂ)))
    (hC : HalfPeriodic (by omega) C)
    (hr : ∀ i, r i = 1)
    (hactive : ∀ i : Fin m,
      (‖plusCrossingVector (by omega) θ r C i‖ = 2 ∧
        ‖minusCrossingVector (by omega) θ r C i‖ < 2) ∨
      (‖plusCrossingVector (by omega) θ r C i‖ < 2 ∧
        ‖minusCrossingVector (by omega) θ r C i‖ = 2)) :
    ∀ j, ‖crossingVector hm θ (centerZero C)
      (patternSign (activePattern (by omega) θ r C)) j‖ = 2 := by
  have hC0 : HalfPeriodic (by omega) (centerZero C) :=
    centerZero_halfPeriodic (by omega) C hC
  have hσ : Antiperiodic (by omega)
      (patternSign (activePattern (by omega) θ r C)) :=
    patternSign_antiperiodic _
  intro j
  obtain ⟨i, hj | hj⟩ := half_decomposition (by omega : 0 < m) j
  · rw [hj]
    exact selected_crossing_halfIndex hm θ r C hr hactive i
  · rw [hj, crossingVector_halfTurn_neg hm θ (centerZero C)
      (patternSign (activePattern (by omega) θ r C)) hθ hC0 hσ,
      norm_neg]
    exact selected_crossing_halfIndex hm θ r C hr hactive i

end
end StructuralNote.MatchingActivityActualChartSelection
