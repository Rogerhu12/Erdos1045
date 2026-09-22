import StructuralNote.FixedSchurEdgeGeometry
import StructuralNote.CommonFiberNonlocalFeasibility

/-! Exact cyclic-offset geometry for a half-periodic center. The selected
next crossing has sign minus in the full fixed-Schur word convention. -/

namespace StructuralNote.FixedSchurOffsetGeometry

open Complex Erdos1045.EventualExact
open FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open CommonFiberGeometry CommonFiberNonlocalFrames CommonFiberNonlocalProjection
open FixedSchurEdgeGeometry

noncomputable section

theorem advance_next {m : ℕ} (hm : 0 < m) (j : Fin (2 * m)) :
    cyclicAdvance j (m + 1) = halfTurn hm (successor (by omega) j) := by
  apply Fin.ext
  simp only [cyclicAdvance, halfTurn, successor, Nat.mod_add_mod]
  congr 1
  omega

theorem next_classification {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (C : Fin (2 * m) → ℂ) (σ : Fin (2 * m) → ℝ)
    (hθ : HalfPeriodic (by omega) (fun j => (θ j : ℂ)))
    (hC : HalfPeriodic (by omega) C) (j : Fin (2 * m))
    (hσ : σ j = 1 ∨ σ j = -1)
    (hsel : ‖crossingVector hm θ C σ j‖ = 2)
    (hun : ‖crossingVector hm θ C (fun k => -σ k) j‖ < 2) :
    ‖vertex θ C (cyclicAdvance j (m + 1)) - vertex θ C j‖ ≤ 2 ∧
      (‖vertex θ C (cyclicAdvance j (m + 1)) - vertex θ C j‖ = 2 ↔ σ j = -1) := by
  rw [advance_next (by omega), norm_sub_rev]
  rcases hσ with h | h
  · have he := crossingVector_eq_vertex_sub_minus hm θ C (fun k => -σ k)
      hθ hC j (by simp [h])
    rw [he] at hun
    exact ⟨hun.le, by norm_num [ne_of_lt hun, h]⟩
  · have he := crossingVector_eq_vertex_sub_minus hm θ C σ hθ hC j h
    rw [he] at hsel
    exact ⟨hsel.le, by simp [hsel, h]⟩

theorem nonlocal_strict {m r : ℕ} (hm : 8 ≤ m) (hr : r < 2 * m)
    (hprev : r ≠ m - 1) (hmatch : r ≠ m) (hnext : r ≠ m + 1)
    (θ : Fin (2 * m) → ℝ) (C : Fin (2 * m) → ℂ)
    (hθhalf : HalfPeriodic (by omega) (fun j => (θ j : ℂ)))
    (hC : HalfPeriodic (by omega) C)
    (hθ : ∀ i, |θ i| ≤ 1 / (1000 * (2 * m : ℝ)))
    (hstep : ∀ i, ‖difference (by omega) C i‖ ≤ 1 / (1000 * (2 * m : ℝ)))
    (hrad : ∀ i, |radial (meanFrame (by omega) θ i) (difference (by omega) C i)| ≤
      10 / (2 * m : ℝ) ^ 2) (j : Fin (2 * m)) :
    ‖vertex θ C (cyclicAdvance j r) - vertex θ C j‖ < 2 := by
  by_cases hrm : r ≤ m
  · have hh := CommonFiberNonlocalFeasibility.forward_strict hm
      (show 2 ≤ m - r by omega) (show m - r ≤ m by omega)
      θ C hθhalf hC hθ hstep hrad (cyclicAdvance j (m - (m - r)))
    change ‖vertex θ C (cyclicAdvance (cyclicAdvance j (m - (m - r))) (m + (m - r))) -
      vertex θ C (cyclicAdvance j (m - (m - r)))‖ < 2 at hh
    rwa [NonlocalFeasibility.advance_back_forward (show m - r ≤ m by omega),
      Nat.sub_sub_self hrm, norm_sub_rev] at hh
  · have hh := CommonFiberNonlocalFeasibility.forward_strict hm
      (show 2 ≤ r - m by omega) (show r - m ≤ m by omega)
      θ C hθhalf hC hθ hstep hrad j
    change ‖vertex θ C (cyclicAdvance j (m + (r - m))) - vertex θ C j‖ < 2 at hh
    rwa [Nat.add_sub_of_le (show m ≤ r by omega)] at hh

def OffsetEdge {m : ℕ} (σ : Fin (2 * m) → ℝ) (j : Fin (2 * m)) (r : ℕ) : Prop :=
  r = m ∨ (r = m + 1 ∧ σ j = -1) ∨
    (r = m - 1 ∧ σ (cyclicAdvance j r) = -1)

theorem offset_classification {m : ℕ} (hm : 2 ≤ m)
    (Z : Fin (2 * m) → ℂ) (σ : Fin (2 * m) → ℝ)
    (hmatch : ∀ j, ‖Z j - Z (halfTurn (by omega) j)‖ = 2)
    (hnext : ∀ j, ‖Z (cyclicAdvance j (m + 1)) - Z j‖ ≤ 2 ∧
      (‖Z (cyclicAdvance j (m + 1)) - Z j‖ = 2 ↔ σ j = -1))
    (hother : ∀ r, r < 2 * m → r ≠ m - 1 → r ≠ m → r ≠ m + 1 →
      ∀ j, ‖Z (cyclicAdvance j r) - Z j‖ < 2)
    (r : ℕ) (hr : r < 2 * m) (j : Fin (2 * m)) :
    ‖Z (cyclicAdvance j r) - Z j‖ ≤ 2 ∧
      (‖Z (cyclicAdvance j r) - Z j‖ = 2 ↔ OffsetEdge σ j r) := by
  by_cases hp : r = m - 1
  · subst r
    have hh := hnext (cyclicAdvance j (m - 1))
    rw [NonlocalFeasibility.advance_back_forward (by omega : 1 ≤ m), norm_sub_rev] at hh
    simpa only [OffsetEdge, show m - 1 ≠ m by omega,
      show m - 1 ≠ m + 1 by omega, false_or, false_and, true_and] using hh
  by_cases hm' : r = m
  · subst r
    have he : cyclicAdvance j m = halfTurn (by omega) j := rfl
    rw [he, norm_sub_rev, hmatch]
    exact ⟨le_rfl, by simp [OffsetEdge]⟩
  by_cases hn : r = m + 1
  · subst r
    simpa only [OffsetEdge, show m + 1 ≠ m by omega,
      show m + 1 ≠ m - 1 by omega, false_or, false_and, true_and, or_false] using hnext j
  have hs := hother r hr hp hm' hn j
  exact ⟨hs.le, by simp [OffsetEdge, hp, hm', hn, ne_of_lt hs]⟩

end
end StructuralNote.FixedSchurOffsetGeometry
