import StructuralNote.CommonTangentialParameters

/-! Exact mean-zero reconstruction from the two closed tangential coordinates. -/

namespace StructuralNote.CommonTangentialParameters

open Erdos1045.EventualExact
open Complex FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum BoxLensLift
open scoped BigOperators
noncomputable section

local notation "conj" => (starRingEnd ℂ)

theorem half_decomposition {m : ℕ} (hm : 0 < m) (j : Fin (2 * m)) :
    ∃ k : Fin m, j = halfIndex k ∨ j = halfTurn hm (halfIndex k) := by
  by_cases hj : j.val < m
  · exact ⟨⟨j.val, hj⟩, Or.inl (Fin.ext rfl)⟩
  · let k : Fin m := ⟨j.val - m, by omega⟩
    refine ⟨k, Or.inr ?_⟩
    apply Fin.ext
    simp only [halfTurn, halfIndex, k]
    rw [Nat.sub_add_cancel (by omega : m ≤ j.val), Nat.mod_eq_of_lt j.isLt]

theorem eq_of_half_restriction {m : ℕ} (hm : 0 < m) {v w : Fin (2 * m) → ℂ}
    (hv : HalfPeriodic hm v) (hw : HalfPeriodic hm w)
    (h : ∀ k, v (halfIndex k) = w (halfIndex k)) : v = w := by
  funext j
  obtain ⟨k, hj | hj⟩ := half_decomposition hm j
  · rw [hj, h k]
  · rw [hj, hv, hw, h k]

theorem difference_halfPeriodic {m : ℕ} (hm : 0 < m) (v : Fin (2 * m) → ℂ)
    (hv : HalfPeriodic hm v) : HalfPeriodic hm (difference (by omega) v) := by
  intro j
  change v (successor _ (halfTurn hm j)) - v (halfTurn hm j) = _
  rw [← halfTurn_successor, hv, hv]
  rfl

theorem constraint_halfTurn {m : ℕ} (hm : 0 < m) (v : Fin (2 * m) → ℂ)
    (hv : HalfPeriodic hm v) (j : Fin (2 * m)) :
    constraint (by omega) v (halfTurn hm j) = -constraint (by omega) v j := by
  unfold constraint
  rw [frame_halfTurn, difference_halfPeriodic hm v hv j]
  simp only [map_neg, neg_mul, Complex.neg_re, mul_neg]

theorem constraint_zero_of_half_tangential {m : ℕ} (hm : 0 < m)
    (v : Fin (2 * m) → ℂ) (hv : HalfPeriodic hm v) (ν : Fin m → ℝ)
    (hν : ∀ j, difference (by omega) v (halfIndex j) = halfIncrement ν j) :
    constraint (by omega) v = 0 := by
  have hh (j : Fin m) : constraint (by omega) v (halfIndex j) = 0 := by
    have hf : conj (frame (2 * m) (halfIndex j)) * frame (2 * m) (halfIndex j) = 1 := by
      rw [mul_comm, Complex.mul_conj, frame_normSq]
      rfl
    rw [constraint, hν, halfIncrement, ← frame_halfIndex]
    simp [← mul_assoc, hf]
  funext j
  obtain ⟨k, hj | hj⟩ := half_decomposition hm j
  · exact hj ▸ hh k
  · rw [hj, constraint_halfTurn hm v hv, hh, neg_zero]
    rfl

def reconstruct {m : ℕ} (hm : 0 < m) (ν : Fin m → ℝ) : Fin (2 * m) → ℂ :=
  integral (repeatHalf hm (halfIncrement ν))

theorem reconstruct_mean_zero {m : ℕ} (hm : 0 < m) (ν : Fin m → ℝ) :
    (∑ j, reconstruct hm ν j) = 0 := integral_mean_zero (by omega) _

theorem reconstruct_difference {m : ℕ} (hm : 0 < m) (ν : Fin m → ℝ) (hν : Closed ν) :
    difference (by omega) (reconstruct hm ν) = repeatHalf hm (halfIncrement ν) := by
  apply difference_integral
  rw [repeatHalf_sum, (closed_iff_increment_sum ν).1 hν, mul_zero]

theorem repeatHalf_halfIndex {m : ℕ} (hm : 0 < m) (f : Fin m → ℂ) (j : Fin m) :
    repeatHalf hm f (halfIndex j) = f j := by
  simp only [repeatHalf, halfIndex, Nat.mod_eq_of_lt j.isLt]

theorem reconstruct_half_difference {m : ℕ} (hm : 0 < m) (ν : Fin m → ℝ) (hν : Closed ν)
    (j : Fin m) : difference (by omega) (reconstruct hm ν) (halfIndex j) = halfIncrement ν j := by
  rw [reconstruct_difference hm ν hν, repeatHalf_halfIndex]

theorem reconstruct_halfPeriodic {m : ℕ} (hm : 0 < m) (ν : Fin m → ℝ) (hν : Closed ν) :
    HalfPeriodic hm (reconstruct hm ν) := by
  have he : (fun j => reconstruct hm ν (halfTurn hm j)) = reconstruct hm ν := by
    apply integral_unique (by omega)
    · have hs := Equiv.sum_comp
        (Equiv.ofBijective (halfTurn hm) (halfTurn_involutive hm).bijective)
        (reconstruct hm ν)
      exact hs.trans (reconstruct_mean_zero hm ν)
    · funext k
      change reconstruct hm ν (halfTurn hm (successor _ k)) -
        reconstruct hm ν (halfTurn hm k) = repeatHalf hm (halfIncrement ν) k
      rw [halfTurn_successor]
      change difference (by omega) (reconstruct hm ν) (halfTurn hm k) = _
      rw [reconstruct_difference hm ν hν]
      exact repeatHalf_halfTurn hm _ k
  exact fun j => congrFun he j

theorem reconstruct_mem {m : ℕ} (hm : 0 < m) (ν : Fin m → ℝ) (hν : Closed ν) :
    ParameterSpace hm (reconstruct hm ν) := by
  have hp := reconstruct_halfPeriodic hm ν hν
  exact ⟨hp, reconstruct_mean_zero hm ν,
    constraint_zero_of_half_tangential hm _ hp ν (reconstruct_half_difference hm ν hν)⟩

theorem coordinates_reconstruct {m : ℕ} (hm : 0 < m) (ν : Fin m → ℝ) (hν : Closed ν) :
    coordinates hm (reconstruct hm ν) = ν :=
  (coordinates_unique hm _ ν (reconstruct_half_difference hm ν hν)).symm

theorem reconstruct_coordinates {m : ℕ} (hm : 0 < m) (v : Fin (2 * m) → ℂ)
    (hv : ParameterSpace hm v) : reconstruct hm (coordinates hm v) = v := by
  apply Eq.symm
  apply integral_unique (by omega) _ v hv.2.1
  apply eq_of_half_restriction hm (difference_halfPeriodic hm v hv.1)
    (repeatHalf_halfTurn hm _)
  intro j
  rw [repeatHalf_halfIndex]
  exact difference_coordinates hm v hv.2.2 j

/-- The two explicit weighted closure equations give precisely the real coordinates of `H_n`. -/
def parameterEquiv {m : ℕ} (hm : 0 < m) :
    {v : Fin (2 * m) → ℂ // ParameterSpace hm v} ≃ {ν : Fin m → ℝ // Closed ν} where
  toFun v := ⟨coordinates hm v, coordinates_closed hm v v.property.1 v.property.2.2⟩
  invFun ν := ⟨reconstruct hm ν, reconstruct_mem hm ν ν.property⟩
  left_inv v := Subtype.ext (reconstruct_coordinates hm v v.property)
  right_inv ν := Subtype.ext (coordinates_reconstruct hm ν ν.property)

end
end StructuralNote.CommonTangentialParameters
