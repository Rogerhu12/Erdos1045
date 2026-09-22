import StructuralNote.FiniteCompressionEnergy

namespace StructuralNote.SolAntipodalMidpoint

open Erdos1045.EventualExact FourierMultiplier FixedDualClassificationKernel
open FiniteCompressionEnergy
noncomputable section

/-- The actual antipodal coordinate spike. -/
def spike {m : ℕ} (hm : 0 < m) (i : Fin (2 * m)) : Fin (2 * m) → ℝ :=
  point i - point (halfTurn hm i)

theorem patch_half_singleton {m : ℕ} (hm : 0 < m) (i : Fin (2 * m)) :
    patch hm (1 / 2 : ℝ) {i} = spike hm i := by
  funext j
  simp [patch, spike]

theorem spike_antiperiodic {m : ℕ} (hm : 0 < m) (i : Fin (2 * m)) :
    FiniteBox.Antiperiodic hm (spike hm i) := by
  rw [← patch_half_singleton hm i]
  exact patch_antiperiodic hm (1 / 2 : ℝ) {i}

theorem spike_energy {m : ℕ} (hm : 0 < m) (i : Fin (2 * m)) :
    normalizedBoxEnergy (operator (2 * m)) (spike hm i) =
      4 * finiteKernel (2 * m) 0 / (2 * m : ℝ) ^ 2 := by
  have h := patch_energy hm (1 / 2 : ℝ) ({i} : Finset (Fin (2 * m)))
  rw [patch_half_singleton] at h
  simp only [Finset.sum_singleton, sub_self] at h
  calc
    _ = (16 * (1 / 2 : ℝ) ^ 2 / (2 * m : ℝ) ^ 2) * finiteKernel (2 * m) 0 := h
    _ = _ := by ring

theorem midpoint_vertices {m : ℕ} (hm : 0 < m) (A : ℝ)
    (b : Fin (2 * m) → ℝ) (hb : b ∈ FiniteBox.box hm A)
    (i : Fin (2 * m)) (hi : b i = -A) :
    b + patch hm A {i} ∈ FiniteBox.box hm A ∧
      b + patch hm A {i} - b = (2 * A) • spike hm i := by
  constructor
  · exact add_patch_mem_box hm A {i} b hb (by simpa using hi)
  · funext j
    simp [patch, spike]

theorem midpoint_energy_identity {m : ℕ} (hm : 0 < m) (A : ℝ)
    (b : Fin (2 * m) → ℝ) (i : Fin (2 * m)) :
    normalizedBoxEnergy (operator (2 * m)) (b + patch hm A {i}) =
      normalizedBoxEnergy (operator (2 * m)) b +
      (4 * A / (2 * m : ℝ)) * operator (2 * m) b i +
      (16 * A ^ 2 / (2 * m : ℝ) ^ 2) * finiteKernel (2 * m) 0 := by
  simpa using energy_add_patch hm A ({i} : Finset (Fin (2 * m))) b

def coordinateMidpoint {m : ℕ} (hm : 0 < m) (A : ℝ)
    (b : Fin (2 * m) → ℝ) (i : Fin (2 * m)) : Fin (2 * m) → ℝ :=
  b + A • spike hm i

theorem antipode_ne {m : ℕ} (hm : 0 < m) (i : Fin (2 * m)) : halfTurn hm i ≠ i := by
  intro h
  have hh := FiniteBox.halfTurn_lt_iff hm i
  rw [h] at hh
  tauto

theorem patch_singleton {m : ℕ} (hm : 0 < m) (A : ℝ) (i : Fin (2 * m)) :
    patch hm A {i} = (2 * A) • spike hm i := by
  funext j
  simp [patch, spike]

/-- The two genuine box vertices on either side of the coordinate midpoint. -/
theorem two_vertices_around_midpoint {m : ℕ} (hm : 0 < m) (A : ℝ)
    (b : Fin (2 * m) → ℝ) (hb : b ∈ FiniteBox.box hm A)
    (hbabs : ∀ j, |b j| = A) (i : Fin (2 * m)) (hi : b i = -A) :
    let b' := b + patch hm A {i}
    let c := coordinateMidpoint hm A b i
    b ∈ FiniteBox.box hm A ∧ b' ∈ FiniteBox.box hm A ∧
      (∀ j, |b j| = A) ∧ (∀ j, |b' j| = A) ∧
      b = c - A • spike hm i ∧ b' = c + A • spike hm i := by
  dsimp only
  have hb' := (midpoint_vertices hm A b hb i hi).1
  refine ⟨hb, hb', hbabs, ?_, ?_, ?_⟩
  · intro j
    have hA : 0 ≤ A := (abs_nonneg (b j)).trans_eq (hbabs j)
    by_cases h : j = i
    · subst j
      have hne := antipode_ne hm i
      rw [Pi.add_apply, patch_apply]
      simp only [Finset.mem_singleton, hne, if_false, sub_zero, hi, if_true]
      norm_num only [mul_one]
      rw [show -A + 2 * A = A by ring, abs_of_nonneg hA]
    · by_cases hh : halfTurn hm j = i
      · have hjv : b j = A := by
          have hjanti := hb.1 j
          rw [hh, hi] at hjanti
          linarith
        rw [Pi.add_apply, patch_apply]
        simp only [Finset.mem_singleton, h, if_false, hh, if_true, zero_sub, hjv]
        rw [show A + 2 * A * -1 = -A by ring, abs_neg, abs_of_nonneg hA]
      · rw [Pi.add_apply, patch_apply]
        simp [h, hh, hbabs j]
  · funext j
    simp [coordinateMidpoint]
  · rw [patch_singleton hm A i]
    funext j
    simp [coordinateMidpoint]
    ring

end
end StructuralNote.SolAntipodalMidpoint
