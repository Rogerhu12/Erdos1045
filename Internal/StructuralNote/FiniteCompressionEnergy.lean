import StructuralNote.FixedDualClassificationKernel
import EventualExact.SchurLift

/-! The actual finite Schur energy of a simultaneous antipodal sign change.
This is the compression identity, with its normalization proved explicitly. -/

namespace StructuralNote.FiniteCompressionEnergy

open Erdos1045.EventualExact FourierMultiplier FixedDualClassificationKernel
open scoped BigOperators
noncomputable section

def point {n : ℕ} (i : Fin n) : Fin n → ℝ := fun j => if j = i then 1 else 0

theorem pairing_point {n : ℕ} (i : Fin n) (f : Fin n → ℝ) :
    finitePairing (point i) f = f i := by
  simp [finitePairing, point]

theorem operator_point_symm {n : ℕ} (i j : Fin n) :
    operator n (point i) j = operator n (point j) i := by
  simpa only [pairing_point] using selfAdjoint n (point j) (point i)

theorem operator_half_point {m : ℕ} (hm : 0 < m) (i : Fin (2 * m)) :
    operator (2 * m) (point (halfTurn hm i)) = -operator (2 * m) (point i) := by
  funext j
  rw [operator_point_symm, operator_antiperiodic, operator_point_symm]
  rfl

theorem operator_point {n : ℕ} (i j : Fin n) :
    operator n (point j) i = (2 / n : ℝ) * finiteKernel n (gridAngle i - gridAngle j) := by
  rw [operator_convolution]
  simp [point]

def patch {m : ℕ} (hm : 0 < m) (A : ℝ) (E : Finset (Fin (2 * m))) : Fin (2 * m) → ℝ :=
  ∑ i ∈ E, (2 * A) • (point i - point (halfTurn hm i))

theorem pairing_patch {m : ℕ} (hm : 0 < m) (A : ℝ)
    (E : Finset (Fin (2 * m))) (f : Fin (2 * m) → ℝ) :
    finitePairing (patch hm A E) f = 2 * A * ∑ i ∈ E, (f i - f (halfTurn hm i)) := by
  simp only [finitePairing, patch, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_assoc, ← Finset.mul_sum, sub_mul, Finset.sum_sub_distrib]
  simp [point]

theorem pairing_patch_operator {m : ℕ} (hm : 0 < m) (A : ℝ)
    (E : Finset (Fin (2 * m))) (f : Fin (2 * m) → ℝ) :
    finitePairing (patch hm A E) (operator (2 * m) f) =
      4 * A * ∑ i ∈ E, operator (2 * m) f i := by
  rw [pairing_patch]
  simp only [operator_antiperiodic, sub_neg_eq_add, Finset.sum_add_distrib]
  ring

theorem operator_patch {m : ℕ} (hm : 0 < m) (A : ℝ)
    (E : Finset (Fin (2 * m))) (i : Fin (2 * m)) :
    operator (2 * m) (patch hm A E) i =
      (8 * A / (2 * m : ℝ)) * ∑ j ∈ E, finiteKernel (2 * m) (gridAngle i - gridAngle j) := by
  simp only [patch, map_sum, map_smul, map_sub, operator_half_point hm,
    Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [operator_point]
  push_cast
  ring

theorem patch_energy {m : ℕ} (hm : 0 < m) (A : ℝ) (E : Finset (Fin (2 * m))) :
    normalizedBoxEnergy (operator (2 * m)) (patch hm A E) =
      (16 * A ^ 2 / (2 * m : ℝ) ^ 2) *
        ∑ i ∈ E, ∑ j ∈ E, finiteKernel (2 * m) (gridAngle i - gridAngle j) := by
  simp only [normalizedBoxEnergy, boxEnergy, Fintype.card_fin, pairing_patch_operator,
    operator_patch, ← Finset.mul_sum]
  push_cast
  ring

/-- The exact energy identity used by one-pass compression. -/
theorem energy_add_patch {m : ℕ} (hm : 0 < m) (A : ℝ)
    (E : Finset (Fin (2 * m))) (b : Fin (2 * m) → ℝ) :
    normalizedBoxEnergy (operator (2 * m)) (b + patch hm A E) =
      normalizedBoxEnergy (operator (2 * m)) b +
        (4 * A / (2 * m : ℝ)) * (∑ i ∈ E, operator (2 * m) b i) +
        (16 * A ^ 2 / (2 * m : ℝ) ^ 2) *
          ∑ i ∈ E, ∑ j ∈ E, finiteKernel (2 * m) (gridAngle i - gridAngle j) := by
  have hp := patch_energy hm A E
  simp only [normalizedBoxEnergy, boxEnergy, Fintype.card_fin] at hp
  rw [normalizedBoxEnergy, boxEnergy_add (selfAdjoint (2 * m)), pairing_patch_operator]
  simp only [Fintype.card_fin, add_div]
  rw [show boxEnergy (operator (2 * m)) (patch hm A E) =
    finitePairing (patch hm A E) (operator (2 * m) (patch hm A E)) / 2 from rfl, hp]
  simp only [normalizedBoxEnergy, Fintype.card_fin]
  push_cast
  ring

theorem point_half {m : ℕ} (hm : 0 < m) (i j : Fin (2 * m)) :
    point (halfTurn hm j) i = point j (halfTurn hm i) := by
  have he : i = halfTurn hm j ↔ halfTurn hm i = j := by
    constructor
    · intro h
      rw [h, SchurLift.halfTurn_involutive hm]
    · intro h
      rw [← h, SchurLift.halfTurn_involutive hm]
  simp only [point, he]

theorem patch_apply {m : ℕ} (hm : 0 < m) (A : ℝ)
    (E : Finset (Fin (2 * m))) (i : Fin (2 * m)) :
    patch hm A E i = 2 * A * ((if i ∈ E then 1 else 0) -
      (if halfTurn hm i ∈ E then 1 else 0)) := by
  simp only [patch, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    point_half hm, ← Finset.mul_sum, Finset.sum_sub_distrib]
  simp [point]

theorem patch_antiperiodic {m : ℕ} (hm : 0 < m) (A : ℝ)
    (E : Finset (Fin (2 * m))) : FiniteBox.Antiperiodic hm (patch hm A E) := by
  intro i
  rw [patch_apply, patch_apply, SchurLift.halfTurn_involutive hm]
  ring

/-- Changing selected negative coordinates and their antipodes preserves the
actual box. The background may be arbitrary at every unselected coordinate. -/
theorem add_patch_mem_box {m : ℕ} (hm : 0 < m) (A : ℝ)
    (E : Finset (Fin (2 * m))) (b : Fin (2 * m) → ℝ)
    (hb : b ∈ FiniteBox.box hm A) (hE : ∀ i ∈ E, b i = -A) :
    b + patch hm A E ∈ FiniteBox.box hm A := by
  refine ⟨?_, ?_⟩
  · intro i
    simp only [Pi.add_apply, hb.1 i, patch_antiperiodic hm A E i]
    ring
  · intro i
    have hA : 0 ≤ A := (abs_nonneg (b i)).trans (hb.2 i)
    simp only [Pi.add_apply, patch_apply]
    by_cases hi : i ∈ E
    · by_cases hh : halfTurn hm i ∈ E
      · simpa only [if_pos hi, if_pos hh, sub_self, mul_zero, add_zero] using hb.2 i
      · rw [if_pos hi, if_neg hh, hE i hi]
        have he : -A + 2 * A * ((1 : ℝ) - 0) = A := by ring
        rw [he, abs_of_nonneg hA]
    · by_cases hh : halfTurn hm i ∈ E
      · have hbi : b i = A := by have h := hE _ hh; rw [hb.1 i] at h; linarith
        rw [if_neg hi, if_pos hh, hbi]
        have he : A + 2 * A * ((0 : ℝ) - 1) = -A := by ring
        rw [he, abs_neg, abs_of_nonneg hA]
      · simpa only [if_neg hi, if_neg hh, sub_self, mul_zero, add_zero] using hb.2 i

end
end StructuralNote.FiniteCompressionEnergy
