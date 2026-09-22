import EventualExact.FiniteMultiplier

/-! Exact symmetries of the actual finite Fourier box energy.

The proofs below use the finite multiplier's own spectral identity.  In
particular, no pair-energy surrogate is used: a cyclic shift only changes each
Fourier coefficient by a unit-modulus character, while a global sign changes
each coefficient by `-1`.
-/

namespace StructuralNote.FiniteBoxEnergySymmetry

open Finset
open scoped BigOperators
open Erdos1045.EventualExact
open Erdos1045.EventualExact.FourierMultiplier

noncomputable section

theorem character_finRotate {n : ℕ} (hn : 0 < n) (p j : Fin n) :
    character n p (finRotate n j) = character n p j * character n p 1 := by
  let : NeZero n := ⟨hn.ne'⟩
  rw [finRotate_apply, Fin.val_add, Fin.val_one']
  have hmod : (j.val + 1) % n = (j.val + 1 % n) % n := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt j.isLt]
  rw [← hmod]
  rw [character_mod hn p (j.val + 1), character_add]

theorem realCoefficient_finRotate_symm {n : ℕ} (hn : 0 < n)
    (q : Fin n → ℝ) (p : Fin n) :
    realCoefficient (fun j => q ((finRotate n).symm j)) p =
      realCoefficient q p * (starRingEnd ℂ) (character n p 1) := by
  unfold realCoefficient coefficient
  rw [← Equiv.sum_comp (finRotate n)
    (fun j => (q ((finRotate n).symm j) : ℂ) *
      (starRingEnd ℂ) (character n p j))]
  simp only [Equiv.symm_apply_apply]
  simp_rw [character_finRotate hn]
  simp_rw [map_mul, ← mul_assoc]
  rw [← Finset.sum_mul]
  ring

theorem realCoefficient_neg {n : ℕ} (q : Fin n → ℝ) (p : Fin n) :
    realCoefficient (fun j => -q j) p = -realCoefficient q p := by
  unfold realCoefficient coefficient
  dsimp only
  simp_rw [Complex.ofReal_neg, neg_mul]
  rw [Finset.sum_neg_distrib]
  ring

theorem normalizedBoxEnergy_finRotate
    {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) :
    normalizedBoxEnergy (FourierMultiplier.operator n)
        (fun j => q ((finRotate n).symm j)) =
      normalizedBoxEnergy (FourierMultiplier.operator n) q := by
  rw [spectral_energy hn, spectral_energy hn]
  apply congrArg (fun z : ℝ => (1 / 2 : ℝ) * z)
  apply Finset.sum_congr rfl
  intro p hp
  rw [realCoefficient_finRotate_symm hn q p, Complex.normSq_mul,
    Complex.normSq_conj]
  have hunit : Complex.normSq (character n p 1) = 1 := by
    rw [show character n p 1 = Erdos1045.LocalPhase.regularRoot n ^ (p : ℕ) by
      simp [character]]
    rw [Complex.normSq_eq_norm_sq, norm_pow,
      Erdos1045.ClosedFourier.root_norm, one_pow]
    norm_num
  rw [hunit, mul_one]

theorem normalizedBoxEnergy_neg
    {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) :
    normalizedBoxEnergy (FourierMultiplier.operator n) (fun j => -q j) =
      normalizedBoxEnergy (FourierMultiplier.operator n) q := by
  rw [spectral_energy hn, spectral_energy hn]
  apply congrArg (fun z : ℝ => (1 / 2 : ℝ) * z)
  apply Finset.sum_congr rfl
  intro p hp
  rw [realCoefficient_neg, Complex.normSq_neg]

theorem normalizedBoxEnergy_finRotate_zero (q : Fin 0 → ℝ) :
    normalizedBoxEnergy (FourierMultiplier.operator 0)
        (fun j => q ((finRotate 0).symm j)) =
      normalizedBoxEnergy (FourierMultiplier.operator 0) q := by
  rfl

theorem normalizedBoxEnergy_neg_zero (q : Fin 0 → ℝ) :
    normalizedBoxEnergy (FourierMultiplier.operator 0) (fun j => -q j) =
      normalizedBoxEnergy (FourierMultiplier.operator 0) q := by
  rfl

/- Forward rotation is the form used by most reindexing statements. -/
theorem normalizedBoxEnergy_finRotate_forward
    {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) :
    normalizedBoxEnergy (FourierMultiplier.operator n)
        (fun j => q (finRotate n j)) =
      normalizedBoxEnergy (FourierMultiplier.operator n) q := by
  simpa only [Equiv.apply_symm_apply] using
    (normalizedBoxEnergy_finRotate hn (fun j => q (finRotate n j))).symm

theorem normalizedBoxEnergy_finRotate_iterate
    {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) (k : ℕ) :
    normalizedBoxEnergy (FourierMultiplier.operator n)
        (fun j => q ((finRotate n)^[k] j)) =
      normalizedBoxEnergy (FourierMultiplier.operator n) q := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ]
      have hs := normalizedBoxEnergy_finRotate_forward hn
        (fun j => q ((finRotate n)^[k] j))
      simpa [Function.comp_apply] using hs.trans ih

theorem normalizedBoxEnergy_finRotate_forward_all
    (n : ℕ) (q : Fin n → ℝ) :
    normalizedBoxEnergy (FourierMultiplier.operator n)
        (fun j => q (finRotate n j)) =
      normalizedBoxEnergy (FourierMultiplier.operator n) q := by
  cases n with
  | zero => exact normalizedBoxEnergy_finRotate_zero q
  | succ n => exact normalizedBoxEnergy_finRotate_forward (by omega) q

theorem normalizedBoxEnergy_neg_all
    (n : ℕ) (q : Fin n → ℝ) :
    normalizedBoxEnergy (FourierMultiplier.operator n) (fun j => -q j) =
      normalizedBoxEnergy (FourierMultiplier.operator n) q := by
  cases n with
  | zero => exact normalizedBoxEnergy_neg_zero q
  | succ n => exact normalizedBoxEnergy_neg (by omega) q

end
end StructuralNote.FiniteBoxEnergySymmetry
