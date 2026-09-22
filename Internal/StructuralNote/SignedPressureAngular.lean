import StructuralNote.SignedPressureRemainder
import EventualExact.AngularObjectiveCurvature
import EventualExact.DiscretePoincare

/-! Difference-energy estimates for the signed angular terms in the pressure inequality. -/

noncomputable section
open scoped BigOperators

namespace StructuralNote.SignedPressureAngular

open Erdos1045 Erdos1045.EventualExact Complex
open SchurSpectrum FiniteFourierLift DiscreteEnergy SchurLiftBounds
open AngularObjectiveCurvature SignedPressureRemainder

def root (n : ℕ) (j : Fin n) : ℂ := LocalPhase.regularRoot n ^ (j : ℕ)

theorem root_norm (n : ℕ) (j : Fin n) : ‖root n j‖ = 1 := by
  rw [root, norm_pow, ClosedFourier.root_norm, one_pow]

theorem normSq_add_le (x y : ℂ) : normSq (x + y) ≤ 2 * normSq x + 2 * normSq y := by
  simp only [normSq_apply, add_re, add_im]
  nlinarith [sq_nonneg (x.re - y.re), sq_nonneg (x.im - y.im)]

theorem product_difference_sq_le (f g : Fin n → ℂ) (i j : Fin n) :
    normSq (f i * g i - f j * g j) ≤
      2 * ‖f‖ ^ 2 * normSq (g i - g j) + 2 * ‖g‖ ^ 2 * normSq (f i - f j) := by
  have he : f i * g i - f j * g j = f i * (g i - g j) + (f i - f j) * g j := by ring
  rw [he]
  have h := normSq_add_le (f i * (g i - g j)) ((f i - f j) * g j)
  rw [normSq_mul, normSq_mul] at h
  have hf : normSq (f i) ≤ ‖f‖ ^ 2 := by
    rw [normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm f i) 2
  have hg : normSq (g j) ≤ ‖g‖ ^ 2 := by
    rw [normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm g j) 2
  nlinarith only [h, mul_le_mul_of_nonneg_right hf (normSq_nonneg (g i - g j)),
    mul_le_mul_of_nonneg_right hg (normSq_nonneg (f i - f j))]

/-- Product estimate for the actual finite chord energy. -/
theorem pairEnergy_mul_le {n : ℕ} (hn : 0 < n) (f g : Fin n → ℂ) :
    pairEnergy hn (fun j => f j * g j) ≤
      2 * ‖f‖ ^ 2 * pairEnergy hn g + 2 * ‖g‖ ^ 2 * pairEnergy hn f := by
  have h (i j : Fin n) := div_le_div_of_nonneg_right (product_difference_sq_le f g i j)
    (normSq_nonneg (root n i - root n j))
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => h i j))
  simp only [add_div, mul_div_assoc, Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  simp only [pairEnergy_eq_chord_sum]
  change _ ≤ 2 * ‖f‖ ^ 2 * ((∑ i, ∑ j, normSq (g i - g j) / normSq (root n i - root n j)) / 2) +
    2 * ‖g‖ ^ 2 * ((∑ i, ∑ j, normSq (f i - f j) / normSq (root n i - root n j)) / 2)
  simp only [root] at hs ⊢
  linarith only [hs]

theorem realEnergy_mul_le {n : ℕ} (hn : 0 < n) (f g : Fin n → ℝ) :
    realEnergy hn (fun j => f j * g j) ≤
      2 * ‖f‖ ^ 2 * realEnergy hn g + 2 * ‖g‖ ^ 2 * realEnergy hn f := by
  have h := pairEnergy_mul_le hn (fun j => (f j : ℂ)) (fun j => (g j : ℂ))
  simpa only [← ofReal_mul, PolarCenterEnergy.realColumn_norm, realEnergy] using h

theorem imaginary_energy_le {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) :
    realEnergy hn (fun j => (c j).im) ≤ pairEnergy hn c := by
  unfold realEnergy
  rw [pairEnergy_eq_chord_sum, pairEnergy_eq_chord_sum]
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply div_le_div_of_nonneg_right _ (normSq_nonneg _)
  simp only [← ofReal_sub, normSq_apply, sub_re, sub_im, ofReal_re, ofReal_im, zero_mul, add_zero]
  nlinarith [sq_nonneg ((c i).re - (c j).re)]

theorem pairEnergy_perm {n : ℕ} (hn : 0 < n) (p : Equiv.Perm (Fin n))
    (hroot : ∀ i j, normSq (root n (p i) - root n (p j)) = normSq (root n i - root n j))
    (c : Fin n → ℂ) : pairEnergy hn (fun j => c (p j)) = pairEnergy hn c := by
  rw [pairEnergy_eq_chord_sum, pairEnergy_eq_chord_sum]
  change (∑ i, ∑ j, normSq (c (p i) - c (p j)) / normSq (root n i - root n j)) / 2 =
    (∑ i, ∑ j, normSq (c i - c j) / normSq (root n i - root n j)) / 2
  have he : (∑ i, ∑ j, normSq (c (p i) - c (p j)) / normSq (root n i - root n j)) =
      ∑ i, ∑ j, normSq (c (p i) - c (p j)) / normSq (root n (p i) - root n (p j)) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hroot]
  rw [he]
  have hinner (i : Fin n) :
      (∑ j, normSq (c (p i) - c (p j)) / normSq (root n (p i) - root n (p j))) =
        ∑ j, normSq (c (p i) - c j) / normSq (root n (p i) - root n j) :=
    Equiv.sum_comp p (fun j => normSq (c (p i) - c j) / normSq (root n (p i) - root n j))
  simp_rw [hinner]
  rw [Equiv.sum_comp p (fun i => ∑ j, normSq (c i - c j) / normSq (root n i - root n j))]

theorem root_rotate {n : ℕ} (hn : 2 ≤ n) (j : Fin n) :
    root n (finRotate n j) = root n j * LocalPhase.regularRoot n := by
  rw [finRotate_eq_successor hn]
  change LocalPhase.regularRoot n ^ ((j.val + 1) % n) =
    LocalPhase.regularRoot n ^ j.val * LocalPhase.regularRoot n
  rw [← ClosedFourier.root_pow_mod (by omega), pow_add, pow_one]

theorem rotate_chord {n : ℕ} (hn : 2 ≤ n) (i j : Fin n) :
    normSq (root n (finRotate n i) - root n (finRotate n j)) = normSq (root n i - root n j) := by
  rw [root_rotate hn, root_rotate hn, ← sub_mul, normSq_mul,
    normSq_eq_norm_sq (LocalPhase.regularRoot n), ClosedFourier.root_norm]
  norm_num

theorem pairEnergy_rotate {n : ℕ} (hn : 2 ≤ n) (c : Fin n → ℂ) :
    pairEnergy (by omega) (fun j => c (finRotate n j)) = pairEnergy (by omega) c :=
  pairEnergy_perm (by omega) (finRotate n) (rotate_chord hn) c

end StructuralNote.SignedPressureAngular
