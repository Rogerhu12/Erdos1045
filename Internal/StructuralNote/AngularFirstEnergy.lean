import StructuralNote.AngularAntipodalFirst
import EventualExact.QuarticWindowBound

/-! Quartic control of the actual first angular derivative after antipodal cancellation. -/

noncomputable section
open scoped BigOperators

namespace StructuralNote.AngularFirstEnergy

open Erdos1045 Erdos1045.EventualExact Complex
open SchurSpectrum AngularObjectiveCurvature GeometricRelativeRemainder
open AngularAntipodalFirst SignedPressureAngular DiscreteEnergy

theorem cyclic_pair_sum {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) (f : ℂ → ℝ) (hf : f 0 = 0) :
    (∑ h ∈ (Finset.range n).erase 0, ∑ j ∈ Finset.range n,
      f (LocalDFT.pairRatio n (periodize hn c) j h)) =
      ∑ p : Fin n × Fin n, f (quotient c (root n) p) := by
  let F (i j : ℕ) := f ((periodize hn c i - periodize hn c j) /
    (LocalPhase.regularRoot n ^ i - LocalPhase.regularRoot n ^ j))
  have hp (i j : ℕ) : F (i + n) j = F i j := by
    simp only [F, periodize_periodic hn c i, pow_add, LocalDFT.regularRoot_pow hn, mul_one]
  have hshift (j : ℕ) : (∑ h ∈ Finset.range n, F (j + h) j) =
      ∑ i ∈ Finset.range n, F i j := by
    have h := CyclicAngles.sum_shift_of_drift (fun i => F i j) 0
      (fun i => by rw [hp]; ring) j
    simpa only [mul_zero, add_zero, Nat.add_comm] using h
  change (∑ h ∈ (Finset.range n).erase 0, ∑ j ∈ Finset.range n, F (j + h) j) = _
  rw [Finset.sum_erase _ (by simp [F, hf]), Finset.sum_comm]
  simp_rw [hshift]
  rw [Finset.sum_comm, Fintype.sum_prod_type, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp only [F, quotient, root, periodize_fin]

theorem fourthEnergy_eq_chord_sum {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) :
    AntipodalLog.fourthEnergy n (periodize hn c) =
      (∑ p : Fin n × Fin n, ‖quotient c (root n) p‖ ^ 4) / 2 := by
  unfold AntipodalLog.fourthEnergy
  rw [cyclic_pair_sum hn c (fun z => ‖z‖ ^ 4) (by simp)]

theorem pairEnergy_eq_quotient_sum {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) :
    pairEnergy hn c = (∑ p : Fin n × Fin n, ‖quotient c (root n) p‖ ^ 2) / 2 := by
  rw [pairEnergy_eq_chord_sum, Fintype.sum_prod_type]
  simp only [quotient, norm_div, div_pow, ← normSq_eq_norm_sq, root]

theorem norm_firstError_le {n : ℕ} (D C : Configuration.Points n)
    (hD : ∀ i, ‖D i‖ ≤ 1) (p : Fin n × Fin n) (hρ : ‖quotient C D p‖ ≤ 1 / 2) :
    ‖firstError D C p‖ ≤
      2 * (‖quotient C D p‖ ^ 2 + ‖C‖ * ‖quotient C D p‖) / ‖D p.1 - D p.2‖ := by
  have hden : (1 : ℝ) / 2 ≤ ‖1 - quotient C D p ^ 2‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (quotient C D p ^ 2)
    rw [norm_one, norm_pow] at h
    nlinarith [norm_nonneg (quotient C D p)]
  have hnum : ‖D p.1 * quotient C D p ^ 2 - C p.1 * quotient C D p‖ ≤
      ‖quotient C D p‖ ^ 2 + ‖C‖ * ‖quotient C D p‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_pow]
    have h₁ := mul_le_mul_of_nonneg_right (hD p.1) (sq_nonneg ‖quotient C D p‖)
    have h₂ := mul_le_mul_of_nonneg_right (norm_le_pi_norm C p.1) (norm_nonneg (quotient C D p))
    linarith only [h₁, h₂]
  have h₁ : ‖D p.1 * quotient C D p ^ 2 - C p.1 * quotient C D p‖ /
      ‖1 - quotient C D p ^ 2‖ ≤ 2 * (‖quotient C D p‖ ^ 2 + ‖C‖ * ‖quotient C D p‖) := by
    apply (div_le_iff₀ (by linarith : 0 < ‖1 - quotient C D p ^ 2‖)).2
    have h := mul_le_mul_of_nonneg_left hden
      (show 0 ≤ 2 * (‖quotient C D p‖ ^ 2 + ‖C‖ * ‖quotient C D p‖) by positivity)
    nlinarith only [h, hnum]
  unfold firstError
  rw [norm_div, norm_mul, div_mul_eq_div_div_swap]
  exact div_le_div_of_nonneg_right h₁ (norm_nonneg _)

theorem angular_error_sum_bound {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) (θ : Fin n → ℝ)
    (hsmall : ∀ p, ‖quotient c (root n) p‖ ≤ 1 / 2) :
    |∑ p : Fin n × Fin n, -(firstError (root n) c p).im * (θ p.1 - θ p.2)| ≤
      8 * Real.sqrt (AntipodalLog.fourthEnergy n (periodize hn c) + ‖c‖ ^ 2 * pairEnergy hn c) *
        Real.sqrt (realEnergy hn θ) := by
  let x (p : Fin n × Fin n) := ‖quotient c (root n) p‖ ^ 2 + ‖c‖ * ‖quotient c (root n) p‖
  let y (p : Fin n × Fin n) := |θ p.1 - θ p.2| / ‖root n p.1 - root n p.2‖
  have hp (p : Fin n × Fin n) :
      |-(firstError (root n) c p).im * (θ p.1 - θ p.2)| ≤ 2 * (x p * y p) := by
    rw [abs_mul, abs_neg]
    have h := (abs_im_le_norm _).trans
      (norm_firstError_le (root n) c (fun i => (root_norm n i).le) p (hsmall p))
    refine (mul_le_mul_of_nonneg_right h (abs_nonneg _)).trans_eq ?_
    dsimp [x, y]
    ring
  have hs := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (s := Finset.univ)
    (fun p _ => hp p))
  rw [← Finset.mul_sum] at hs
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ x y
  have hy : (∑ p, y p ^ 2) = 2 * realEnergy hn θ := by
    rw [realEnergy, pairEnergy_eq_quotient_sum hn]
    simp only [y, div_pow, sq_abs, quotient, ← ofReal_sub, norm_div, Complex.norm_real,
      Real.norm_eq_abs]
    ring
  have hx : (∑ p, x p ^ 2) ≤ 4 *
      (AntipodalLog.fourthEnergy n (periodize hn c) + ‖c‖ ^ 2 * pairEnergy hn c) := by
    have hpoint (p : Fin n × Fin n) : x p ^ 2 ≤
        2 * ‖quotient c (root n) p‖ ^ 4 + 2 * ‖c‖ ^ 2 * ‖quotient c (root n) p‖ ^ 2 := by
      dsimp [x]
      nlinarith only [sq_nonneg (‖quotient c (root n) p‖ ^ 2 - ‖c‖ * ‖quotient c (root n) p‖)]
    have h := Finset.sum_le_sum (s := Finset.univ) (fun p _ => hpoint p)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
    rw [fourthEnergy_eq_chord_sum, pairEnergy_eq_quotient_sum]
    linarith only [h]
  have hQ : 0 ≤ AntipodalLog.fourthEnergy n (periodize hn c) := by
    rw [fourthEnergy_eq_chord_sum]
    positivity
  have hA := pairEnergy_nonneg hn c
  have hE := pairEnergy_nonneg hn (fun j => (θ j : ℂ))
  change 0 ≤ realEnergy hn θ at hE
  have hxroot : Real.sqrt (∑ p, x p ^ 2) ≤
      2 * Real.sqrt (AntipodalLog.fourthEnergy n (periodize hn c) + ‖c‖ ^ 2 * pairEnergy hn c) := by
    apply (Real.sqrt_le_left (by positivity)).2
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    norm_num only [OfNat.ofNat_ne_zero, pow_succ, pow_zero, mul_one] at *
    exact hx
  have hyroot : Real.sqrt (∑ p, y p ^ 2) ≤ 2 * Real.sqrt (realEnergy hn θ) := by
    apply (Real.sqrt_le_left (by positivity)).2
    rw [hy, mul_pow, Real.sq_sqrt hE]
    nlinarith only [hE]
  have hprod := mul_le_mul hxroot hyroot (Real.sqrt_nonneg _) (by positivity)
  have hf := hs.trans (mul_le_mul_of_nonneg_left (hcs.trans hprod) (by norm_num : (0 : ℝ) ≤ 2))
  exact hf.trans_eq (by ring)

end StructuralNote.AngularFirstEnergy
