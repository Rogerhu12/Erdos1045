import StructuralNote.SignedPressureAngular
import EventualExact.SchurEnergyBounds

/-! Actual tangential center fields and the two signed angular sums in the pressure bound. -/

noncomputable section
open scoped BigOperators

namespace StructuralNote.SignedPressureTangential

open Erdos1045 Erdos1045.EventualExact Complex
open SchurSpectrum FiniteFourierLift DiscreteEnergy
open AngularObjectiveCurvature SignedPressureAngular

theorem frame_chord (n : ℕ) (i j : Fin n) :
    normSq ((starRingEnd ℂ) (SchurLift.frame n i) -
      (starRingEnd ℂ) (SchurLift.frame n j)) = normSq (root n i - root n j) := by
  rw [← map_sub, normSq_conj]
  simp only [SchurLift.frame, FourierMultiplier.character, mul_one, ← mul_sub, normSq_mul,
    LocalPhase.phase_normSq, one_mul, root]

theorem frame_mul_difference_le (c : Fin n → ℂ) (i j : Fin n) :
    normSq ((starRingEnd ℂ) (SchurLift.frame n i) * c i -
      (starRingEnd ℂ) (SchurLift.frame n j) * c j) ≤
        2 * normSq (c i - c j) + 2 * normSq (c j) * normSq (root n i - root n j) := by
  have he : (starRingEnd ℂ) (SchurLift.frame n i) * c i -
      (starRingEnd ℂ) (SchurLift.frame n j) * c j =
      (starRingEnd ℂ) (SchurLift.frame n i) * (c i - c j) +
        ((starRingEnd ℂ) (SchurLift.frame n i) -
          (starRingEnd ℂ) (SchurLift.frame n j)) * c j := by ring
  rw [he]
  have h := normSq_add_le ((starRingEnd ℂ) (SchurLift.frame n i) * (c i - c j))
    (((starRingEnd ℂ) (SchurLift.frame n i) - (starRingEnd ℂ) (SchurLift.frame n j)) * c j)
  rw [normSq_mul, normSq_mul, normSq_conj, SchurLift.frame_normSq, one_mul, frame_chord] at h
  nlinarith only [h]

theorem rotating_energy_le {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) :
    pairEnergy hn (fun j => (starRingEnd ℂ) (SchurLift.frame n j) * c j) ≤
      2 * pairEnergy hn c + (n : ℝ) * ∑ j, normSq (c j) := by
  have hp (i j : Fin n) :
      normSq ((starRingEnd ℂ) (SchurLift.frame n i) * c i -
        (starRingEnd ℂ) (SchurLift.frame n j) * c j) / normSq (root n i - root n j) ≤
      2 * (normSq (c i - c j) / normSq (root n i - root n j)) + 2 * normSq (c j) := by
    have h := div_le_div_of_nonneg_right (frame_mul_difference_le c i j)
      (normSq_nonneg (root n i - root n j))
    rw [add_div, mul_div_assoc, mul_div_assoc] at h
    have hd : normSq (root n i - root n j) / normSq (root n i - root n j) ≤ (1 : ℝ) :=
      div_self_le_one _
    have hb := mul_le_mul_of_nonneg_left hd
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (normSq_nonneg (c j)))
    rw [mul_one] at hb
    linarith only [h, hb]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hp i j))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  rw [pairEnergy_eq_chord_sum, pairEnergy_eq_chord_sum]
  change _ ≤ 2 * ((∑ i, ∑ j, normSq (c i - c j) / normSq (root n i - root n j)) / 2) + _
  simp only [root] at hs ⊢
  linarith only [hs]

theorem rotating_energy_le_six {n : ℕ} (hn : 2 ≤ n) (c : Fin n → ℂ)
    (hmean : ∑ j, c j = 0) :
    pairEnergy (by omega) (fun j => (starRingEnd ℂ) (SchurLift.frame n j) * c j) ≤
      6 * pairEnergy (by omega) c := by
  have hp := mean_zero_poincare hn c hmean
  have hsum : 0 ≤ ∑ j, normSq (c j) := Finset.sum_nonneg fun j _ => normSq_nonneg _
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h := rotating_energy_le (show 0 < n by omega) c
  nlinarith only [h, hp, mul_nonneg (show 0 ≤ (n : ℝ) - 2 by linarith) hsum]

theorem pairEnergy_add_le {n : ℕ} (hn : 0 < n) (c d : Fin n → ℂ) :
    pairEnergy hn (fun j => c j + d j) ≤ 2 * pairEnergy hn c + 2 * pairEnergy hn d := by
  have hp (i j : Fin n) := div_le_div_of_nonneg_right
    (normSq_add_le (c i - c j) (d i - d j)) (normSq_nonneg (root n i - root n j))
  simp_rw [show ∀ i j : Fin n, (c i - c j) + (d i - d j) =
    (c i + d i) - (c j + d j) by intros; ring] at hp
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hp i j))
  simp only [add_div, mul_div_assoc, Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  simp only [pairEnergy_eq_chord_sum]
  change _ ≤ 2 * ((∑ i, ∑ j, normSq (c i - c j) / normSq (root n i - root n j)) / 2) +
    2 * ((∑ i, ∑ j, normSq (d i - d j) / normSq (root n i - root n j)) / 2)
  simp only [root] at hs ⊢
  linarith only [hs]

def tangentialSum (n : ℕ) (c : Fin n → ℂ) (j : Fin n) : ℝ :=
  ((starRingEnd ℂ) (SchurLift.frame n j) * (c (finRotate n j) + c j)).im

theorem tangentialSum_norm_le (n : ℕ) (c : Fin n → ℂ) : ‖tangentialSum n c‖ ≤ 2 * ‖c‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro j
  have hf : ‖SchurLift.frame n j‖ = 1 := by
    have h := SchurLift.frame_normSq n j
    rw [normSq_eq_norm_sq] at h
    nlinarith [norm_nonneg (SchurLift.frame n j)]
  calc
    _ = |((starRingEnd ℂ) (SchurLift.frame n j) * (c (finRotate n j) + c j)).im| := Real.norm_eq_abs _
    _ ≤ ‖(starRingEnd ℂ) (SchurLift.frame n j) * (c (finRotate n j) + c j)‖ := abs_im_le_norm _
    _ = ‖c (finRotate n j) + c j‖ := by rw [norm_mul, norm_conj, hf, one_mul]
    _ ≤ ‖c (finRotate n j)‖ + ‖c j‖ := norm_add_le _ _
    _ ≤ 2 * ‖c‖ := by linarith [norm_le_pi_norm c (finRotate n j), norm_le_pi_norm c j]

theorem tangentialSum_energy_le {n : ℕ} (hn : 2 ≤ n) (c : Fin n → ℂ)
    (hmean : ∑ j, c j = 0) :
    realEnergy (by omega) (tangentialSum n c) ≤ 24 * pairEnergy (by omega) c := by
  have hm : (∑ j, (c (finRotate n j) + c j)) = 0 := by
    rw [Finset.sum_add_distrib, Equiv.sum_comp, hmean, add_zero]
  have h₁ := imaginary_energy_le (show 0 < n by omega)
    (fun j => (starRingEnd ℂ) (SchurLift.frame n j) * (c (finRotate n j) + c j))
  have h₂ := rotating_energy_le_six hn (fun j => c (finRotate n j) + c j) hm
  have h₃ := pairEnergy_add_le (show 0 < n by omega) (fun j => c (finRotate n j)) c
  rw [pairEnergy_rotate hn c] at h₃
  change realEnergy (by omega) (tangentialSum n c) ≤ _ at h₁
  linarith only [h₁, h₂, h₃]

open FourierMultiplier SchurLiftBounds SchurOperatorBounds

theorem pressure_product_energy_le {n : ℕ} (hn : 2 ≤ n) (heven : Even n)
    (q : Fin n → ℝ) (c : Fin n → ℂ) (hmean : ∑ j, c j = 0) :
    realEnergy (by omega) (fun j => operator n q j * tangentialSum n c j) ≤
      48 * ‖operator n q‖ ^ 2 * pairEnergy (by omega) c +
        16 * (n : ℝ) ^ 2 * ‖c‖ ^ 2 * meanSquare q := by
  have h := realEnergy_mul_le (show 0 < n by omega) (operator n q) (tangentialSum n c)
  have ht := tangentialSum_energy_le hn c hmean
  have htn := pow_le_pow_left₀ (norm_nonneg _) (tangentialSum_norm_le n c) 2
  have hg := pairEnergy_operator_le (show 0 < n by omega) heven q
  have h₁ := mul_le_mul_of_nonneg_left ht (show 0 ≤ 2 * ‖operator n q‖ ^ 2 by positivity)
  have h₂ := mul_le_mul htn hg (pairEnergy_nonneg (show 0 < n by omega) _)
    (show 0 ≤ (2 * ‖c‖) ^ 2 by positivity)
  change ‖tangentialSum n c‖ ^ 2 * realEnergy (by omega) (operator n q) ≤ _ at h₂
  nlinarith only [h, h₁, h₂]

/-- Both angular sums are bounded directly from the actual fields. -/
theorem signed_angular_pairings {n : ℕ} (hn : 2 ≤ n) (heven : Even n)
    (q θ : Fin n → ℝ) (c : Fin n → ℂ) (hmean : ∑ j, c j = 0) :
    |∑ j, |operator n q j| * (θ (successor (by omega) j) - θ j)| ≤
        8 * Real.pi / (n : ℝ) ^ 2 * Real.sqrt (2 * (n : ℝ) ^ 2 * meanSquare q) *
          Real.sqrt (realEnergy (by omega) θ) ∧
      |∑ j, operator n q j * tangentialSum n c j * (θ (successor (by omega) j) - θ j)| ≤
        8 * Real.pi / (n : ℝ) ^ 2 *
          Real.sqrt (48 * ‖operator n q‖ ^ 2 * pairEnergy (by omega) c +
            16 * (n : ℝ) ^ 2 * ‖c‖ ^ 2 * meanSquare q) *
          Real.sqrt (realEnergy (by omega) θ) := by
  have hga : realEnergy (by omega) (fun j => |operator n q j|) ≤
      2 * (n : ℝ) ^ 2 * meanSquare q :=
    (pairEnergy_abs_le (show 0 < n by omega) _).trans (pairEnergy_operator_le (by omega) heven q)
  constructor
  · refine (real_difference_pairing_le (show 0 < n by omega) (fun j => |operator n q j|) θ).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hga) (by positivity)) (Real.sqrt_nonneg _)
  · refine (real_difference_pairing_le (show 0 < n by omega)
      (fun j => operator n q j * tangentialSum n c j) θ).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (pressure_product_energy_le hn heven q c hmean))
        (by positivity)) (Real.sqrt_nonneg _)

def angularBudget {n : ℕ} (hn : 0 < n) (q θ : Fin n → ℝ) (c : Fin n → ℂ) : ℝ :=
  (2 * Real.pi ^ 2 / (n : ℝ) ^ 2 * Real.sqrt (2 * (n : ℝ) ^ 2 * meanSquare q) +
    Real.pi / n * Real.sqrt (48 * ‖operator n q‖ ^ 2 * pairEnergy hn c +
      16 * (n : ℝ) ^ 2 * ‖c‖ ^ 2 * meanSquare q)) * Real.sqrt (realEnergy hn θ)

/-- Includes the actual reciprocal-sine coefficients in formula (6.17). -/
theorem signed_angular_terms_le {n : ℕ} (hn : 2 ≤ n) (heven : Even n)
    (q θ : Fin n → ℝ) (c : Fin n → ℂ) (hmean : ∑ j, c j = 0) :
    (Real.pi / n) / (2 * Real.sin (Real.pi / n)) *
        (∑ j, |operator n q j| * (θ (successor (by omega) j) - θ j)) +
      (1 / (4 * Real.sin (Real.pi / n))) *
        (∑ j, operator n q j * tangentialSum n c j * (θ (successor (by omega) j) - θ j)) ≤
      angularBudget (by omega) q θ c := by
  have hs := SignedPressureRemainder.reciprocal_sine_le hn
  have hspos := hs.1
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha : (Real.pi / n) / (2 * Real.sin (Real.pi / n)) ≤ Real.pi / 4 := by
    have h := mul_le_mul_of_nonneg_left hs.2 (show 0 ≤ Real.pi / n by positivity)
    calc
      _ = Real.pi / n * (1 / (2 * Real.sin (Real.pi / n))) := by ring
      _ ≤ Real.pi / n * (n / 4) := h
      _ = _ := by field_simp
  have hb : 1 / (4 * Real.sin (Real.pi / n)) ≤ (n : ℝ) / 8 := by
    have he : 1 / (4 * Real.sin (Real.pi / n)) = (1 / (2 * Real.sin (Real.pi / n))) / 2 := by ring
    rw [he]
    linarith only [hs.2]
  have hh := signed_angular_pairings hn heven q θ c hmean
  have h₁ := mul_le_mul ha hh.1 (abs_nonneg _) (show 0 ≤ Real.pi / 4 by positivity)
  have h₂ := mul_le_mul hb hh.2 (abs_nonneg _) (show 0 ≤ (n : ℝ) / 8 by positivity)
  have h₃ := mul_le_mul_of_nonneg_left (le_abs_self
    (∑ j, |operator n q j| * (θ (successor (by omega) j) - θ j)))
      (show 0 ≤ (Real.pi / n) / (2 * Real.sin (Real.pi / n)) by positivity)
  have h₄ := mul_le_mul_of_nonneg_left (le_abs_self
    (∑ j, operator n q j * tangentialSum n c j * (θ (successor (by omega) j) - θ j)))
      (show 0 ≤ 1 / (4 * Real.sin (Real.pi / n)) by positivity)
  have hf := add_le_add (h₃.trans h₁) (h₄.trans h₂)
  refine hf.trans_eq ?_
  unfold angularBudget
  field_simp
  ring

end StructuralNote.SignedPressureTangential
