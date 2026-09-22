import StructuralNote.EdgeNormalForm
import StructuralNote.EdgeSpectralBounds
import EventualExact.DiscreteEnergyBounds

/-! The physical pair energy and the full normal/tangential edge spectrum. -/

noncomputable section
open scoped BigOperators

namespace StructuralNote.EdgeEnergyComparison

open Erdos1045 Erdos1045.EventualExact
open Complex FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open LocalTrigonometry EdgeCoordinates EdgeNormalForm

theorem ratio_le_leftWeight {n k : ℝ} (hn : 4 ≤ n) (hk : 3 ≤ k) (hkn : k ≤ n - 1) :
    LocalTrigonometry.pairRatio n k ≤ leftWeight n k := by
  have ha := mode_pos (by linarith : 1 < n) (by linarith : 0 < k) (by linarith : k < n)
  have hb := mode_pos (by linarith : 1 < n) (by linarith : 0 < k - 2) (by linarith : k - 2 < n)
  have hcross := mode_ratio_cross (by linarith : 1 < n) (by linarith : 0 < k - 2)
    (by linarith : k - 2 ≤ k) (by linarith : k < n)
  have hm := mul_le_mul_of_nonneg_right hcross
    (mul_nonneg (show 0 ≤ n - k by linarith) ha.le)
  unfold LocalTrigonometry.pairRatio leftWeight
  apply (div_le_div_iff₀ (mul_pos ha hb) (sq_pos_of_pos ha)).2
  nlinarith

theorem rightWeight_le_six_ratio {n k : ℝ} (hn : 4 ≤ n) (hk : 3 ≤ k)
    (hkn : 2 * k ≤ n + 2) (hl : 4 ≤ n + 2 - k) :
    rightWeight n k ≤ 6 * LocalTrigonometry.pairRatio n k := by
  have ha := mode_pos (by linarith : 1 < n) (by linarith : 0 < k) (by linarith : k < n)
  have hb := mode_pos (by linarith : 1 < n) (by linarith : 0 < k - 2) (by linarith : k - 2 < n)
  have hthree := paired_mode_le_three hn hk hkn
  have hmul := mul_le_mul_of_nonneg_left hthree (show 0 ≤ n + 2 - k by linarith)
  have hbase : (n + 2 - k) * mode n k ≤ 6 * (n - k) * mode n (k - 2) := by
    nlinarith [mul_nonneg (show 0 ≤ n - k - 2 by linarith) hb.le]
  have hm := mul_le_mul_of_nonneg_right hbase
    (mul_nonneg (show 0 ≤ k - 2 by linarith) hb.le)
  unfold rightWeight LocalTrigonometry.pairRatio
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (sq_pos_of_pos hb) (mul_pos ha hb)).2
  nlinarith

/-- The coefficient comparison from (4.13), including n=4's self-paired mode. -/
theorem integer_mode_comparison {n k : ℕ} (hn : 4 ≤ n) (hk : 3 ≤ k) (hkn : k < n) :
    LocalTrigonometry.pairRatio n k ≤ leftWeight n k ∧
      leftWeight n k ≤ 6 * LocalTrigonometry.pairRatio n k := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hknR : (k : ℝ) ≤ n - 1 := by
    have h : (k : ℝ) + 1 ≤ n := by exact_mod_cast (show k + 1 ≤ n by omega)
    linarith
  refine ⟨ratio_le_leftWeight hnR hkR hknR, ?_⟩
  by_cases hlow : 2 * k ≤ n + 2
  · have hlowR : 2 * (k : ℝ) ≤ n + 2 := by exact_mod_cast hlow
    have h := leftWeight_le_three_ratio hnR hkR hlowR
    have hp := pairRatio_pos hnR hkR hlowR
    linarith
  · have hk4 : (4 : ℝ) ≤ k := by exact_mod_cast (show 4 ≤ k by omega)
    have hlowR : (n : ℝ) + 2 ≤ 2 * k := by exact_mod_cast (show n + 2 ≤ 2 * k by omega)
    have h := rightWeight_le_six_ratio hnR
      (show (3 : ℝ) ≤ n + 2 - k by linarith)
      (show 2 * ((n : ℝ) + 2 - k) ≤ n + 2 by linarith)
      (show (4 : ℝ) ≤ n + 2 - ((n : ℝ) + 2 - k) by linarith)
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    rw [pairRatio_reflect hn0, ← leftWeight_reflect hn0,
      show (n : ℝ) + 2 - ((n : ℝ) + 2 - k) = k by ring] at h
    exact h

theorem scaled_weight_eq_ratio {n p : ℕ} (hp : EdgeWeights.Active n p) :
    (n : ℝ) * EdgeWeights.weight n p = LocalTrigonometry.pairRatio n ((p : ℝ) + 1) := by
  rcases EdgeWeights.active_bounds hp with ⟨hn, hp1, hpn, _⟩
  have hs : Real.sin (Real.pi / n) ≠ 0 :=
    (base_sine_pos (by linarith : (1 : ℝ) < n)).ne'
  rw [EdgeWeights.weight, if_pos hp]
  unfold LocalTrigonometry.pairRatio mode
  rw [show (p : ℝ) + 1 - 2 = p - 1 by ring]
  field_simp [hn.ne']
  ring

theorem amplitude_weight_identity {n : ℕ} (hn : 2 ≤ n) (u : Fin n → ℂ)
    (p : Fin n) (hp : EdgeWeights.Active n p) :
    leftWeight n ((p : ℝ) + 1) * normSq (amplitude (by omega) u p) =
      ((p : ℝ) + 1) * ((n : ℝ) - p - 1) * normSq (centerCoefficient (by omega) u p) := by
  have hbounds := EdgeWeights.active_bounds hp
  have hm := mode_pos (by linarith : (1 : ℝ) < n)
    (by linarith : (0 : ℝ) < p + 1) hbounds.2.2.1
  rw [amplitude_eq hn, LocalSpectrum.fullAmplitude, Complex.normSq_mul, Complex.normSq_ofReal]
  unfold leftWeight
  field_simp [hm.ne']
  ring

/-- Both inequalities concern the actual Fourier coefficients of the input column. -/
theorem physical_mode_comparison {n : ℕ} (hn : 2 ≤ n) (u : Fin n → ℂ)
    (p : Fin n) (hp : EdgeWeights.Active n p) :
    (n : ℝ) * EdgeWeights.weight n p * normSq (amplitude (by omega) u p) ≤
        ((p : ℝ) + 1) * ((n : ℝ) - p - 1) * normSq (centerCoefficient (by omega) u p) ∧
      ((p : ℝ) + 1) * ((n : ℝ) - p - 1) * normSq (centerCoefficient (by omega) u p) ≤
        6 * ((n : ℝ) * EdgeWeights.weight n p * normSq (amplitude (by omega) u p)) := by
  have hb := integer_mode_comparison (n := n) (k := p.val + 1)
    (by have := hp.1; have := hp.2; omega) (by have := hp.1; omega) (by have := hp.2; omega)
  simp only [Nat.cast_add, Nat.cast_one] at hb
  rw [← scaled_weight_eq_ratio hp] at hb
  have hnorm := normSq_nonneg (amplitude (by omega) u p)
  have hlow := mul_le_mul_of_nonneg_right hb.1 hnorm
  have hupp := mul_le_mul_of_nonneg_right hb.2 hnorm
  rw [amplitude_weight_identity hn u p hp] at hlow hupp
  exact ⟨hlow, by nlinarith [hupp]⟩

/-- The k=2 physical vertex mode, before identifying its normal projection. -/
def firstEnergy {n : ℕ} (hn : 0 < n) (u : Fin n → ℂ) : ℝ :=
  (n : ℝ) * ((n : ℝ) - 2) * normSq (centerCoefficient hn u 1)

def interiorEnergy {n : ℕ} (hn : 0 < n) (u : Fin n → ℂ) : ℝ :=
  (n : ℝ) / 2 * ∑ p : Fin n,
    (n : ℝ) * EdgeWeights.weight n p * normSq (amplitude hn u p)

theorem shifted_energy_spectrum {n : ℕ} (hn : 0 < n) (u : Fin n → ℂ) :
    pairEnergy hn u = (n : ℝ) / 2 * ∑ p : Fin n,
      ((p : ℝ) + 1) * ((n : ℝ) - p - 1) * normSq (centerCoefficient hn u p) := by
  have hA : pairEnergy hn u = LocalSpectrum.fullA n (centerCoefficient hn u) := by
    exact (LocalDFT.energyA_eq_fourier ClosedFourier.dftInversion hn _ (periodize_periodic hn u)).trans
      (LocalHessian.fullA_eq_geometric hn (ClosedFourier.orthogonality n hn) _).symm
  rw [hA, LocalSpectrum.fullA, ← Fin.sum_univ_eq_sum_range
    (fun p => ((p : ℝ) + 1) * ((n : ℝ) - ((p : ℝ) + 1)) * normSq (centerCoefficient hn u p)) n]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  congr 2
  ring

theorem physical_energy_comparison {n : ℕ} (hn : 3 ≤ n) (u : Fin n → ℂ)
    (hfirst : centerCoefficient (by omega) u 0 = 0) :
    firstEnergy (by omega) u + interiorEnergy (by omega) u ≤ pairEnergy (by omega) u ∧
      pairEnergy (by omega) u ≤ firstEnergy (by omega) u + 6 * interiorEnergy (by omega) u := by
  let b := centerCoefficient (by omega : 0 < n) u
  let a := amplitude (by omega : 0 < n) u
  let F (p : Fin n) := if p.val = 1 then 2 * ((n : ℝ) - 2) * normSq (b 1) else 0
  let M (p : Fin n) := (n : ℝ) * EdgeWeights.weight n p * normSq (a p)
  let A (p : Fin n) := ((p : ℝ) + 1) * ((n : ℝ) - p - 1) * normSq (b p)
  have hpoint (p : Fin n) : F p + M p ≤ A p ∧ A p ≤ F p + 6 * M p := by
    by_cases hp : EdgeWeights.Active n p
    · have hp1 : p.val ≠ 1 := by have := hp.1; omega
      have h := physical_mode_comparison (by omega) u p hp
      simpa only [F, M, A, if_neg hp1, zero_add, b, a] using h
    · have hb : p.val = 0 ∨ p.val = 1 ∨ p.val + 1 = n := by
        have := p.isLt
        unfold EdgeWeights.Active at hp
        omega
      have hz : M p = 0 := by simp [M, EdgeWeights.weight_eq_zero hp]
      rw [hz, add_zero, mul_zero, add_zero]
      suffices he : F p = A p from ⟨he.le, he.ge⟩
      rcases hb with h0 | h1 | hlast
      · simp [F, A, h0, b, hfirst]
      · simp only [F, A, h1, if_true, Nat.cast_one]
        ring
      · have h1 : p.val ≠ 1 := by omega
        have hr : (n : ℝ) - p - 1 = 0 := by
          have hh : (p : ℝ) + 1 = n := by exact_mod_cast hlast
          linarith
        simp [F, A, h1, hr]
  have hsumF : (∑ p, F p) = 2 * ((n : ℝ) - 2) * normSq (b 1) := by
    let oneIndex : Fin n := ⟨1, by omega⟩
    apply Finset.sum_eq_single oneIndex
    · intro p _ hp
      have hp1 : p.val ≠ 1 := by intro h; apply hp; exact Fin.ext h
      simp [F, hp1]
    · simp
  have hl := Finset.sum_le_sum (s := Finset.univ) (fun p _ => (hpoint p).1)
  have hu := Finset.sum_le_sum (s := Finset.univ) (fun p _ => (hpoint p).2)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsumF] at hl hu
  have hn0 : (0 : ℝ) ≤ n / 2 := by positivity
  have hlo := mul_le_mul_of_nonneg_left hl hn0
  have hup := mul_le_mul_of_nonneg_left hu hn0
  rw [shifted_energy_spectrum (by omega)]
  change firstEnergy (by omega) u + interiorEnergy (by omega) u ≤ (n : ℝ) / 2 * ∑ p, A p ∧
    (n : ℝ) / 2 * ∑ p, A p ≤ firstEnergy (by omega) u + 6 * interiorEnergy (by omega) u
  unfold firstEnergy interiorEnergy
  change (n : ℝ) * ((n : ℝ) - 2) * normSq (b 1) + (n : ℝ) / 2 * ∑ p, M p ≤ _ ∧
    _ ≤ (n : ℝ) * ((n : ℝ) - 2) * normSq (b 1) + 6 * ((n : ℝ) / 2 * ∑ p, M p)
  constructor <;> nlinarith

theorem midpoint_norm_sum {n : ℕ} [NeZero n] (u : Fin n → ℂ)
    (p : Fin n) (hp : p ≠ 0) :
    normSq (midpointCoefficient (normal (NeZero.pos n) u) p) +
        normSq (midpointCoefficient (tangent (NeZero.pos n) u) p) =
      (n : ℝ) ^ 2 / 2 * (normSq (amplitude (NeZero.pos n) u p) +
        normSq (amplitude (NeZero.pos n) u (-p))) := by
  rw [midpoint_normal u p hp, midpoint_tangent u p hp]
  simp [Complex.normSq_apply]
  ring

theorem weight_neg {n : ℕ} [NeZero n] (p : Fin n) :
    EdgeWeights.weight n (-p).val = EdgeWeights.weight n p := by
  by_cases hp : p = 0
  · subst p
    simp
  · rw [Fin.val_neg, if_neg hp]
    exact EdgeWeights.weight_reflect p.isLt.le

theorem interiorEnergy_eq_values {n : ℕ} (hn : 2 ≤ n) (u : Fin n → ℂ) :
    interiorEnergy (by omega) u = value (normal (by omega) u) + value (tangent (by omega) u) := by
  let : NeZero n := ⟨by omega⟩
  have hs : (∑ p : Fin n, EdgeWeights.weight n p * normSq (amplitude (by omega) u (-p))) =
      ∑ p : Fin n, EdgeWeights.weight n p * normSq (amplitude (by omega) u p) := by
    have h := Equiv.sum_comp (Equiv.neg (Fin n))
      (fun p => EdgeWeights.weight n p * normSq (amplitude (by omega) u p))
    simpa only [Equiv.neg_apply, weight_neg] using h
  have hterm (p : Fin n) :
      EdgeWeights.weight n p * normSq (midpointCoefficient (normal (by omega) u) p) +
        EdgeWeights.weight n p * normSq (midpointCoefficient (tangent (by omega) u) p) =
      (n : ℝ) ^ 2 / 2 * (EdgeWeights.weight n p * normSq (amplitude (by omega) u p) +
        EdgeWeights.weight n p * normSq (amplitude (by omega) u (-p))) := by
    by_cases hp : p = 0
    · subst p
      simp [EdgeWeights.weight_zero]
    · rw [← mul_add, midpoint_norm_sum u p hp]
      ring
  symm
  unfold value
  rw [← mul_add, ← Finset.sum_add_distrib]
  simp_rw [hterm]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, hs]
  unfold interiorEnergy
  have he : (∑ p : Fin n, (n : ℝ) * EdgeWeights.weight n p * normSq (amplitude (by omega) u p)) =
      (n : ℝ) * ∑ p : Fin n, EdgeWeights.weight n p * normSq (amplitude (by omega) u p) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros
    ring
  rw [he]
  ring

/-- Both sides of the manuscript's physical energy comparison. The first term
is explicitly the k=2 vertex mode, and every other term is an actual edge form. -/
theorem energy_comparison {n : ℕ} (hn : 3 ≤ n) (u : Fin n → ℂ)
    (hfirst : centerCoefficient (by omega) u 0 = 0) :
    firstEnergy (by omega) u + value (normal (by omega) u) + value (freeTangent (by omega) u) ≤
        pairEnergy (by omega) u ∧
      pairEnergy (by omega) u ≤ firstEnergy (by omega) u +
        6 * (value (normal (by omega) u) + value (freeTangent (by omega) u)) := by
  have h := physical_energy_comparison hn u hfirst
  rw [interiorEnergy_eq_values (by omega)] at h
  simp only [freeTangent, value_sub_J (show 2 ≤ n by omega)]
  constructor
  · linarith [h.1]
  · exact h.2

def firstProjection {n : ℕ} (q : Fin n → ℝ) (j : Fin n) : ℝ :=
  2 * (firstCoefficient q * frame n j).re

def firstMass {n : ℕ} (q : Fin n → ℝ) : ℝ := 2 * normSq (firstCoefficient q)

def chi (n : ℕ) : ℝ := ((n : ℝ) - 2) / (2 * n * Real.cos (Real.pi / n) ^ 2)

theorem firstProjection_meanSquare {n : ℕ} (hn : 3 ≤ n) (q : Fin n → ℝ) :
    SchurLiftBounds.meanSquare (firstProjection q) = firstMass q := by
  have h := SchurLiftBounds.imaginary_frame_energy hn (I * firstCoefficient q)
  simp only [mul_assoc, Complex.I_mul_im, Complex.normSq_mul, Complex.normSq_I, one_mul] at h
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  unfold SchurLiftBounds.meanSquare firstProjection firstMass
  simp only [mul_pow, ← Finset.mul_sum]
  rw [h]
  field_simp

theorem mode_two {n : ℕ} (hn : 2 ≤ n) :
    mode n 2 = 2 * Real.cos (Real.pi / n) := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hs := (base_sine_pos hnR).ne'
  unfold mode
  rw [show 2 * Real.pi / (n : ℝ) = 2 * (Real.pi / n) by ring, Real.sin_two_mul]
  field_simp

theorem firstMass_normal {n : ℕ} (hn : 3 ≤ n) (u : Fin n → ℂ) :
    firstMass (normal (by omega) u) = 2 * (n : ℝ) ^ 2 * Real.cos (Real.pi / n) ^ 2 *
      normSq (centerCoefficient (by omega) u 1) := by
  let : NeZero n := ⟨by omega⟩
  let p : Fin n := ⟨1, by omega⟩
  have hp0 : p ≠ 0 := by simp [p]
  have hlast : amplitude (by omega) u (-p) = 0 := by
    rw [amplitude_eq (by omega), LocalSpectrum.fullAmplitude]
    have hl : ((-p).val : ℝ) + 1 = n := by
      rw [Fin.val_neg, if_neg hp0, Nat.cast_sub (by omega : p.val ≤ n)]
      simp [p]
    rw [hl]
    unfold mode
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    simp [hn0]
  unfold firstMass
  rw [firstCoefficient_eq_midpoint (by omega)]
  change 2 * normSq (midpointCoefficient (normal (by omega) u) p) = _
  rw [midpoint_normal u p hp0, hlast, map_zero, add_zero,
    Complex.normSq_mul, Complex.normSq_div, Complex.normSq_mul]
  simp only [Complex.normSq_I, Complex.normSq_natCast, one_mul]
  rw [amplitude_eq (by omega), LocalSpectrum.fullAmplitude,
    Complex.normSq_mul, Complex.normSq_ofReal]
  rw [show normSq (2 : ℂ) = 4 by norm_num]
  norm_num only [p, Nat.cast_one]
  change 2 * (((n : ℝ) * n) / 4 *
    (mode n 2 * mode n 2 * normSq (centerCoefficient (by omega) u 1))) = _
  rw [mode_two (by omega)]
  ring

theorem cosine_half_bound {n : ℕ} (hn : 4 ≤ n) :
    (1 / 2 : ℝ) ≤ Real.cos (Real.pi / n) ^ 2 := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have h := EdgeSpectralBounds.endpointBudget_le hnR
  have hm := mul_nonneg (show 0 ≤ (n : ℝ) - 4 by linarith) (sq_nonneg (Real.sin (Real.pi / n)))
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi / n)]

theorem chi_bounds {n : ℕ} (hn : 3 ≤ n) : 0 ≤ chi n ∧ chi n ≤ 1 := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hc : 0 < Real.cos (Real.pi / n) ^ 2 := by
    by_cases h4 : 4 ≤ n
    · linarith [cosine_half_bound h4]
    · have he : n = 3 := by omega
      subst n
      norm_num [Real.cos_pi_div_three]
  have hd : 0 < 2 * (n : ℝ) * Real.cos (Real.pi / n) ^ 2 := by positivity
  unfold chi
  refine ⟨div_nonneg (by linarith) hd.le, (div_le_one hd).2 ?_⟩
  by_cases h4 : 4 ≤ n
  · have h := mul_le_mul_of_nonneg_left (cosine_half_bound h4) (show 0 ≤ 2 * (n : ℝ) by positivity)
    linarith
  · have he : n = 3 := by omega
    subst n
    norm_num [Real.cos_pi_div_three]

/-- The exceptional mode is exactly the paper's chi times first-harmonic mass. -/
theorem firstEnergy_eq_chi {n : ℕ} (hn : 3 ≤ n) (u : Fin n → ℂ) :
    firstEnergy (by omega) u = chi n * firstMass (normal (by omega) u) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hc : Real.cos (Real.pi / n) ≠ 0 := by
    by_cases h4 : 4 ≤ n
    · intro hz
      have h := cosine_half_bound h4
      norm_num [hz] at h
    · have he : n = 3 := by omega
      subst n
      norm_num [Real.cos_pi_div_three]
  rw [firstMass_normal hn]
  unfold firstEnergy chi
  field_simp

theorem firstEnergy_le_firstMass {n : ℕ} (hn : 3 ≤ n) (u : Fin n → ℂ) :
    firstEnergy (by omega) u ≤ firstMass (normal (by omega) u) := by
  rw [firstEnergy_eq_chi hn]
  exact mul_le_of_le_one_left (mul_nonneg (by norm_num) (normSq_nonneg _)) (chi_bounds hn).2

/-- Formula (4.13) using the actual real first-harmonic projection P1. -/
theorem energy_comparison_projection {n : ℕ} (hn : 3 ≤ n) (u : Fin n → ℂ)
    (hfirst : centerCoefficient (by omega) u 0 = 0) :
    chi n * SchurLiftBounds.meanSquare (firstProjection (normal (by omega) u)) +
        value (normal (by omega) u) + value (freeTangent (by omega) u) ≤ pairEnergy (by omega) u ∧
      pairEnergy (by omega) u ≤
        chi n * SchurLiftBounds.meanSquare (firstProjection (normal (by omega) u)) +
          6 * (value (normal (by omega) u) + value (freeTangent (by omega) u)) := by
  rw [firstProjection_meanSquare hn, ← firstEnergy_eq_chi hn]
  exact energy_comparison hn u hfirst

theorem midpoint_parseval {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) :
    (∑ p, normSq (midpointCoefficient q p)) = SchurLiftBounds.meanSquare q := by
  simp_rw [midpointCoefficient_normSq]
  exact SchurOperatorBounds.realCoefficient_parseval hn q

/-- The first harmonic has zero spectral weight and is retained explicitly. -/
theorem value_with_firstMass_le {n : ℕ} (hn : 3 ≤ n) (q : Fin n → ℝ) :
    6 * value q + (((n : ℝ) - 1) / n) * firstMass q ≤
      (((n : ℝ) - 1) / n) * SchurLiftBounds.meanSquare q := by
  let : NeZero n := ⟨by omega⟩
  let p₁ : Fin n := ⟨1, by omega⟩
  let s : ℝ := ((n : ℝ) - 1) / n
  let F (p : Fin n) := normSq (midpointCoefficient q p)
  have hp0 : p₁ ≠ 0 := by simp [p₁]
  have hpneg : p₁ ≠ -p₁ := by
    intro he
    have hv := congrArg Fin.val he
    rw [Fin.val_neg, if_neg hp0] at hv
    dsimp [p₁] at hv
    omega
  have hzero : EdgeWeights.weight n p₁ = 0 := EdgeWeights.weight_one n
  have hnegzero : EdgeWeights.weight n (-p₁).val = 0 := by rw [weight_neg, hzero]
  have hpoint (p : Fin n) :
      3 * (EdgeWeights.weight n p * F p) +
          (if p = p₁ then s * F p else 0) + (if p = -p₁ then s * F p else 0) ≤ s * F p := by
    by_cases h1 : p = p₁
    · subst p
      simp [hzero, hpneg]
    · by_cases hneg : p = -p₁
      · subst p
        simp [hnegzero, hpneg.symm]
      · simp only [if_neg h1, if_neg hneg, add_zero]
        have h := mul_le_mul_of_nonneg_right (EdgeSpectralBounds.weight_le_s_over_three hn p)
          (normSq_nonneg (midpointCoefficient q p))
        change _ ≤ s / 3 * F p at h
        linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun p _ => hpoint p)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at hsum
  have hmass : F p₁ + F (-p₁) = firstMass q := by
    dsimp [F]
    rw [midpointCoefficient_neg q p₁ hp0, Complex.normSq_neg, Complex.normSq_conj]
    rw [← firstCoefficient_eq_midpoint (by omega)]
    unfold firstMass
    ring
  have hparse : (∑ p, F p) = SchurLiftBounds.meanSquare q := midpoint_parseval (by omega) q
  have hv : 2 * value q = ∑ p : Fin n, EdgeWeights.weight n p * F p := by
    unfold value
    dsimp [F]
    ring
  rw [hparse, ← hv] at hsum
  have hm := congrArg (fun x => s * x) hmass
  change 6 * value q + s * firstMass q ≤ s * SchurLiftBounds.meanSquare q
  nlinarith

theorem energy_le_normalMass_add_free {n : ℕ} (hn : 3 ≤ n) (u : Fin n → ℂ)
    (hfirst : centerCoefficient (by omega) u 0 = 0) :
    pairEnergy (by omega) u ≤ SchurLiftBounds.meanSquare (normal (by omega) u) +
      6 * value (freeTangent (by omega) u) := by
  have hA := (energy_comparison hn u hfirst).2
  have hfirstMass := firstEnergy_le_firstMass hn u
  have hweight := value_with_firstMass_le hn (normal (by omega) u)
  have hproj := SchurLiftBounds.firstCoefficient_bound hn (normal (by omega) u)
  change firstMass (normal (by omega) u) ≤ SchurLiftBounds.meanSquare (normal (by omega) u) at hproj
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : ((n : ℝ) - 1) / n ≤ 1 := (div_le_one hnR).2 (by linarith)
  have hm := mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hproj)
  nlinarith

theorem deficit_eq_mass {n : ℕ} (hn : 3 ≤ n) (u : Fin n → ℂ)
    (hfirst : centerCoefficient (by omega) u 0 = 0) :
    deficit (by omega) u = (((n : ℝ) - 1) / n) / 2 *
      SchurLiftBounds.meanSquare (normal (by omega) u) - value (normal (by omega) u) +
      value (freeTangent (by omega) u) := by
  rw [freeTangent, value_sub_J (show 2 ≤ n by omega)]
  have h := deficit_identity (show 2 ≤ n by omega) u hfirst
  change deficit (by omega) u = ((n : ℝ) - 1) / (2 * n) *
    SchurLiftBounds.meanSquare (normal (by omega) u) - value (normal (by omega) u) +
    value (tangent (by omega) u) at h
  rw [h]
  ring

theorem value_three_zero (q : Fin 3 → ℝ) : value q = 0 := by
  have hw (p : Fin 3) : EdgeWeights.weight 3 p = 0 := by
    apply EdgeWeights.weight_eq_zero
    intro hp
    have := hp.1
    have := hp.2
    omega
  simp [value, hw]

/-- The sharp enough physical coercivity (4.18), with no energy estimate assumed. -/
theorem deficit_coercive {n : ℕ} (hn : 3 ≤ n) (u : Fin n → ℂ)
    (hfirst : centerCoefficient (by omega) u 0 = 0) :
    (pairEnergy (by omega) u + (n : ℝ) * LocalDFT.energyB n (periodize (by omega) u)) / 8 ≤
      deficit (by omega) u := by
  have hM : SchurLiftBounds.meanSquare (normal (by omega) u) =
      (n : ℝ) * LocalDFT.energyB n (periodize (by omega) u) :=
    normal_mean_square (by omega) u
  rw [← hM, deficit_eq_mass hn u hfirst]
  have hA := energy_le_normalMass_add_free hn u hfirst
  have hM0 := SchurLiftBounds.meanSquare_nonneg (normal (by omega) u)
  have hV0 := value_nonneg (freeTangent (by omega) u)
  by_cases h4 : 4 ≤ n
  · have hnR : (4 : ℝ) ≤ n := by exact_mod_cast h4
    have hs : (3 / 4 : ℝ) ≤ ((n : ℝ) - 1) / n := by
      apply (le_div_iff₀ (by linarith : (0 : ℝ) < n)).2
      linarith
    have hs0 : 0 ≤ ((n : ℝ) - 1) / n := by linarith
    have hweight := value_with_firstMass_le hn (normal (by omega) u)
    have hfirst0 : 0 ≤ firstMass (normal (by omega) u) :=
      mul_nonneg (by norm_num) (normSq_nonneg _)
    have h6 : 6 * value (normal (by omega) u) ≤
        (((n : ℝ) - 1) / n) * SchurLiftBounds.meanSquare (normal (by omega) u) := by
      nlinarith [mul_nonneg hs0 hfirst0]
    have hm := mul_le_mul_of_nonneg_right hs hM0
    nlinarith
  · have he : n = 3 := by omega
    subst n
    rw [value_three_zero] at hA
    rw [value_three_zero, value_three_zero]
    norm_num at hA ⊢
    nlinarith

end StructuralNote.EdgeEnergyComparison
