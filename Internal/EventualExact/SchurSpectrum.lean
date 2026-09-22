import EventualExact.SchurLift
import Erdos1045.ClosedDFT
import Erdos1045.ClosedGeometricSine

/-! The finite Schur calculation for actual geometric center columns. -/

noncomputable section

open scoped BigOperators

namespace Erdos1045.EventualExact.SchurSpectrum

open Complex FourierMultiplier FiniteFourierLift SchurLift

local notation "conj" => (starRingEnd ℂ)

def midpointCharacter (n p : ℕ) (j : Fin n) : ℂ :=
  LocalPhase.phase n p * character n p j

def midpointTransform {n : ℕ} (f : Fin n → ℂ) (p : Fin n) : ℂ :=
  (∑ j, f j * conj (midpointCharacter n p j)) / n

def midpointSynthesis {n : ℕ} (a : Fin n → ℂ) (j : Fin n) : ℂ :=
  ∑ p, a p * midpointCharacter n p j

theorem midpointTransform_eq {n : ℕ} (f : Fin n → ℂ) (p : Fin n) :
    midpointTransform f p = coefficient f p * conj (LocalPhase.phase n p) := by
  simp only [midpointTransform, midpointCharacter, coefficient, map_mul]
  rw [div_mul_eq_mul_div, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intros
  ring

theorem phase_mul_conj (n p : ℕ) : LocalPhase.phase n p * conj (LocalPhase.phase n p) = 1 := by
  rw [Complex.mul_conj, LocalPhase.phase_normSq]
  rfl

theorem midpointTransform_synthesis {n : ℕ} (hn : 0 < n)
    (a : Fin n → ℂ) (p : Fin n) : midpointTransform (midpointSynthesis a) p = a p := by
  have he : midpointSynthesis a = synthesis (fun p => a p * LocalPhase.phase n p) := by
    funext j
    unfold midpointSynthesis synthesis midpointCharacter
    apply Finset.sum_congr rfl
    intros
    ring
  rw [midpointTransform_eq, he, coefficient_synthesis hn, mul_assoc, phase_mul_conj, mul_one]

theorem midpointSynthesis_transform {n : ℕ} (hn : 0 < n) (f : Fin n → ℂ) (j : Fin n) :
    midpointSynthesis (midpointTransform f) j = f j := by
  rw [← synthesis_coefficient hn f j]
  unfold midpointSynthesis synthesis midpointCharacter
  apply Finset.sum_congr rfl
  intro p _
  rw [midpointTransform_eq]
  have hp := phase_mul_conj n p
  calc
    _ = coefficient f p * (LocalPhase.phase n p * conj (LocalPhase.phase n p)) *
        character n p j := by ring
    _ = _ := by rw [hp, mul_one]

theorem midpointTransform_real {n : ℕ} (f : Fin n → ℝ) (p : Fin n) :
    midpointTransform (fun j => (f j : ℂ)) p = midpointCoefficient f p := rfl

theorem midpointTransform_add {n : ℕ} (f g : Fin n → ℂ) (p : Fin n) :
    midpointTransform (f + g) p = midpointTransform f p + midpointTransform g p := by
  simp [midpointTransform, add_mul, Finset.sum_add_distrib, add_div]

theorem midpointTransform_sub {n : ℕ} (f g : Fin n → ℂ) (p : Fin n) :
    midpointTransform (f - g) p = midpointTransform f p - midpointTransform g p := by
  simp [midpointTransform, sub_mul, Finset.sum_sub_distrib, sub_div]

theorem midpointTransform_mul {n : ℕ} (z : ℂ) (f : Fin n → ℂ) (p : Fin n) :
    midpointTransform (fun j => z * f j) p = z * midpointTransform f p := by
  simp [midpointTransform, mul_assoc, ← Finset.mul_sum]
  ring

theorem phase_neg {n : ℕ} [NeZero n] (p : Fin n) (hp : p ≠ 0) :
    LocalPhase.phase n (-p).val = -conj (LocalPhase.phase n p) := by
  have he : p.val + (-p).val = n := by
    rw [Fin.val_neg, if_neg hp]
    omega
  have hprod := LocalPhase.phase_product (NeZero.pos n) he
  apply mul_left_cancel₀ (show LocalPhase.phase n p ≠ 0 from Complex.exp_ne_zero _)
  rw [hprod, mul_neg, phase_mul_conj]

theorem midpointCharacter_neg {n : ℕ} [NeZero n] (p : Fin n) (hp : p ≠ 0) (j : Fin n) :
    midpointCharacter n (-p).val j = -conj (midpointCharacter n p j) := by
  simp only [midpointCharacter, phase_neg p hp, character_neg, map_mul, neg_mul]

theorem midpointTransform_conj {n : ℕ} [NeZero n] (f : Fin n → ℂ)
    (p : Fin n) (hp : p ≠ 0) :
    midpointTransform (fun j => conj (f j)) p = -conj (midpointTransform f (-p)) := by
  simp [midpointTransform, midpointCharacter_neg p hp, Finset.sum_neg_distrib]
  ring

theorem midpointCoefficient_neg {n : ℕ} [NeZero n] (q : Fin n → ℝ)
    (p : Fin n) (hp : p ≠ 0) :
    midpointCoefficient q (-p) = -conj (midpointCoefficient q p) := by
  have h := midpointTransform_conj (fun j => (q j : ℂ)) p hp
  simp only [Complex.conj_ofReal, midpointTransform_real] at h
  have h' := congrArg (fun z : ℂ => -conj z) h
  simpa using h'.symm

theorem midpointTransform_imaginary {n : ℕ} [NeZero n] (f : Fin n → ℂ)
    (p : Fin n) (hp : p ≠ 0) :
    midpointTransform (fun j => ((-(n : ℝ) * (f j).im : ℝ) : ℂ)) p =
      blockConstraint n (midpointTransform f p) (midpointTransform f (-p)) := by
  have he : (fun j => ((-(n : ℝ) * (f j).im : ℝ) : ℂ)) =
      (fun j => (Complex.I * n / 2) * (f j - conj (f j))) := by
    funext j
    apply Complex.ext
    · simp
      ring
    · simp
  rw [he, midpointTransform_mul]
  change _ * midpointTransform (f - fun j => conj (f j)) p = _
  rw [midpointTransform_sub, midpointTransform_conj f p hp]
  simp [blockConstraint]

def periodize {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) (j : ℕ) : ℂ :=
  c ⟨j % n, Nat.mod_lt _ hn⟩

theorem periodize_fin {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) (j : Fin n) :
    periodize hn c j = c j := by
  simp [periodize, Nat.mod_eq_of_lt j.isLt]

theorem periodize_periodic {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) :
    Function.Periodic (periodize hn c) n := by
  intro j
  simp [periodize, Nat.add_mod_right]

def centerCoefficient {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) (p : ℕ) : ℂ :=
  LocalDFT.coefficient n (periodize hn c) p

theorem centerCoefficient_eq {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) (p : ℕ) :
    centerCoefficient hn c p =
      (∑ j : Fin n, c j * conj (character n (p + 1) j)) / n := by
  unfold centerCoefficient LocalDFT.coefficient
  rw [← Fin.sum_univ_eq_sum_range (fun j => periodize hn c j *
    conj (LocalPhase.regularRoot n ^ (j * (p + 1)))) n]
  simp only [periodize_fin, character]

def edgeRatio {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) (j : Fin n) : ℂ :=
  LocalDFT.pairRatio n (periodize hn c) j 1

theorem edgeRatio_eq_difference {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) (j : Fin n) :
    edgeRatio hn c j = difference hn c j /
      difference hn (fun j => character n 1 j) j := by
  unfold edgeRatio LocalDFT.pairRatio difference successor
  simp only [periodize, character, Nat.mul_one, Nat.mod_eq_of_lt j.isLt]
  rw [ClosedFourier.root_pow_mod hn (j.val + 1)]

def amplitude {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) : Fin n → ℂ :=
  midpointTransform (edgeRatio hn c)

theorem edgeRatio_expansion {n : ℕ} (hn : 2 ≤ n) (c : Fin n → ℂ) :
    edgeRatio (by omega) c = midpointSynthesis (fun p : Fin n =>
      LocalSpectrum.fullAmplitude n (centerCoefficient (by omega) c) p) := by
  funext j
  rw [edgeRatio, ← LocalDFT.ratioFourier_eq_pairRatio ClosedFourier.dftInversion
    (by omega) _ (periodize_periodic _ _) (by omega) (by omega)]
  unfold LocalFourier.ratioFourier midpointSynthesis
  change (∑ r ∈ Finset.range n, (centerCoefficient (by omega) c r *
    LocalFourier.geom (r + 1) (LocalPhase.regularRoot n ^ 1)) *
      LocalPhase.regularRoot n ^ (j.val * r)) = _
  rw [← Fin.sum_univ_eq_sum_range (fun r =>
    (centerCoefficient (by omega) c r * LocalFourier.geom (r + 1)
      (LocalPhase.regularRoot n ^ 1)) * LocalPhase.regularRoot n ^ (j.val * r)) n]
  apply Finset.sum_congr rfl
  intro p _
  rw [pow_one, LocalPhase.geom_shifted ClosedFourier.geometricSine hn]
  unfold LocalSpectrum.fullAmplitude midpointCharacter character
  ring

/-- The midpoint coefficients are exactly the actual sine-rescaled center coefficients. -/
theorem amplitude_eq {n : ℕ} (hn : 2 ≤ n) (c : Fin n → ℂ) (p : Fin n) :
    amplitude (by omega) c p = LocalSpectrum.fullAmplitude n (centerCoefficient (by omega) c) p := by
  unfold amplitude
  rw [edgeRatio_expansion hn, midpointTransform_synthesis (by omega)]

def HalfPeriodic {m : ℕ} (hm : 0 < m) (c : Fin (2 * m) → ℂ) : Prop :=
  ∀ j, c (halfTurn hm j) = c j

theorem centerCoefficient_even_zero {m : ℕ} (hm : 0 < m) (c : Fin (2 * m) → ℂ)
    (hc : HalfPeriodic hm c) (p : ℕ) (hp : Even p) :
    centerCoefficient (by omega) c p = 0 := by
  change ∀ j, c (halfTurn hm j) = c j at hc
  have ho : Odd (p + 1) := hp.add_odd (by decide)
  have hs := Equiv.sum_comp
    (Equiv.ofBijective (halfTurn hm) (halfTurn_involutive hm).bijective)
    (fun j => c j * conj (character (2 * m) (p + 1) j))
  have hs' : (∑ j, c j * conj (character (2 * m) (p + 1) j)) =
      -(∑ j, c j * conj (character (2 * m) (p + 1) j)) := by
    calc
      _ = ∑ j, c (halfTurn hm j) * conj (character (2 * m) (p + 1) (halfTurn hm j)) :=
        hs.symm
      _ = _ := by simp [hc, character_halfTurn hm ho, Finset.sum_neg_distrib]
  have hz : (∑ j, c j * conj (character (2 * m) (p + 1) j)) = 0 := by
    linear_combination (1 / 2 : ℂ) * hs'
  rw [centerCoefficient_eq, hz, zero_div]

/-- The actual negative real sum of squared pair quotients, counting each pair once. -/
def pairPotential {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) : ℝ :=
  -((∑ h ∈ (Finset.range n).erase 0, ∑ j ∈ Finset.range n,
    LocalDFT.pairRatio n (periodize hn c) j h *
      LocalDFT.pairRatio n (periodize hn c) j h) / 2 : ℂ).re

theorem pairPotential_spectrum {n : ℕ} (hn : 2 ≤ n) (c : Fin n → ℂ)
    (hc : centerCoefficient (by omega) c 0 = 0) :
    pairPotential (by omega) c = (n : ℝ) / 2 * ∑ p ∈ Finset.range n,
      ((p : ℝ) - 1) * ((n : ℝ) - ((p : ℝ) + 1)) *
        (centerCoefficient (by omega) c p *
          centerCoefficient (by omega) c (LocalFourier.partner n p)).re := by
  have hQ : LocalSpectrum.fullQ n (centerCoefficient (by omega) c) =
      LocalDFT.positiveQuadratic n (periodize (by omega) c) := by
    calc
      _ = LocalHessian.geometricQ n (centerCoefficient (by omega) c) :=
        LocalHessian.fullQ_eq_geometric ClosedFourier.geometricSine hn
          (ClosedFourier.orthogonality n (by omega)) _ hc
      _ = _ := (LocalDFT.quadratic_eq_fourier ClosedFourier.dftInversion hn _
        (periodize_periodic (by omega) c)).symm
  have hB : LocalSpectrum.fullB n (centerCoefficient (by omega) c) =
      LocalDFT.energyB n (periodize (by omega) c) := by
    calc
      _ = LocalHessian.geometricB n (centerCoefficient (by omega) c) :=
        LocalHessian.fullB_eq_geometric ClosedFourier.geometricSine hn
          (ClosedFourier.orthogonality n (by omega)) _ hc
      _ = _ := (LocalDFT.energyB_eq_fourier ClosedFourier.dftInversion hn _
        (periodize_periodic (by omega) c)).symm
  unfold LocalSpectrum.fullQ at hQ
  rw [hB] at hQ
  unfold LocalDFT.positiveQuadratic at hQ
  unfold pairPotential
  linarith

theorem partner_eq_neg {n : ℕ} [NeZero n] (p : Fin n) :
    LocalFourier.partner n p = (-p).val := by
  by_cases hp : p = 0
  · subst p
    simp [LocalFourier.partner]
  · rw [Fin.val_neg, if_neg hp, LocalFourier.partner, if_neg]
    exact Fin.val_ne_zero_iff.mpr hp

theorem partner_mode {n : ℕ} [NeZero n] (p : Fin n) (hp : p ≠ 0) :
    LocalTrigonometry.mode (n : ℝ) ((-p).val + 1 : ℝ) =
      Real.sin (((p : ℝ) - 1) * Real.pi / n) / Real.sin (Real.pi / n) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  unfold LocalTrigonometry.mode
  rw [Fin.val_neg, if_neg hp, Nat.cast_sub p.isLt.le]
  rw [show ((n : ℝ) - p + 1) * Real.pi / n =
    Real.pi - ((p : ℝ) - 1) * Real.pi / n by field_simp; ring, Real.sin_pi_sub]

theorem odd_inactive_boundary {m : ℕ} (p : Fin (2 * m)) (hp : Odd p.val)
    (ha : ¬SchurWeights.Active (2 * m) p) : p.val = 1 ∨ p.val + 1 = 2 * m := by
  have hmod := Nat.odd_iff.mp hp
  have hi := p.isLt
  have hb : ¬(3 ≤ p.val ∧ p.val + 3 ≤ 2 * m) := fun h => ha ⟨hp, h⟩
  omega

def spectralGap {n : ℕ} (x : Fin n → ℂ) : ℝ :=
  (1 / 2 : ℝ) * ∑ p : Fin n, blockGap n p (x p) (x (-p))

theorem spectralGap_nonneg {n : ℕ} (x : Fin n → ℂ) : 0 ≤ spectralGap x := by
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun p _ => blockGap_nonneg _ _ _ _)

/-- All even physical-frequency blocks, including a possible self-paired block,
are identified with the actual pair-quotient potential. -/
theorem pairPotential_eq_blocks {m : ℕ} (hm : 1 ≤ m) (c : Fin (2 * m) → ℂ)
    (hc : HalfPeriodic (by omega) c) :
    pairPotential (by omega) c = (1 / 2 : ℝ) * ∑ p : Fin (2 * m),
      blockValue (2 * m) p (amplitude (by omega) c p) (amplitude (by omega) c (-p)) := by
  let : NeZero (2 * m) := ⟨by omega⟩
  have hzero := centerCoefficient_even_zero (by omega) c hc 0 (by decide)
  rw [pairPotential_spectrum (by omega) c hzero]
  rw [← Fin.sum_univ_eq_sum_range (fun p =>
    ((p : ℝ) - 1) * (((2 * m : ℕ) : ℝ) - ((p : ℝ) + 1)) *
      (centerCoefficient (by omega) c p * centerCoefficient (by omega) c
        (LocalFourier.partner (2 * m) p)).re) (2 * m)]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : SchurWeights.Active (2 * m) p
  · have hp0 : p ≠ 0 := by
      intro h
      have := hp.2.1
      simp [h] at this
    rw [amplitude_eq (by omega), amplitude_eq (by omega),
      LocalSpectrum.fullAmplitude, LocalSpectrum.fullAmplitude, partner_mode p hp0]
    rw [LocalTrigonometry.mode, blockValue_physical hp, partner_eq_neg]
    ring
  · rw [blockValue, SchurWeights.weight_eq_zero hp]
    simp only [mul_zero, zero_mul]
    rcases (Nat.even_or_odd p.val) with he | ho
    · rw [centerCoefficient_even_zero (by omega) c hc p he]
      simp
    · rcases odd_inactive_boundary p ho hp with h1 | hlast
      · simp [h1]
      · have hreal : (p : ℝ) + 1 = (2 * m : ℕ) := by exact_mod_cast hlast
        rw [← hreal, sub_self, mul_zero, zero_mul, mul_zero]

theorem constraint_eq_edgeImaginary {n : ℕ} (hn : 2 ≤ n) (c : Fin n → ℂ) (j : Fin n) :
    constraint (by omega) c j = -(n : ℝ) * (edgeRatio (by omega) c j).im := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : Real.sin (Real.pi / n) ≠ 0 := by
    apply (Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_).ne'
    apply (div_lt_iff₀ hnR).2
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.pi_pos]
  have hz : frame n j * conj (frame n j) = 1 := by
    rw [Complex.mul_conj, frame_normSq]
    rfl
  have hf : frame n j ≠ 0 := by
    intro h
    rw [h, zero_mul] at hz
    exact zero_ne_one hz
  rw [edgeRatio_eq_difference, reference_difference, constraint]
  have hs0 : (Real.sin (Real.pi / n) : ℂ) ≠ 0 := by exact_mod_cast hs
  have hratio : difference (by omega) c j /
      ((2 * Real.sin (Real.pi / n) : ℝ) * Complex.I * frame n j) =
      (-Complex.I * (conj (frame n j) * difference (by omega) c j)) /
        ((2 * Real.sin (Real.pi / n) : ℝ) : ℂ) := by
    have htwo : ((2 * Real.sin (Real.pi / n) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hs
    apply (div_eq_iff (mul_ne_zero (mul_ne_zero htwo Complex.I_ne_zero) hf)).2
    generalize Real.sin (Real.pi / n) = sa at *
    push_cast
    field_simp
    calc
      _ = -(frame n j * conj (frame n j)) * difference (by omega) c j * Complex.I ^ 2 := by
        rw [hz, Complex.I_sq]
        ring
      _ = _ := by ring
  rw [hratio]
  simp only [Complex.div_ofReal_im, Complex.mul_im, Complex.neg_im,
    Complex.I_re, Complex.I_im, zero_mul, neg_mul, one_mul, zero_add]
  ring

theorem constraint_amplitude {n : ℕ} [NeZero n] (hn : 2 ≤ n) (c : Fin n → ℂ)
    (p : Fin n) (hp : p ≠ 0) :
    midpointCoefficient (constraint (by omega) c) p =
      blockConstraint n (amplitude (by omega) c p) (amplitude (by omega) c (-p)) := by
  rw [← midpointTransform_real]
  simp_rw [constraint_eq_edgeImaginary hn]
  exact midpointTransform_imaginary _ p hp

theorem midpointTransform_frame {n : ℕ} (hn : 2 ≤ n) (p : Fin n) :
    midpointTransform (frame n) p = if p.val = 1 then 1 else 0 := by
  let oneIndex : Fin n := ⟨1, by omega⟩
  have he : midpointSynthesis (fun r : Fin n => if r = oneIndex then (1 : ℂ) else 0) =
      frame n := by
    funext j
    simp [midpointSynthesis, oneIndex, midpointCharacter, frame]
  have h := midpointTransform_synthesis (by omega)
    (fun r : Fin n => if r = oneIndex then (1 : ℂ) else 0) p
  rw [he] at h
  simpa only [Fin.ext_iff, oneIndex] using h

theorem midpointTransform_im_zero {n : ℕ} [NeZero n] (f : Fin n → ℂ)
    (p : Fin n) (hp : p ≠ 0) (hf : midpointTransform f p = 0)
    (hfneg : midpointTransform f (-p) = 0) :
    midpointTransform (fun j => ((f j).im : ℂ)) p = 0 := by
  have h := midpointTransform_imaginary f p hp
  rw [hf, hfneg] at h
  have he : (fun j => ((-(n : ℝ) * (f j).im : ℝ) : ℂ)) =
      (fun j => (-(n : ℂ)) * ((f j).im : ℂ)) := by
    funext j
    push_cast
    rfl
  rw [he, midpointTransform_mul] at h
  simp only [blockConstraint, map_zero, add_zero, mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (neg_ne_zero.mpr (by exact_mod_cast NeZero.ne n))

theorem amplitude_canonicalLift {n : ℕ} [NeZero n] (hn : 3 ≤ n) (q : Fin n → ℝ)
    (p : Fin n) (hp : SchurWeights.Active n p) :
    amplitude (by omega) (canonicalLift q) p = blockLift n (midpointCoefficient q p) := by
  have hp0 : p ≠ 0 := by intro h; have := hp.2.1; simp [h] at this
  have hp1 : p.val ≠ 1 := by have := hp.2.1; omega
  have hn1 : (-p).val ≠ 1 := by
    rw [Fin.val_neg, if_neg hp0]
    have := hp.2.2
    omega
  have hz : midpointTransform (fun j => ((firstCoefficient q * frame n j).im : ℂ)) p = 0 := by
    apply midpointTransform_im_zero _ p hp0
    · rw [midpointTransform_mul, midpointTransform_frame (by omega), if_neg hp1, mul_zero]
    · rw [midpointTransform_mul, midpointTransform_frame (by omega), if_neg hn1, mul_zero]
  have he : edgeRatio (by omega) (canonicalLift q) =
      (fun j => ((2 / n : ℝ) : ℂ) * ((firstCoefficient q * frame n j).im : ℂ)) -
      (fun j => (Complex.I / n) * (q j : ℂ)) := by
    funext j
    rw [edgeRatio_eq_difference, canonicalLift_ratio hn]
    push_cast
    rfl
  unfold amplitude
  rw [he, midpointTransform_sub, midpointTransform_mul, midpointTransform_mul, hz,
    mul_zero, zero_sub, midpointTransform_real]
  unfold blockLift
  ring

/-- The complete square identity for the actual geometric pair potential. -/
theorem geometric_completedSquare {m : ℕ} (hm : 2 ≤ m) (c : Fin (2 * m) → ℂ)
    (hc : HalfPeriodic (by omega) c) :
    pairPotential (by omega) c =
      normalizedBoxEnergy (operator (2 * m)) (constraint (by omega) c) -
        spectralGap (amplitude (by omega) c) := by
  let : NeZero (2 * m) := ⟨by omega⟩
  rw [pairPotential_eq_blocks (by omega) c hc, spectral_energy_midpoint (by omega)]
  simp_rw [block_completedSquare]
  rw [Finset.sum_sub_distrib, mul_sub]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : SchurWeights.Active (2 * m) p
  · have hp0 : p ≠ 0 := by intro h; have := hp.2.1; simp [h] at this
    rw [constraint_amplitude (by omega) c p hp0]
  · simp [SchurWeights.weight_eq_zero hp]

theorem canonicalLift_spectralGap_zero {m : ℕ} (hm : 2 ≤ m) (q : Fin (2 * m) → ℝ) :
    spectralGap (amplitude (by omega) (canonicalLift q)) = 0 := by
  let : NeZero (2 * m) := ⟨by omega⟩
  unfold spectralGap
  suffices (∑ p : Fin (2 * m), blockGap (2 * m) p
      (amplitude (by omega) (canonicalLift q) p)
      (amplitude (by omega) (canonicalLift q) (-p))) = 0 by rw [this, mul_zero]
  apply Finset.sum_eq_zero
  intro p _
  by_cases hp : SchurWeights.Active (2 * m) p
  · have hp0 : p ≠ 0 := by intro h; have := hp.2.1; simp [h] at this
    have hpneg : SchurWeights.Active (2 * m) (-p).val := by
      rw [Fin.val_neg, if_neg hp0]
      exact (SchurWeights.active_reflect (even_two_mul m) p.isLt.le).mpr hp
    apply (blockGap_eq_zero_iff hp _ _).mpr
    rw [amplitude_canonicalLift (by omega) q p hp,
      amplitude_canonicalLift (by omega) q (-p) hpneg, midpointCoefficient_neg q p hp0]
    simp [blockLift, Complex.conj_ofNat]
  · simp [blockGap, SchurWeights.weight_eq_zero hp]

/-- Exact equality P(c0(q)) = Vn(q), with no assumed Schur identity. -/
theorem pairPotential_canonicalLift {m : ℕ} (hm : 2 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : FiniteBox.Antiperiodic (by omega) q) :
    pairPotential (by omega) (canonicalLift q) =
      normalizedBoxEnergy (operator (2 * m)) q := by
  rw [geometric_completedSquare hm (canonicalLift q) (canonicalLift_halfTurn hm q hq),
    constraint_canonicalLift (by omega), canonicalLift_spectralGap_zero hm, sub_zero]

theorem edgeRatio_add {n : ℕ} (hn : 0 < n) (c d : Fin n → ℂ) :
    edgeRatio hn (c + d) = edgeRatio hn c + edgeRatio hn d := by
  funext j
  simp only [edgeRatio, LocalDFT.pairRatio, periodize, Pi.add_apply]
  ring

theorem edgeRatio_sub {n : ℕ} (hn : 0 < n) (c d : Fin n → ℂ) :
    edgeRatio hn (c - d) = edgeRatio hn c - edgeRatio hn d := by
  funext j
  simp only [edgeRatio, LocalDFT.pairRatio, periodize, Pi.sub_apply]
  ring

theorem amplitude_add {n : ℕ} (hn : 0 < n) (c d : Fin n → ℂ) (p : Fin n) :
    amplitude hn (c + d) p = amplitude hn c p + amplitude hn d p := by
  unfold amplitude
  rw [edgeRatio_add, midpointTransform_add]

theorem constraint_add {n : ℕ} (hn : 2 ≤ n) (c d : Fin n → ℂ) :
    constraint (by omega) (c + d) = constraint (by omega) c + constraint (by omega) d := by
  funext j
  simp only [constraint_eq_edgeImaginary hn, edgeRatio_add, Pi.add_apply, Complex.add_im]
  ring

theorem constraint_sub {n : ℕ} (hn : 2 ≤ n) (c d : Fin n → ℂ) :
    constraint (by omega) (c - d) = constraint (by omega) c - constraint (by omega) d := by
  funext j
  simp only [constraint_eq_edgeImaginary hn, edgeRatio_sub, Pi.sub_apply, Complex.sub_im]
  ring

/-- The full geometric orthogonal decomposition in manuscript (4.5). -/
theorem geometric_orthogonal_decomposition {m : ℕ} (hm : 2 ≤ m)
    (q : Fin (2 * m) → ℝ) (hq : FiniteBox.Antiperiodic (by omega) q)
    (v : Fin (2 * m) → ℂ) (hv : HalfPeriodic (by omega) v)
    (hvq : constraint (by omega) v = 0) :
    pairPotential (by omega) (canonicalLift q + v) =
      normalizedBoxEnergy (operator (2 * m)) q + pairPotential (by omega) v := by
  let : NeZero (2 * m) := ⟨by omega⟩
  have hsum : HalfPeriodic (by omega) (canonicalLift q + v) := by
    intro j
    simp only [Pi.add_apply, canonicalLift_halfTurn hm q hq, hv j]
  rw [pairPotential_eq_blocks (by omega) _ hsum,
    pairPotential_eq_blocks (by omega) v hv, spectral_energy_midpoint (by omega)]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : SchurWeights.Active (2 * m) p
  · have hp0 : p ≠ 0 := by intro h; have := hp.2.1; simp [h] at this
    have hpneg : SchurWeights.Active (2 * m) (-p).val := by
      rw [Fin.val_neg, if_neg hp0]
      exact (SchurWeights.active_reflect (even_two_mul m) p.isLt.le).mpr hp
    have hconj : amplitude (by omega) (canonicalLift q) (-p) =
        conj (blockLift (2 * m) (midpointCoefficient q p)) := by
      rw [amplitude_canonicalLift (by omega) q (-p) hpneg, midpointCoefficient_neg q p hp0]
      simp [blockLift, Complex.conj_ofNat]
    have hvblock : blockConstraint (2 * m) (amplitude (by omega) v p)
        (amplitude (by omega) v (-p)) = 0 := by
      rw [← constraint_amplitude (by omega) v p hp0, hvq]
      simp [midpointCoefficient]
    rw [amplitude_add, amplitude_add, amplitude_canonicalLift (by omega) q p hp, hconj]
    exact block_orthogonal_decomposition (by omega) p _ _ _ hvblock
  · simp [blockValue, SchurWeights.weight_eq_zero hp]

def pairEnergy {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) : ℝ :=
  LocalDFT.energyA n (periodize hn c)

theorem pairEnergy_nonneg {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) : 0 ≤ pairEnergy hn c := by
  unfold pairEnergy LocalDFT.energyA
  exact div_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Complex.normSq_nonneg _) (by norm_num)

theorem periodize_sum {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) :
    (∑ j ∈ Finset.range n, periodize hn c j) = ∑ j : Fin n, c j := by
  rw [← Fin.sum_univ_eq_sum_range (periodize hn c) n]
  simp only [periodize_fin]

theorem constraint_kernel_energyB_zero {n : ℕ} (hn : 2 ≤ n) (c : Fin n → ℂ)
    (hc : constraint (by omega) c = 0) :
    LocalDFT.energyB n (periodize (by omega) c) = 0 := by
  have hn0 : (-(n : ℝ)) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast (show n ≠ 0 by omega))
  have hi (j : Fin n) : (edgeRatio (by omega) c j).im = 0 := by
    have h := congrFun hc j
    rw [constraint_eq_edgeImaginary hn] at h
    exact (mul_eq_zero.mp h).resolve_left hn0
  unfold LocalDFT.energyB
  apply Finset.sum_eq_zero
  intro j hj
  change (edgeRatio (by omega) c ⟨j, Finset.mem_range.mp hj⟩).im ^ 2 = 0
  rw [hi]
  norm_num

theorem pairPotential_eq_quadratic {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) :
    pairPotential hn c = ((n : ℝ) - 1) / 2 * LocalDFT.energyB n (periodize hn c) -
      LocalDFT.positiveQuadratic n (periodize hn c) := by
  unfold pairPotential LocalDFT.positiveQuadratic
  ring

/-- The uniform negative remainder in (4.5), inherited from the already proved
geometric coercivity theorem, with all of its normalization premises discharged. -/
theorem kernel_coercivity {m : ℕ} (hm : 2 ≤ m) (v : Fin (2 * m) → ℂ)
    (hv : HalfPeriodic (by omega) v) (hmean : ∑ j, v j = 0)
    (hq : constraint (by omega) v = 0) :
    pairEnergy (by omega) v / 64 ≤ -pairPotential (by omega) v := by
  have hn0 : ((2 * m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show 2 * m ≠ 0 by omega)
  have hc0 := centerCoefficient_even_zero (by omega) v hv 0 (by decide)
  have hsim : (∑ j ∈ Finset.range (2 * m), periodize (by omega) v j *
      conj (LocalPhase.regularRoot (2 * m) ^ j)) = 0 := by
    unfold centerCoefficient LocalDFT.coefficient at hc0
    simp only [Nat.zero_add, Nat.mul_one] at hc0
    simpa only [zero_mul] using (div_eq_iff hn0).mp hc0
  have hm' : (∑ j ∈ Finset.range (2 * m), periodize (by omega) v j) = 0 := by
    rw [periodize_sum, hmean]
  have he := LocalDFT.normalized_coercivity ClosedFourier.dftInversion
    ClosedFourier.geometricSine (by omega) (ClosedFourier.orthogonality (2 * m) (by omega))
    (periodize (by omega) v) (periodize_periodic _ _) hm' hsim
  have hB := constraint_kernel_energyB_zero (by omega) v hq
  rw [hB] at he
  rw [pairPotential_eq_quadratic, hB]
  simpa only [mul_zero, add_zero, zero_sub, neg_neg, pairEnergy] using he

theorem pairEnergy_zero_forces_zero {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ)
    (hmean : ∑ j, c j = 0) (hc : pairEnergy hn c = 0) : c = 0 := by
  have hm : (∑ j ∈ Finset.range n, periodize hn c j) = 0 := by rw [periodize_sum, hmean]
  have hz := LocalDFT.zero_energy_forces_zero ClosedFourier.dftInversion hn
    (ClosedFourier.orthogonality n hn) (periodize hn c) (periodize_periodic hn c) hm hc
  funext j
  simpa only [periodize_fin, Pi.zero_apply] using hz j

/-- Among mean-zero half-periodic centers with the prescribed real constraint,
the explicit lift is the unique maximizer of the actual geometric potential. -/
theorem canonicalLift_unique_maximizer {m : ℕ} (hm : 2 ≤ m)
    (q : Fin (2 * m) → ℝ) (hq : FiniteBox.Antiperiodic (by omega) q)
    (c : Fin (2 * m) → ℂ) (hc : HalfPeriodic (by omega) c)
    (hmean : ∑ j, c j = 0) (hconstraint : constraint (by omega) c = q) :
    pairPotential (by omega) c ≤ normalizedBoxEnergy (operator (2 * m)) q ∧
      (pairPotential (by omega) c = normalizedBoxEnergy (operator (2 * m)) q ↔
        c = canonicalLift q) := by
  have hupper := geometric_completedSquare hm c hc
  rw [hconstraint] at hupper
  refine ⟨?_, ?_⟩
  · rw [hupper]
    exact sub_le_self _ (spectralGap_nonneg _)
  · constructor
    · intro he
      let v := c - canonicalLift q
      have hv : HalfPeriodic (by omega) v := by
        intro j
        simp only [v, Pi.sub_apply, hc j, canonicalLift_halfTurn hm q hq]
      have hvm : (∑ j, v j) = 0 := by
        simp only [v, Pi.sub_apply, Finset.sum_sub_distrib, hmean,
          canonicalLift_mean_zero (n := 2 * m) (by omega) q, sub_self]
      have hvq : constraint (by omega) v = 0 := by
        rw [show v = c - canonicalLift q from rfl, constraint_sub (by omega),
          hconstraint, constraint_canonicalLift (by omega), sub_self]
      have hcv : canonicalLift q + v = c := by
        dsimp [v]
        abel
      have hdecomp := geometric_orthogonal_decomposition hm q hq v hv hvq
      rw [hcv, he] at hdecomp
      have hvP : pairPotential (by omega) v = 0 := by linarith
      have hco := kernel_coercivity hm v hv hvm hvq
      rw [hvP, neg_zero] at hco
      have hvA : pairEnergy (by omega) v = 0 := by
        have hnonneg := pairEnergy_nonneg (by omega) v
        linarith
      have hv0 := pairEnergy_zero_forces_zero (by omega) v hvm hvA
      exact sub_eq_zero.mp hv0
    · rintro rfl
      exact pairPotential_canonicalLift hm q hq

end Erdos1045.EventualExact.SchurSpectrum
