import EventualExact.SchurSpectrum

/-! The normal and tangential edge coordinates of Section 4 of the structural note.
The midpoint transform is retained; in particular its conjugacy has a minus sign.
No parity condition is imposed on the number of vertices. -/

noncomputable section

open scoped BigOperators

namespace StructuralNote.EdgeCoordinates

open Erdos1045 Erdos1045.EventualExact
open Complex FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum

local notation "conj" => (starRingEnd ℂ)

def normal {n : ℕ} (hn : 0 < n) (u : Fin n → ℂ) (j : Fin n) : ℝ :=
  -(n : ℝ) * (edgeRatio hn u j).im

def tangent {n : ℕ} (hn : 0 < n) (u : Fin n → ℂ) (j : Fin n) : ℝ :=
  (n : ℝ) * (edgeRatio hn u j).re

/-- The actual increment in formula (4.2), for arbitrary real edge data. -/
def edgeIncrement {n : ℕ} (q p : Fin n → ℝ) (j : Fin n) : ℂ :=
  (2 * Real.sin (Real.pi / n) / n : ℝ) * frame n j *
    ((q j : ℂ) + I * (p j : ℂ))

theorem scaled_edgeRatio {n : ℕ} (hn : 0 < n) (u : Fin n → ℂ) (j : Fin n) :
    (n : ℂ) * edgeRatio hn u j =
      (tangent hn u j : ℂ) - I * (normal hn u j : ℂ) := by
  apply Complex.ext <;> simp [normal, tangent]

theorem reference_difference_ne_zero {n : ℕ} (hn : 2 ≤ n) (j : Fin n) :
    difference (by omega) (fun j => character n 1 j) j ≠ 0 := by
  rw [reference_difference]
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : Real.sin (Real.pi / n) ≠ 0 := by
    apply (Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_).ne'
    apply (div_lt_iff₀ hnr).2
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.pi_pos]
  have hf : frame n j ≠ 0 := by
    intro hz
    have h := frame_normSq n j
    simp [hz] at h
  exact mul_ne_zero (mul_ne_zero (by exact_mod_cast mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hs)
    I_ne_zero) hf

theorem actual_increment {n : ℕ} (hn : 2 ≤ n) (u : Fin n → ℂ) :
    difference (by omega) u = edgeIncrement (normal (by omega) u) (tangent (by omega) u) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  funext j
  have hd := reference_difference_ne_zero hn j
  have he : difference (by omega) u j = edgeRatio (by omega) u j *
      difference (by omega) (fun j => character n 1 j) j := by
    rw [edgeRatio_eq_difference, div_mul_cancel₀ _ hd]
  rw [he, reference_difference, edgeIncrement]
  have hr := scaled_edgeRatio (by omega) u j
  have hz : edgeRatio (by omega) u j =
      ((tangent (by omega) u j : ℂ) - I * (normal (by omega) u j : ℂ)) / n := by
    apply (eq_div_iff hn0).2
    simpa [mul_comm] using hr
  rw [hz]
  generalize Real.sin (Real.pi / n) = sa
  push_cast
  field_simp
  ring_nf
  simp

theorem midpoint_tangent {n : ℕ} [NeZero n] (u : Fin n → ℂ)
    (p : Fin n) (hp : p ≠ 0) :
    midpointCoefficient (tangent (NeZero.pos n) u) p =
      (n : ℂ) / 2 * (amplitude (NeZero.pos n) u p -
        conj (amplitude (NeZero.pos n) u (-p))) := by
  have he : (fun j => (tangent (NeZero.pos n) u j : ℂ)) =
      (fun j => (n : ℂ) / 2 * (edgeRatio (NeZero.pos n) u j +
        conj (edgeRatio (NeZero.pos n) u j))) := by
    funext j
    apply Complex.ext <;> simp [tangent]
    ring
  rw [← midpointTransform_real, he, midpointTransform_mul]
  change _ * midpointTransform (edgeRatio (NeZero.pos n) u +
    fun j => conj (edgeRatio (NeZero.pos n) u j)) p = _
  rw [midpointTransform_add, midpointTransform_conj _ p hp]
  rfl

theorem midpoint_normal {n : ℕ} [NeZero n] (u : Fin n → ℂ)
    (p : Fin n) (hp : p ≠ 0) :
    midpointCoefficient (normal (NeZero.pos n) u) p =
      I * n / 2 * (amplitude (NeZero.pos n) u p +
        conj (amplitude (NeZero.pos n) u (-p))) :=
  midpointTransform_imaginary _ p hp

/-- Formula (4.8), including a self-paired midpoint frequency. -/
theorem midpoint_norm_difference {n : ℕ} [NeZero n] (u : Fin n → ℂ)
    (p : Fin n) (hp : p ≠ 0) :
    normSq (midpointCoefficient (normal (NeZero.pos n) u) p) -
        normSq (midpointCoefficient (tangent (NeZero.pos n) u) p) =
      (n : ℝ) ^ 2 * (amplitude (NeZero.pos n) u p *
        amplitude (NeZero.pos n) u (-p)).re := by
  rw [midpoint_normal u p hp, midpoint_tangent u p hp]
  simp [Complex.normSq_apply]
  ring

/-- Formula (4.6) with the paper's normalized real square norm. -/
theorem normal_mean_square {n : ℕ} (hn : 0 < n) (u : Fin n → ℂ) :
    (∑ j, normal hn u j ^ 2) / (n : ℝ) =
      (n : ℝ) * LocalDFT.energyB n (periodize hn u) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold LocalDFT.energyB
  rw [← Fin.sum_univ_eq_sum_range
    (fun j => (LocalDFT.pairRatio n (periodize hn u) j 1).im ^ 2) n]
  simp only [normal, edgeRatio, mul_pow, neg_sq, ← Finset.mul_sum]
  field_simp

theorem edgeIncrement_sum {n : ℕ} (hn : 0 < n) (q p : Fin n → ℝ) :
    (∑ j, edgeIncrement q p j) =
      (2 * Real.sin (Real.pi / n) : ℝ) *
        (conj (firstCoefficient q) + I * conj (firstCoefficient p)) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [edgeIncrement, mul_add, Finset.sum_add_distrib]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  have hs (j : Fin n) : frame n j * (I * (p j : ℂ)) =
      I * (frame n j * (p j : ℂ)) := by ring
  simp_rw [hs, ← Finset.mul_sum]
  rw [sum_frame_mul hn q, sum_frame_mul hn p]
  push_cast
  field_simp

/-- Closing the polygon imposes one complex first-harmonic relation, not
vanishing of the first harmonic of the normal variable. -/
theorem closed_iff_first_harmonic {n : ℕ} (hn : 2 ≤ n) (q p : Fin n → ℝ) :
    (∑ j, edgeIncrement q p j) = 0 ↔
      firstCoefficient p = -I * firstCoefficient q := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : Real.sin (Real.pi / n) ≠ 0 := by
    apply (Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_).ne'
    apply (div_lt_iff₀ hnr).2
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.pi_pos]
  have hsC : ((2 * Real.sin (Real.pi / n) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hs
  rw [edgeIncrement_sum (by omega), mul_eq_zero, or_iff_right hsC]
  constructor
  · intro he
    apply Complex.ext
    · have hr := congrArg Complex.im he
      simp at hr ⊢
      linarith
    · have hr := congrArg Complex.re he
      simp at hr ⊢
      linarith
  · intro he
    rw [he]
    simp [← mul_assoc]

theorem difference_sum_zero {n : ℕ} (hn : 0 < n) (u : Fin n → ℂ) :
    (∑ j, difference hn u j) = 0 := by
  let : NeZero n := ⟨hn.ne'⟩
  have h := coefficient_difference hn u (0 : Fin n)
  rw [coefficient_zero] at h
  simp only [differenceSymbol, Fin.val_zero, pow_zero, sub_self, mul_zero] at h
  exact (div_eq_zero_iff).mp h |>.resolve_right (by exact_mod_cast hn.ne')

theorem actual_first_harmonic {n : ℕ} (hn : 2 ≤ n) (u : Fin n → ℂ) :
    firstCoefficient (tangent (by omega) u) =
      -I * firstCoefficient (normal (by omega) u) := by
  apply (closed_iff_first_harmonic hn _ _).mp
  rw [← actual_increment hn]
  exact difference_sum_zero (by omega) u

/-- The mean-zero primitive of arbitrary closed normal/tangential edge data. -/
def lift {n : ℕ} (q p : Fin n → ℝ) : Fin n → ℂ :=
  integral (edgeIncrement q p)

theorem lift_mean_zero {n : ℕ} (hn : 0 < n) (q p : Fin n → ℝ) :
    (∑ j, lift q p j) = 0 := integral_mean_zero hn _

theorem lift_difference {n : ℕ} (hn : 2 ≤ n) (q p : Fin n → ℝ)
    (hclose : firstCoefficient p = -I * firstCoefficient q) :
    difference (by omega) (lift q p) = edgeIncrement q p :=
  difference_integral (by omega) _ ((closed_iff_first_harmonic hn q p).mpr hclose)

theorem lift_unique {n : ℕ} (hn : 0 < n) (q p : Fin n → ℝ) (u : Fin n → ℂ)
    (hmean : ∑ j, u j = 0) (hd : difference hn u = edgeIncrement q p) :
    u = lift q p := integral_unique hn _ u hmean hd

theorem lift_edgeRatio {n : ℕ} (hn : 2 ≤ n) (q p : Fin n → ℝ)
    (hclose : firstCoefficient p = -I * firstCoefficient q) (j : Fin n) :
    edgeRatio (by omega) (lift q p) j = ((p j : ℂ) - I * (q j : ℂ)) / n := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [edgeRatio_eq_difference, lift_difference hn q p hclose]
  apply (div_eq_iff (reference_difference_ne_zero hn j)).2
  rw [edgeIncrement, reference_difference]
  generalize Real.sin (Real.pi / n) = sa
  push_cast
  field_simp
  ring_nf
  simp

theorem lift_coordinates {n : ℕ} (hn : 2 ≤ n) (q p : Fin n → ℝ)
    (hclose : firstCoefficient p = -I * firstCoefficient q) :
    normal (by omega) (lift q p) = q ∧ tangent (by omega) (lift q p) = p := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  constructor <;> funext j
  · rw [normal, lift_edgeRatio hn q p hclose]
    simp
    field_simp
  · rw [tangent, lift_edgeRatio hn q p hclose]
    simp
    field_simp

/-- The real first harmonic forced upon the tangential component by closure. -/
def J {n : ℕ} (q : Fin n → ℝ) (j : Fin n) : ℝ :=
  2 * (firstCoefficient q * frame n j).im

def freeTangent {n : ℕ} (hn : 0 < n) (u : Fin n → ℂ) : Fin n → ℝ :=
  tangent hn u - J (normal hn u)

theorem midpoint_J {n : ℕ} [NeZero n] (hn : 2 ≤ n) (q : Fin n → ℝ)
    (p : Fin n) (hp : p ≠ 0) :
    midpointCoefficient (J q) p = -I *
      (firstCoefficient q * (if p.val = 1 then 1 else 0) +
        conj (firstCoefficient q * (if (-p).val = 1 then 1 else 0))) := by
  have he : (fun j => (J q j : ℂ)) = fun j => -I *
      (firstCoefficient q * frame n j - conj (firstCoefficient q * frame n j)) := by
    funext j
    apply Complex.ext <;> simp [J]
    ring
  rw [← midpointTransform_real, he, midpointTransform_mul]
  change -I * midpointTransform ((fun j => firstCoefficient q * frame n j) -
    fun j => conj (firstCoefficient q * frame n j)) p = _
  rw [midpointTransform_sub, midpointTransform_conj _ p hp,
    midpointTransform_mul, midpointTransform_mul,
    midpointTransform_frame hn, midpointTransform_frame hn]
  simp

theorem firstCoefficient_J {n : ℕ} (hn : 3 ≤ n) (q : Fin n → ℝ) :
    firstCoefficient (J q) = -I * firstCoefficient q := by
  let : NeZero n := ⟨by omega⟩
  let p : Fin n := ⟨1, by omega⟩
  have hp0 : p ≠ 0 := by simp [p]
  have hpneg : (-p).val ≠ 1 := by
    rw [Fin.val_neg, if_neg hp0]
    simp only [p]
    omega
  rw [firstCoefficient_eq_midpoint (by omega)]
  change midpointCoefficient (J q) p = _
  rw [midpoint_J (by omega) q p hp0, if_neg hpneg]
  simp [p]

theorem freeTangent_first_zero {n : ℕ} (hn : 3 ≤ n) (u : Fin n → ℂ) :
    firstCoefficient (freeTangent (by omega) u) = 0 := by
  have hs (p q : Fin n → ℝ) : firstCoefficient (p - q) =
      firstCoefficient p - firstCoefficient q := by
    simp [firstCoefficient, sub_mul, Finset.sum_sub_distrib, sub_div]
  rw [freeTangent, hs, firstCoefficient_J hn, actual_first_harmonic (by omega), sub_self]

theorem normalized_edge_mean_zero {n : ℕ} (hn : 2 ≤ n) (u : Fin n → ℂ)
    (hfirst : centerCoefficient (by omega) u 0 = 0) :
    (∑ j, normal (by omega) u j) = 0 ∧ (∑ j, tangent (by omega) u j) = 0 := by
  have hz : amplitude (by omega) u ⟨0, by omega⟩ = 0 := by
    rw [amplitude_eq hn]
    simp [LocalSpectrum.fullAmplitude, hfirst]
  have hs : (∑ j, edgeRatio (by omega) u j) = 0 := by
    have he : (∑ j, edgeRatio (by omega) u j) / (n : ℂ) = 0 := by
      simpa [amplitude, midpointTransform, midpointCharacter, character, LocalPhase.phase] using hz
    exact (div_eq_zero_iff).mp he |>.resolve_right (by exact_mod_cast (show n ≠ 0 by omega))
  have hr : (∑ j, (edgeRatio (by omega) u j).re) = 0 := by
    simpa using congrArg Complex.re hs
  have hi : (∑ j, (edgeRatio (by omega) u j).im) = 0 := by
    simpa using congrArg Complex.im hs
  constructor
  · simp [normal, ← Finset.mul_sum, hi]
  · simp [tangent, ← Finset.mul_sum, hr]

theorem J_mean_zero {n : ℕ} (hn : 2 ≤ n) (q : Fin n → ℝ) : (∑ j, J q j) = 0 := by
  have hf : (∑ j : Fin n, frame n j) = 0 := by
    simp only [frame, ← Finset.mul_sum]
    rw [sum_character (by omega), if_neg, mul_zero]
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have h : (∑ j, firstCoefficient q * frame n j) = 0 := by
    rw [← Finset.mul_sum, hf, mul_zero]
  have hi : (∑ j, (firstCoefficient q * frame n j).im) = 0 := by
    simpa using congrArg Complex.im h
  simp only [J, ← Finset.mul_sum, hi, mul_zero]

theorem freeTangent_mean_zero {n : ℕ} (hn : 2 ≤ n) (u : Fin n → ℂ)
    (hfirst : centerCoefficient (by omega) u 0 = 0) :
    (∑ j, freeTangent (by omega) u j) = 0 := by
  simp only [freeTangent, Pi.sub_apply, Finset.sum_sub_distrib,
    (normalized_edge_mean_zero hn u hfirst).2, J_mean_zero hn, sub_self]

end StructuralNote.EdgeCoordinates
