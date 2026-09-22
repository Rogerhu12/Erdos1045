import StructuralNote.EdgeCoordinates
import StructuralNote.EdgeWeights

/-! The full-frequency normal/tangential identity. The potential is the actual
sum of squared pair quotients, and the only normalization removes vertex mode 1. -/

noncomputable section

open scoped BigOperators

namespace StructuralNote.EdgeNormalForm

open Erdos1045 Erdos1045.EventualExact
open Complex FourierMultiplier SchurLift SchurSpectrum EdgeCoordinates

def value {n : ℕ} (q : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ p : Fin n,
    EdgeWeights.weight n p * normSq (midpointCoefficient q p)

theorem value_nonneg {n : ℕ} (q : Fin n → ℝ) : 0 ≤ value q := by
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg fun p _ =>
    mul_nonneg (EdgeWeights.weight_nonneg _ _) (normSq_nonneg _)

theorem weighted_physical_block {n p : ℕ} (hp : EdgeWeights.Active n p) (b d : ℂ) :
    (n : ℝ) ^ 2 * EdgeWeights.weight n p *
      (((Real.sin (((p : ℝ) + 1) * Real.pi / n) / Real.sin (Real.pi / n) : ℝ) * b) *
        ((Real.sin (((p : ℝ) - 1) * Real.pi / n) / Real.sin (Real.pi / n) : ℝ) * d)).re =
      (n : ℝ) * ((p : ℝ) - 1) * ((n : ℝ) - p - 1) * (b * d).re := by
  rcases EdgeWeights.active_bounds hp with ⟨hn, hp0, hpn, _⟩
  have hsin (a : ℝ) (ha : 0 < a) (han : a < n) :
      Real.sin (a * Real.pi / n) ≠ 0 := by
    apply (Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_).ne'
    apply (div_lt_iff₀ hn).2
    nlinarith [Real.pi_pos]
  have hs0 := hsin 1 (by norm_num) (by linarith)
  simp only [one_mul] at hs0
  have hsminus := hsin ((p : ℝ) - 1) hp0 (by linarith)
  have hsplus := hsin ((p : ℝ) + 1) (by linarith) hpn
  simp only [EdgeWeights.weight, if_pos hp, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, sub_zero]
  generalize Real.sin (Real.pi / n) = sa at *
  generalize Real.sin (((p : ℝ) - 1) * Real.pi / n) = sm at *
  generalize Real.sin (((p : ℝ) + 1) * Real.pi / n) = sp at *
  field_simp

/-- Formula (4.10) converted to the actual edge amplitudes, on every frequency.
The half factor handles a possible self-paired frequency without duplication. -/
theorem potential_eq_edge_blocks {n : ℕ} (hn : 2 ≤ n) (u : Fin n → ℂ)
    (hfirst : centerCoefficient (by omega) u 0 = 0) :
    pairPotential (by omega) u = (1 / 2 : ℝ) * ∑ p : Fin n,
      (n : ℝ) ^ 2 * EdgeWeights.weight n p *
        (amplitude (by omega) u p * amplitude (by omega) u (-p)).re := by
  let : NeZero n := ⟨by omega⟩
  rw [pairPotential_spectrum hn u hfirst]
  rw [← Fin.sum_univ_eq_sum_range (fun p =>
    ((p : ℝ) - 1) * ((n : ℝ) - ((p : ℝ) + 1)) *
      (centerCoefficient (by omega) u p * centerCoefficient (by omega) u
        (LocalFourier.partner n p)).re) n]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : EdgeWeights.Active n p
  · have hp0 : p ≠ 0 := by
      intro h
      have := hp.1
      simp [h] at this
    rw [amplitude_eq hn, amplitude_eq hn,
      LocalSpectrum.fullAmplitude, LocalSpectrum.fullAmplitude, partner_mode p hp0]
    rw [LocalTrigonometry.mode, weighted_physical_block hp, partner_eq_neg]
    ring
  · rw [EdgeWeights.weight_eq_zero hp]
    simp only [mul_zero, zero_mul]
    have hb : p.val = 0 ∨ p.val = 1 ∨ p.val + 1 = n := by
      have := p.isLt
      unfold EdgeWeights.Active at hp
      omega
    rcases hb with hz | hone | hlast
    · rw [hz, hfirst]
      simp
    · simp [hone]
    · have hr : (p : ℝ) + 1 = n := by exact_mod_cast hlast
      rw [← hr, sub_self, mul_zero, zero_mul, mul_zero]

/-- The precise quadratic form in (4.5), before removing the costless first
harmonic of the tangential variable. It holds for odd and even n alike. -/
theorem potential_eq_normal_sub_tangent {n : ℕ} (hn : 2 ≤ n) (u : Fin n → ℂ)
    (hfirst : centerCoefficient (by omega) u 0 = 0) :
    pairPotential (by omega) u =
      value (normal (by omega) u) - value (tangent (by omega) u) := by
  let : NeZero n := ⟨by omega⟩
  rw [potential_eq_edge_blocks hn u hfirst]
  unfold value
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p = 0
  · subst p
    simp [EdgeWeights.weight_zero]
  · rw [← mul_sub, midpoint_norm_difference u p hp]
    ring

theorem value_sub_J {n : ℕ} (hn : 2 ≤ n) (p q : Fin n → ℝ) :
    value (p - J q) = value p := by
  let : NeZero n := ⟨by omega⟩
  unfold value
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : EdgeWeights.Active n k
  · have hk0 : k ≠ 0 := by intro h; have := hk.1; simp [h] at this
    have hk1 : k.val ≠ 1 := by have := hk.1; omega
    have hkn1 : (-k).val ≠ 1 := by
      rw [Fin.val_neg, if_neg hk0]
      have := hk.2
      omega
    have hJ : midpointCoefficient (J q) k = 0 := by
      rw [midpoint_J hn q k hk0, if_neg hk1, if_neg hkn1]
      simp
    have hs : midpointCoefficient (p - J q) k =
        midpointCoefficient p k - midpointCoefficient (J q) k := by
      simp [midpointCoefficient, sub_mul, Finset.sum_sub_distrib, sub_div]
    rw [hs, hJ, sub_zero]
  · simp [EdgeWeights.weight_eq_zero hk]

/-- Formula (4.5) with the precise free tangential variable in (4.3).
Its first midpoint harmonic vanishes by `freeTangent_first_zero`. -/
theorem normal_form {n : ℕ} (hn : 3 ≤ n) (u : Fin n → ℂ)
    (hfirst : centerCoefficient (by omega) u 0 = 0) :
    pairPotential (by omega) u =
      value (normal (by omega) u) - value (freeTangent (by omega) u) := by
  rw [freeTangent, value_sub_J (by omega)]
  exact potential_eq_normal_sub_tangent (by omega) u hfirst

/-- The quadratic perimeter deficit (4.7), retaining p rather than choosing
coordinates on its first-harmonic complement. -/
def deficit {n : ℕ} (hn : 0 < n) (u : Fin n → ℂ) : ℝ :=
  ((n : ℝ) - 1) / 2 * LocalDFT.energyB n (periodize hn u) - pairPotential hn u

theorem deficit_identity {n : ℕ} (hn : 2 ≤ n) (u : Fin n → ℂ)
    (hfirst : centerCoefficient (by omega) u 0 = 0) :
    deficit (by omega) u =
      ((n : ℝ) - 1) / (2 * n) * ((∑ j, normal (by omega) u j ^ 2) / n) -
        value (normal (by omega) u) + value (tangent (by omega) u) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [normal_mean_square, deficit, potential_eq_normal_sub_tangent hn u hfirst]
  field_simp
  ring

end StructuralNote.EdgeNormalForm
