import Erdos1045.FaberFourier
import Erdos1045.FaberAlgebra

/-! # From the differentiated generating identity to coefficient remainder bounds

The quotient is estimated on actual functions of the circle parameter. Parseval
is then applied; no pointwise quotient identity between Fourier coefficients is
assumed. This is the analytic passage absent from the initial algebraic pilot.
-/

namespace Erdos1045.FaberFourier

open MeasureTheory
open scoped BigOperators
open Erdos1045.FaberAlgebra
noncomputable section

theorem series_summable {d : ℕ → ℂ} (hd : Summable (fun k => ‖d k‖)) (t : ℝ) :
    Summable (fun k => d k * character k t) := by
  apply Summable.of_norm
  simpa [norm_mul, norm_character] using hd

theorem norm_sub_summable {d p : ℕ → ℂ}
    (hd : Summable (fun k => ‖d k‖)) (hp : Summable (fun k => ‖p k‖)) :
    Summable (fun k => ‖d k - p k‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_sub_le _ _) (hd.add hp)

theorem series_sub {d p : ℕ → ℂ}
    (hd : Summable (fun k => ‖d k‖)) (hp : Summable (fun k => ‖p k‖)) (t : ℝ) :
    series (fun k => d k - p k) t = series d t - series p t := by
  simp only [series, sub_mul]
  exact (series_summable hd t).tsum_sub (series_summable hp t)

/-- Parseval turns the generating-function quotient into the full weighted
coefficient estimate, the first analytic step of (4.8). -/
theorem correction_coefficients_le (facts : ClassicalFourierFacts)
    (d p : ℕ → ℂ) (q : ℝ → ℂ)
    (hd : Summable (fun k => ‖d k‖)) (hp : Summable (fun k => ‖p k‖))
    (hid : ∀ t, series d t = correction (q t) (series p t))
    (hq : ∀ t, ‖q t‖ ≤ 1 / 2) :
    (∑' k, ‖d k‖ ^ 2) ≤ 4 * (∑' k, ‖p k‖ ^ 2) := by
  have hpd := facts.parseval d hd
  have hpp := facts.parseval p hp
  have hi : energy (series d) ≤ 4 * energy (series p) := by
    unfold energy
    rw [← integral_const_mul]
    apply integral_mono hpd.2.1 (hpp.2.1.const_mul 4)
    intro t
    dsimp only
    rw [hid t]
    exact norm_correction_sq_le (hq t)
  rw [hpd.2.2, hpp.2.2] at hi
  have hpi : 0 < 2 * Real.pi := by positivity
  nlinarith

/-- The same Parseval passage applied to the first-order remainder gives the
extra small factor `η²` required in (4.13). -/
theorem remainder_coefficients_le (facts : ClassicalFourierFacts)
    (d p : ℕ → ℂ) (q : ℝ → ℂ)
    (hd : Summable (fun k => ‖d k‖)) (hp : Summable (fun k => ‖p k‖))
    (hid : ∀ t, series d t = correction (q t) (series p t))
    {η : ℝ} (hη : 0 ≤ η) (hqη : ∀ t, ‖q t‖ ≤ η)
    (hq : ∀ t, ‖q t‖ ≤ 1 / 2) :
    (∑' k, ‖d k - p k‖ ^ 2) ≤ 4 * η ^ 2 * (∑' k, ‖p k‖ ^ 2) := by
  have hpd := facts.parseval (fun k => d k - p k) (norm_sub_summable hd hp)
  have hpp := facts.parseval p hp
  have hi : energy (series (fun k => d k - p k)) ≤ 4 * η ^ 2 * energy (series p) := by
    unfold energy
    rw [← integral_const_mul]
    apply integral_mono hpd.2.1 (hpp.2.1.const_mul (4 * η ^ 2))
    intro t
    dsimp only
    rw [series_sub hd hp t, hid t]
    exact norm_remainder_sq_le_uniform hη (hqη t) (hq t)
  rw [hpd.2.2, hpp.2.2] at hi
  have hpi : 0 < 2 * Real.pi := by positivity
  nlinarith

def radialCoefficients (r : ℝ) (d : ℕ → ℂ) (k : ℕ) : ℂ := (r : ℂ) ^ k * d k

theorem norm_radialCoefficients_sq {r : ℝ} (hr : 0 ≤ r) (d : ℕ → ℂ) (k : ℕ) :
    ‖radialCoefficients r d k‖ ^ 2 = r ^ (2 * k) * ‖d k‖ ^ 2 := by
  simp [radialCoefficients, norm_pow, Complex.norm_real,
    abs_of_nonneg hr, mul_pow, ← pow_mul, Nat.mul_comm]

/-- Removing radial weights from finitely many coefficients, with the weight
loss `B` stated explicitly rather than silently depending on the dimension. -/
theorem finite_unweight (r B : ℝ) (hr : 0 ≤ r) (hB : 0 ≤ B)
    (d : ℕ → ℂ) (n : ℕ)
    (hweights : ∀ k ∈ Finset.range n, 1 ≤ B * r ^ (2 * k))
    (hd : Summable (fun k => ‖radialCoefficients r d k‖ ^ 2)) :
    (∑ k ∈ Finset.range n, ‖d k‖ ^ 2) ≤ B * (∑' k, ‖radialCoefficients r d k‖ ^ 2) := by
  calc
    (∑ k ∈ Finset.range n, ‖d k‖ ^ 2) ≤
        ∑ k ∈ Finset.range n, B * ‖radialCoefficients r d k‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_radialCoefficients_sq hr]
      have h := mul_le_mul_of_nonneg_right (hweights k hk) (sq_nonneg ‖d k‖)
      simpa [mul_assoc] using h
    _ = B * ∑ k ∈ Finset.range n, ‖radialCoefficients r d k‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ B * (∑' k, ‖radialCoefficients r d k‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hd.sum_le_tsum _ (fun k _ => sq_nonneg _)) hB

end

end Erdos1045.FaberFourier
