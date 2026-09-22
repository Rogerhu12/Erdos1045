import Erdos1045.FaberWeighted
import Erdos1045.FaberRemainder
import Erdos1045.MatrixDefect

/-! # Finite Faber matrices from the full analytic expansions

The only function-identification premise below is the differentiated generating
identity `series R = p/(1+q)` on the chosen circle. All coefficient estimates,
integration, Parseval, truncation, and removal of radial weights are proved.
-/

namespace Erdos1045.FaberFourier

open scoped BigOperators
open Erdos1045.FaberAlgebra Erdos1045.FaberSampling
noncomputable section

def coefficientMatrix {n : ℕ} (R : Fin n → ℕ → ℂ) : MatrixDefect.Mat n :=
  fun j k => R j k

def firstOrder (b : ℕ → ℂ) (k : ℕ) : ℂ := (k : ℂ) * b k

def radialSourceEnergy {n : ℕ} (r : ℝ) (b : Fin n → ℕ → ℂ) : ℝ :=
  ∑ j, ∑' k, ‖radialCoefficients r (firstOrder (b j)) k‖ ^ 2

theorem frobSq_coefficientMatrix {n : ℕ} (R : Fin n → ℕ → ℂ) :
    MatrixDefect.frobSq (coefficientMatrix R) =
      ∑ j, ∑ k ∈ Finset.range n, ‖R j k‖ ^ 2 := by
  simp [MatrixDefect.frobSq, coefficientMatrix, Finset.sum_range, Complex.sq_norm]

theorem radialCoefficients_sub (r : ℝ) (d p : ℕ → ℂ) :
    radialCoefficients r (fun k => d k - p k) =
      fun k => radialCoefficients r d k - radialCoefficients r p k := by
  funext k
  simp [radialCoefficients, mul_sub]

theorem firstOrder_radial_sq {r : ℝ} (hr : 0 ≤ r) (b : ℕ → ℂ) (k : ℕ) :
    ‖radialCoefficients r (firstOrder b) k‖ ^ 2 =
      (k : ℝ) ^ 2 * r ^ (2 * k) * ‖b k‖ ^ 2 := by
  rw [norm_radialCoefficients_sq hr]
  simp [firstOrder, mul_pow]
  ring

theorem radialSourceEnergy_eq (facts : ClassicalFourierFacts)
    {n : ℕ} {r : ℝ} (hr : 0 ≤ r) (b : Fin n → ℕ → ℂ)
    (hp : ∀ j, Summable (fun k => ‖radialCoefficients r (firstOrder (b j)) k‖)) :
    radialSourceEnergy r b = ∑' k, ((k + 1 : ℕ) : ℝ) ^ 2 * r ^ (2 * (k + 1)) *
      (∑ j, ‖b j (k + 1)‖ ^ 2) := by
  have hs (j : Fin n) := (facts.parseval _ (hp j)).1
  have hsum : Summable (fun k => ∑ j, ‖radialCoefficients r (firstOrder (b j)) k‖ ^ 2) :=
    summable_sum fun j _ => hs j
  unfold radialSourceEnergy
  rw [← Summable.tsum_finsetSum (fun j _ => hs j), hsum.tsum_eq_zero_add]
  have hz : (∑ j, ‖radialCoefficients r (firstOrder (b j)) 0‖ ^ 2) = 0 := by
    simp [radialCoefficients, firstOrder]
  rw [hz, zero_add]
  apply tsum_congr
  intro k
  simp_rw [firstOrder_radial_sq hr]
  rw [Finset.mul_sum]

/-- Equation (4.8), in its squared Frobenius form, before substituting (4.4). -/
theorem error_matrix_bound (facts : ClassicalFourierFacts)
    {n : ℕ} {r B L : ℝ} (hr : 0 ≤ r) (hB : 0 ≤ B)
    (R b : Fin n → ℕ → ℂ) (q : Fin n → ℝ → ℂ)
    (hR : ∀ j, Summable (fun k => ‖radialCoefficients r (R j) k‖))
    (hp : ∀ j, Summable (fun k => ‖radialCoefficients r (firstOrder (b j)) k‖))
    (hid : ∀ j t, series (radialCoefficients r (R j)) t =
      correction (q j t) (series (radialCoefficients r (firstOrder (b j))) t))
    (hq : ∀ j t, ‖q j t‖ ≤ 1 / 2)
    (hweights : ∀ k ∈ Finset.range n, 1 ≤ B * r ^ (2 * k))
    (hsource : radialSourceEnergy r b ≤ L) :
    MatrixDefect.frobSq (coefficientMatrix R) ≤ 4 * B * L := by
  have hrow (j : Fin n) : (∑ k ∈ Finset.range n, ‖R j k‖ ^ 2) ≤
      4 * B * (∑' k, ‖radialCoefficients r (firstOrder (b j)) k‖ ^ 2) := by
    have hu := finite_unweight r B hr hB (R j) n hweights (facts.parseval _ (hR j)).1
    have hc := correction_coefficients_le facts _ _ (q j) (hR j) (hp j) (hid j) (hq j)
    have hm := mul_le_mul_of_nonneg_left hc hB
    exact hu.trans (hm.trans_eq (by ring))
  rw [frobSq_coefficientMatrix]
  calc
    _ ≤ ∑ j, 4 * B * (∑' k, ‖radialCoefficients r (firstOrder (b j)) k‖ ^ 2) :=
      Finset.sum_le_sum fun j _ => hrow j
    _ = 4 * B * radialSourceEnergy r b := by unfold radialSourceEnergy; rw [Finset.mul_sum]
    _ ≤ 4 * B * L := mul_le_mul_of_nonneg_left hsource (by positivity)

/-- Equation (4.13), before substituting `η² = O(n E²)` and (4.4). -/
theorem remainder_matrix_bound (facts : ClassicalFourierFacts)
    {n : ℕ} {r B L η : ℝ} (hr : 0 ≤ r) (hB : 0 ≤ B) (hη : 0 ≤ η)
    (R b : Fin n → ℕ → ℂ) (q : Fin n → ℝ → ℂ)
    (hR : ∀ j, Summable (fun k => ‖radialCoefficients r (R j) k‖))
    (hp : ∀ j, Summable (fun k => ‖radialCoefficients r (firstOrder (b j)) k‖))
    (hid : ∀ j t, series (radialCoefficients r (R j)) t =
      correction (q j t) (series (radialCoefficients r (firstOrder (b j))) t))
    (hq : ∀ j t, ‖q j t‖ ≤ 1 / 2) (hqη : ∀ j t, ‖q j t‖ ≤ η)
    (hweights : ∀ k ∈ Finset.range n, 1 ≤ B * r ^ (2 * k))
    (hsource : radialSourceEnergy r b ≤ L) :
    MatrixDefect.frobSq (coefficientMatrix R - coefficientMatrix (fun j => firstOrder (b j))) ≤
      4 * B * η ^ 2 * L := by
  have hrow (j : Fin n) : (∑ k ∈ Finset.range n, ‖R j k - firstOrder (b j) k‖ ^ 2) ≤
      4 * B * η ^ 2 * (∑' k, ‖radialCoefficients r (firstOrder (b j)) k‖ ^ 2) := by
    have hs₀ := (facts.parseval _ (norm_sub_summable (hR j) (hp j))).1
    have hs : Summable (fun k => ‖radialCoefficients r
        (fun k => R j k - firstOrder (b j) k) k‖ ^ 2) := by
      simpa only [radialCoefficients, mul_sub] using hs₀
    have hu := finite_unweight r B hr hB (fun k => R j k - firstOrder (b j) k) n hweights hs
    simp_rw [congrFun (radialCoefficients_sub r (R j) (firstOrder (b j)))] at hu
    have hc := remainder_coefficients_le facts _ _ (q j) (hR j) (hp j) (hid j) hη (hqη j) (hq j)
    have hm := mul_le_mul_of_nonneg_left hc hB
    exact hu.trans (hm.trans_eq (by ring))
  change MatrixDefect.frobSq (coefficientMatrix (fun j k => R j k - firstOrder (b j) k)) ≤ _
  rw [frobSq_coefficientMatrix]
  calc
    _ ≤ ∑ j, 4 * B * η ^ 2 * (∑' k, ‖radialCoefficients r (firstOrder (b j)) k‖ ^ 2) :=
      Finset.sum_le_sum fun j _ => hrow j
    _ = 4 * B * η ^ 2 * radialSourceEnergy r b := by unfold radialSourceEnergy; rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsource (by positivity)

/-- Substitution of the proved sampling estimate into the actual derivative
series. This is (4.4) with the paper's `E² = 2π Σ m² |a_m|²`. -/
theorem source_energy_bound (facts : ClassicalFourierFacts)
    (classicalMoment : ClassicalGeometricMoment)
    {n : ℕ} (hn : 0 < n) {τ c C E : ℝ} (hτ : 0 < τ) (hc : (1 : ℝ) / 2 ≤ c) (hC : 0 ≤ C)
    (a : ℕ → ℂ) (θ : Fin n → ℝ) (hsampling : H1Sampling θ C)
    (ha : Summable (fun m : ℕ => (1 + (m : ℝ) ^ 2) * ‖a m‖ ^ 2))
    (hE : E ^ 2 = 2 * Real.pi * (∑' m : ℕ, (m : ℝ) ^ 2 * ‖a m‖ ^ 2))
    (hp : ∀ j, Summable (fun k => ‖radialCoefficients (radialRatio n τ)
      (firstOrder (coefficient c a θ j)) k‖)) :
    radialSourceEnergy (radialRatio n τ) (coefficient c a θ) ≤
      8 * C * radialConstant τ * (n : ℝ) ^ 2 * E ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hs := (weighted_coefficient_estimate facts classicalMoment hn hτ hc0 hC a θ hsampling ha).2
  rw [radialSourceEnergy_eq facts (radialRatio_pos hn hτ).le _ hp]
  have hS : (∑' k, ((k + 1 : ℕ) : ℝ) ^ 2 * radialRatio n τ ^ (2 * (k + 1)) *
      (∑ j, ‖coefficient c a θ j (k + 1)‖ ^ 2)) ≤
      (2 * C * radialConstant τ / c ^ 2) * (n : ℝ) ^ 2 * E ^ 2 := by
    convert hs using 1 <;> first | rfl | (rw [hE]; ring)
  have hK : 0 ≤ radialConstant τ := le_trans zero_le_one (le_max_left _ _)
  have hcSq : (1 : ℝ) / 4 ≤ c ^ 2 := by nlinarith
  have hfactor : 2 * C * radialConstant τ / c ^ 2 ≤ 8 * C * radialConstant τ := by
    apply (div_le_iff₀ (sq_pos_of_pos hc0)).2
    have hm := mul_le_mul_of_nonneg_left hcSq
      (show 0 ≤ 8 * C * radialConstant τ by positivity)
    nlinarith
  exact hS.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hfactor (sq_nonneg (n : ℝ))) (sq_nonneg E))

/-- Fully combined matrix bound (4.8): the norm square is `O(n² E²)`. -/
theorem faber_error_energy_bound (facts : ClassicalFourierFacts)
    (classicalMoment : ClassicalGeometricMoment)
    {n : ℕ} (hn : 0 < n) {τ c C E : ℝ} (hτ : 0 < τ) (hc : (1 : ℝ) / 2 ≤ c) (hC : 0 ≤ C)
    (a : ℕ → ℂ) (θ : Fin n → ℝ) (hsampling : H1Sampling θ C)
    (ha : Summable (fun m : ℕ => (1 + (m : ℝ) ^ 2) * ‖a m‖ ^ 2))
    (hE : E ^ 2 = 2 * Real.pi * (∑' m : ℕ, (m : ℝ) ^ 2 * ‖a m‖ ^ 2))
    (R : Fin n → ℕ → ℂ) (q : Fin n → ℝ → ℂ)
    (hR : ∀ j, Summable (fun k => ‖radialCoefficients (radialRatio n τ) (R j) k‖))
    (hp : ∀ j, Summable (fun k => ‖radialCoefficients (radialRatio n τ)
      (firstOrder (coefficient c a θ j)) k‖))
    (hid : ∀ j t, series (radialCoefficients (radialRatio n τ) (R j)) t = correction (q j t)
      (series (radialCoefficients (radialRatio n τ) (firstOrder (coefficient c a θ j))) t))
    (hq : ∀ j t, ‖q j t‖ ≤ 1 / 2) :
    MatrixDefect.frobSq (coefficientMatrix R) ≤
      32 * Real.exp (2 * τ) * C * radialConstant τ * (n : ℝ) ^ 2 * E ^ 2 := by
  have hs := source_energy_bound facts classicalMoment hn hτ hc hC a θ hsampling ha hE hp
  have h := error_matrix_bound facts (radialRatio_pos hn hτ).le (Real.exp_pos (2 * τ)).le
    R (coefficient c a θ) q hR hp hid hq
    (fun k hk => radial_unweight hn hτ (Nat.le_of_lt (Finset.mem_range.mp hk))) hs
  convert h using 1
  first | rfl | ring

/-- Fully combined matrix remainder bound (4.13), with every dependence on
the sampling constant, radius, and pointwise quotient bound displayed. -/
theorem faber_remainder_energy_bound (facts : ClassicalFourierFacts)
    (classicalMoment : ClassicalGeometricMoment)
    {n : ℕ} (hn : 0 < n) {τ c C E η Q : ℝ} (hτ : 0 < τ)
    (hc : (1 : ℝ) / 2 ≤ c) (hC : 0 ≤ C) (hη : 0 ≤ η)
    (a : ℕ → ℂ) (θ : Fin n → ℝ) (hsampling : H1Sampling θ C)
    (ha : Summable (fun m : ℕ => (1 + (m : ℝ) ^ 2) * ‖a m‖ ^ 2))
    (hE : E ^ 2 = 2 * Real.pi * (∑' m : ℕ, (m : ℝ) ^ 2 * ‖a m‖ ^ 2))
    (R : Fin n → ℕ → ℂ) (q : Fin n → ℝ → ℂ)
    (hR : ∀ j, Summable (fun k => ‖radialCoefficients (radialRatio n τ) (R j) k‖))
    (hp : ∀ j, Summable (fun k => ‖radialCoefficients (radialRatio n τ)
      (firstOrder (coefficient c a θ j)) k‖))
    (hid : ∀ j t, series (radialCoefficients (radialRatio n τ) (R j)) t = correction (q j t)
      (series (radialCoefficients (radialRatio n τ) (firstOrder (coefficient c a θ j))) t))
    (hq : ∀ j t, ‖q j t‖ ≤ 1 / 2) (hqη : ∀ j t, ‖q j t‖ ≤ η)
    (hscale : η ^ 2 ≤ Q * n * E ^ 2) :
    MatrixDefect.frobSq (coefficientMatrix R - coefficientMatrix
      (fun j => firstOrder (coefficient c a θ j))) ≤
      32 * Real.exp (2 * τ) * C * radialConstant τ * Q * (n : ℝ) ^ 3 * E ^ 4 := by
  have hs := source_energy_bound facts classicalMoment hn hτ hc hC a θ hsampling ha hE hp
  have h := remainder_matrix_bound facts (radialRatio_pos hn hτ).le (Real.exp_pos (2 * τ)).le hη
    R (coefficient c a θ) q hR hp hid hq hqη
    (fun k hk => radial_unweight hn hτ (Nat.le_of_lt (Finset.mem_range.mp hk))) hs
  have hK : 0 ≤ radialConstant τ := le_trans zero_le_one (le_max_left _ _)
  have hm := mul_le_mul_of_nonneg_left hscale
    (show 0 ≤ 32 * Real.exp (2 * τ) * C * radialConstant τ * (n : ℝ) ^ 2 * E ^ 2 by positivity)
  exact h.trans (by nlinarith)

end

end Erdos1045.FaberFourier
