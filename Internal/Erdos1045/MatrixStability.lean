import Erdos1045.LogDefect
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Dimension-free transfer of logarithmic spectral defect

This is the new stability argument used in both Sections 2.1 and 5.1.
The finite spectral theorem here has no classical theorem as a hypothesis.
The subsequent matrix wrapper will use the classical Mirsky inequality to
control `rootDistance` by the squared Frobenius perturbation.
-/

namespace Erdos1045.MatrixStability

open scoped BigOperators
open Erdos1045.LogDefect

noncomputable section

variable {n : ℕ}

def rootDistance (lam μ : Fin n → ℝ) : ℝ :=
  ∑ i, (Real.sqrt (lam i) - Real.sqrt (μ i)) ^ 2

def rootDeviation (lam : Fin n → ℝ) : ℝ :=
  ∑ i, (Real.sqrt (lam i) - 1) ^ 2

def lowerScale (C : ℝ) : ℝ := Real.exp (-C - 1) / 4

def stabilityConstant (C : ℝ) : ℝ := 2 * (8 * C + 14) / lowerScale C

theorem lowerScale_pos (C : ℝ) : 0 < lowerScale C := by
  unfold lowerScale
  positivity

theorem stabilityConstant_nonneg {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ stabilityConstant C := by
  unfold stabilityConstant
  exact div_nonneg (by nlinarith) (lowerScale_pos C).le

theorem rootDistance_nonneg (lam μ : Fin n → ℝ) : 0 ≤ rootDistance lam μ :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem coordinate_rootDistance_le (lam μ : Fin n → ℝ) (i : Fin n) :
    (Real.sqrt (lam i) - Real.sqrt (μ i)) ^ 2 ≤ rootDistance lam μ := by
  exact Finset.single_le_sum
    (fun j _ => sq_nonneg (Real.sqrt (lam j) - Real.sqrt (μ j))) (Finset.mem_univ i)

theorem rootDeviation_le_total (lam : Fin n → ℝ) (hlam : ∀ i, 0 < lam i) :
    rootDeviation lam ≤ total Finset.univ lam := by
  exact Finset.sum_le_sum fun i _ => sqrt_sub_one_sq_le_chi (hlam i)

theorem rootDeviation_transfer (lam μ : Fin n → ℝ) :
    rootDeviation μ ≤ 2 * rootDeviation lam + 2 * rootDistance lam μ := by
  unfold rootDeviation rootDistance
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  nlinarith [sq_nonneg (Real.sqrt (lam i) - 1 +
    (Real.sqrt (lam i) - Real.sqrt (μ i)))]

/-- The crucial lower spectral bound follows from bounded defect of the
reference spectrum and a small square-root perturbation. -/
theorem lowerScale_le_coordinate (lam μ : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (hμ : ∀ i, 0 ≤ μ i)
    {C : ℝ} (hC : total Finset.univ lam ≤ C)
    (hd : rootDistance lam μ ≤ lowerScale C) (i : Fin n) :
    lowerScale C ≤ μ i := by
  have hcoord := coordinate_bounds_of_total_le Finset.univ lam
    (fun j _ => hlam j) hC (Finset.mem_univ i)
  have hroot : Real.sqrt (Real.exp (-C - 1)) ≤ Real.sqrt (lam i) :=
    Real.sqrt_le_sqrt hcoord.1
  have hslam := Real.sq_sqrt (hlam i).le
  have hsμ := Real.sq_sqrt (hμ i)
  have hsa := Real.sq_sqrt (Real.exp_pos (-C - 1)).le
  have hsnonneg := Real.sqrt_nonneg (Real.exp (-C - 1))
  have hdcoord := (coordinate_rootDistance_le lam μ i).trans hd
  have hsq : (Real.sqrt (lam i) - Real.sqrt (μ i)) ^ 2 ≤
      (Real.sqrt (Real.exp (-C - 1)) / 2) ^ 2 := by
    unfold lowerScale at hdcoord
    nlinarith
  have habs := abs_le_of_sq_le_sq hsq (by positivity)
  have hleft : Real.sqrt (Real.exp (-C - 1)) / 2 ≤ Real.sqrt (μ i) := by
    have hu := (abs_le.mp habs).2
    linarith
  unfold lowerScale
  nlinarith [Real.sqrt_nonneg (μ i)]

theorem coordinate_pos (lam μ : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (hμ : ∀ i, 0 ≤ μ i)
    {C : ℝ} (hC : total Finset.univ lam ≤ C)
    (hd : rootDistance lam μ ≤ lowerScale C) (i : Fin n) : 0 < μ i :=
  (lowerScale_pos C).trans_le (lowerScale_le_coordinate lam μ hlam hμ hC hd i)

/-- A square-root perturbation of size at most one retains a uniform upper
spectral bound.  No factor depending on the number of eigenvalues occurs. -/
theorem coordinate_upper (lam μ : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (hμ : ∀ i, 0 ≤ μ i)
    {C : ℝ} (hC : total Finset.univ lam ≤ C)
    (hd : rootDistance lam μ ≤ 1) (i : Fin n) : μ i ≤ 4 * C + 6 := by
  have hcoord := coordinate_bounds_of_total_le Finset.univ lam
    (fun j _ => hlam j) hC (Finset.mem_univ i)
  have hdcoord := (coordinate_rootDistance_le lam μ i).trans hd
  have hslam := Real.sq_sqrt (hlam i).le
  have hsμ := Real.sq_sqrt (hμ i)
  nlinarith [sq_nonneg (2 * Real.sqrt (lam i) - Real.sqrt (μ i))]

theorem sub_one_sq_le_rootDeviation_term {x C : ℝ}
    (hx : 0 ≤ x) (hu : x ≤ 4 * C + 6) :
    (x - 1) ^ 2 ≤ (8 * C + 14) * (Real.sqrt x - 1) ^ 2 := by
  have hs := Real.sq_sqrt hx
  have hfactor : (Real.sqrt x + 1) ^ 2 ≤ 8 * C + 14 := by
    nlinarith [sq_nonneg (Real.sqrt x - 1)]
  have hm := mul_le_mul_of_nonneg_right hfactor (sq_nonneg (Real.sqrt x - 1))
  have hid : (Real.sqrt x + 1) ^ 2 * (Real.sqrt x - 1) ^ 2 = (x - 1) ^ 2 := by
    calc
      _ = ((Real.sqrt x) ^ 2 - 1) ^ 2 := by ring
      _ = (x - 1) ^ 2 := by rw [hs]
  rwa [hid] at hm

/-- Finite-dimensional nonlinear stability of logarithmic defect.
This is proved here, rather than included in the classical matrix interface. -/
theorem total_transfer (lam μ : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (hμ : ∀ i, 0 ≤ μ i)
    {C : ℝ} (hC : total Finset.univ lam ≤ C)
    (hdsmall : rootDistance lam μ ≤ lowerScale C)
    (hdone : rootDistance lam μ ≤ 1) :
    total Finset.univ μ ≤ stabilityConstant C *
      (total Finset.univ lam + rootDistance lam μ) := by
  have hCnonneg : 0 ≤ C := (total_nonneg Finset.univ lam (fun i _ => hlam i)).trans hC
  have hfactor : 0 ≤ (8 * C + 14) / lowerScale C :=
    div_nonneg (by nlinarith) (lowerScale_pos C).le
  have hbound : total Finset.univ μ ≤
      ((8 * C + 14) / lowerScale C) * rootDeviation μ := by
    unfold total rootDeviation
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hlow := lowerScale_le_coordinate lam μ hlam hμ hC hdsmall i
    have hup := coordinate_upper lam μ hlam hμ hC hdone i
    calc
      chi (μ i) ≤ (μ i - 1) ^ 2 / lowerScale C :=
        chi_le_sub_one_sq_div_lower (lowerScale_pos C) hlow
      _ ≤ ((8 * C + 14) * (Real.sqrt (μ i) - 1) ^ 2) / lowerScale C :=
        div_le_div_of_nonneg_right
          (sub_one_sq_le_rootDeviation_term (hμ i) hup) (lowerScale_pos C).le
      _ = ((8 * C + 14) / lowerScale C) * (Real.sqrt (μ i) - 1) ^ 2 := by ring
  have hroot : rootDeviation μ ≤
      2 * (total Finset.univ lam + rootDistance lam μ) := by
    have h₁ := rootDeviation_transfer lam μ
    have h₂ := rootDeviation_le_total lam hlam
    linarith
  calc
    total Finset.univ μ ≤ ((8 * C + 14) / lowerScale C) * rootDeviation μ := hbound
    _ ≤ ((8 * C + 14) / lowerScale C) *
        (2 * (total Finset.univ lam + rootDistance lam μ)) :=
      mul_le_mul_of_nonneg_left hroot hfactor
    _ = stabilityConstant C * (total Finset.univ lam + rootDistance lam μ) := by
      unfold stabilityConstant
      ring

end

end Erdos1045.MatrixStability
