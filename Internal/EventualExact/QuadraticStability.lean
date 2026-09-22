import EventualExact.GeometricLogRemainder
import Erdos1045.GapRigidity

/-! Quantitative stability of the actual pair energy and Schur potential. -/

noncomputable section
open scoped BigOperators

namespace Erdos1045.EventualExact.QuadraticStability

open Complex SchurSpectrum

theorem energyA_le_uniform_ratio {n : ℕ} (u : ℕ → ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ h ∈ (Finset.range n).erase 0, ∀ j, ‖LocalDFT.pairRatio n u j h‖ ≤ δ) :
    LocalDFT.energyA n u ≤ (n : ℝ) ^ 2 * δ ^ 2 / 2 := by
  unfold LocalDFT.energyA
  apply div_le_div_of_nonneg_right _ (by norm_num)
  have hin (h : ℕ) (hh : h ∈ (Finset.range n).erase 0) :
      (∑ j ∈ Finset.range n, normSq (LocalDFT.pairRatio n u j h)) ≤ (n : ℝ) * δ ^ 2 := by
    calc
      _ ≤ ∑ _j ∈ Finset.range n, δ ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        rw [Complex.normSq_eq_norm_sq]
        exact (sq_le_sq₀ (norm_nonneg _) hδ).2 (hbound h hh j)
      _ = _ := by simp
  calc
    _ ≤ ∑ _h ∈ (Finset.range n).erase 0, (n : ℝ) * δ ^ 2 := Finset.sum_le_sum hin
    _ ≤ (n : ℝ) * ((n : ℝ) * δ ^ 2) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hcard : ((Finset.range n).erase 0).card ≤ n := by
        simpa using (Finset.card_erase_le : ((Finset.range n).erase 0).card ≤ (Finset.range n).card)
      exact_mod_cast hcard
    _ = _ := by ring

theorem energyA_le_step {n : ℕ} (hn : 4 ≤ n) (u : ℕ → ℂ)
    (hu : Function.Periodic u n) {ε : ℝ} (hε : 0 ≤ ε)
    (hstep : ∀ j, ‖u (j + 1) - u j‖ ≤ ε) :
    LocalDFT.energyA n u ≤ (n : ℝ) ^ 4 * ε ^ 2 / 8 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hedge := GapRigidity.root_edge_lower (show 2 ≤ n by omega)
  have hrelative (j : ℕ) : ‖u (j + 1) - u j‖ ≤
      ((n : ℝ) * ε / 4) * ‖LocalPhase.regularRoot n - 1‖ := by
    apply (hstep j).trans
    have hh := mul_le_mul_of_nonneg_left hedge (show 0 ≤ (n : ℝ) * ε / 4 by positivity)
    have he : ((n : ℝ) * ε / 4) * (4 / n) = ε := by field_simp
    rwa [he] at hh
  have hb := energyA_le_uniform_ratio u (show 0 ≤ 2 * ((n : ℝ) * ε / 4) by positivity)
    (fun h hh j => LocalMaximum.pair_ratio_bound ClosedFourier.geometricSine hn u hu
      (by positivity) hrelative hh j)
  convert hb using 1
  ring

def pairs (n : ℕ) : Finset (ℕ × ℕ) := ((Finset.range n).erase 0) ×ˢ Finset.range n

def ratio {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) (k : ℕ × ℕ) : ℂ :=
  LocalDFT.pairRatio n (periodize hn c) k.2 k.1

theorem pairEnergy_sum {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) :
    (∑ k ∈ pairs n, ‖ratio hn c k‖ ^ 2) = 2 * pairEnergy hn c := by
  simp only [pairs, Finset.sum_product, ratio, pairEnergy, LocalDFT.energyA,
    Complex.normSq_eq_norm_sq]
  ring

theorem pairPotential_sum {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) :
    pairPotential hn c = -(∑ k ∈ pairs n, (ratio hn c k ^ 2).re) / 2 := by
  rw [AntipodalLog.pairPotential_eq_real_sum]
  simp only [pairs, Finset.sum_product, ratio]

theorem ratio_add {n : ℕ} (hn : 0 < n) (c d : Fin n → ℂ) (k : ℕ × ℕ) :
    ratio hn (c + d) k = ratio hn c k + ratio hn d k := by
  simp only [ratio, LocalDFT.pairRatio, periodize, Pi.add_apply]
  ring

def bilinear {n : ℕ} (hn : 0 < n) (c d : Fin n → ℂ) : ℝ :=
  (∑ k ∈ pairs n, (ratio hn c k * ratio hn d k).re) / 2

theorem bilinear_abs_le {n : ℕ} (hn : 0 < n) (c d : Fin n → ℂ) :
    |bilinear hn c d| ≤ Real.sqrt (pairEnergy hn c) * Real.sqrt (pairEnergy hn d) := by
  have hc := pairEnergy_nonneg hn c
  have hd := pairEnergy_nonneg hn d
  have hs := Real.sum_mul_le_sqrt_mul_sqrt (pairs n)
    (fun k => ‖ratio hn c k‖) (fun k => ‖ratio hn d k‖)
  rw [pairEnergy_sum, pairEnergy_sum, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at hs
  have hroot : Real.sqrt 2 * Real.sqrt 2 = 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hrhs : Real.sqrt 2 * Real.sqrt (pairEnergy hn c) *
      (Real.sqrt 2 * Real.sqrt (pairEnergy hn d)) =
      2 * (Real.sqrt (pairEnergy hn c) * Real.sqrt (pairEnergy hn d)) := by
    calc
      _ = (Real.sqrt 2 * Real.sqrt 2) *
          (Real.sqrt (pairEnergy hn c) * Real.sqrt (pairEnergy hn d)) := by ring
      _ = _ := by rw [hroot]
  rw [hrhs] at hs
  have hb : |∑ k ∈ pairs n, (ratio hn c k * ratio hn d k).re| ≤
      ∑ k ∈ pairs n, ‖ratio hn c k‖ * ‖ratio hn d k‖ := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro k _
    simpa only [norm_mul] using Complex.abs_re_le_norm (ratio hn c k * ratio hn d k)
  unfold bilinear
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

theorem potential_abs_le_energy {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) :
    |pairPotential hn c| ≤ pairEnergy hn c := by
  have hb := bilinear_abs_le hn c c
  rw [Real.mul_self_sqrt (pairEnergy_nonneg hn c)] at hb
  rw [pairPotential_sum]
  simpa only [bilinear, pow_two, abs_div, abs_neg] using hb

theorem potential_add {n : ℕ} (hn : 0 < n) (c d : Fin n → ℂ) :
    pairPotential hn (c + d) = pairPotential hn c + pairPotential hn d - 2 * bilinear hn c d := by
  simp only [pairPotential_sum, ratio_add, bilinear]
  have he (k : ℕ × ℕ) : ((ratio hn c k + ratio hn d k) ^ 2).re =
      (ratio hn c k ^ 2).re + (ratio hn d k ^ 2).re + 2 * (ratio hn c k * ratio hn d k).re := by
    simp [add_sq, Complex.add_re, Complex.mul_re, Complex.mul_im]
    ring
  simp only [he, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem potential_difference_le {n : ℕ} (hn : 0 < n) (c d : Fin n → ℂ) :
    |pairPotential hn (c + d) - pairPotential hn c| ≤
      2 * Real.sqrt (pairEnergy hn c) * Real.sqrt (pairEnergy hn d) + pairEnergy hn d := by
  rw [potential_add]
  have he : pairPotential hn c + pairPotential hn d - 2 * bilinear hn c d -
      pairPotential hn c = pairPotential hn d - 2 * bilinear hn c d := by ring
  rw [he]
  have ht := abs_sub (pairPotential hn d) (2 * bilinear hn c d)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ht
  have hb := bilinear_abs_le hn c d
  have hd := potential_abs_le_energy hn d
  nlinarith

theorem pairEnergy_add_le {n : ℕ} (hn : 0 < n) (c d : Fin n → ℂ) :
    pairEnergy hn (c + d) ≤ 2 * pairEnergy hn c + 2 * pairEnergy hn d := by
  have hpoint (k : ℕ × ℕ) : ‖ratio hn (c + d) k‖ ^ 2 ≤
      2 * ‖ratio hn c k‖ ^ 2 + 2 * ‖ratio hn d k‖ ^ 2 := by
    rw [ratio_add, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
    nlinarith [sq_nonneg ((ratio hn c k).re - (ratio hn d k).re),
      sq_nonneg ((ratio hn c k).im - (ratio hn d k).im)]
  have hs := Finset.sum_le_sum (s := pairs n) (fun k _ => hpoint k)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, pairEnergy_sum] at hs
  linarith

end Erdos1045.EventualExact.QuadraticStability
