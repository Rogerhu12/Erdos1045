import StructuralNote.FixedDualClassificationKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Exact Fourier coefficients of the actual grid step function. -/

namespace StructuralNote.FixedDualClassificationStep

open Real Complex MeasureTheory Set
open Erdos1045.EventualExact Erdos1045.EventualExact.FourierMultiplier
open scoped BigOperators ComplexConjugate
noncomputable section

def oscillation (k t : ℝ) : ℂ := Complex.exp (((k * t : ℝ) : ℂ) * Complex.I)

theorem oscillation_add (k t c : ℝ) :
    oscillation k (t + c) = oscillation k c * oscillation k t := by
  unfold oscillation
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem oscillation_continuous (k : ℝ) : Continuous (oscillation k) := by
  unfold oscillation
  fun_prop

theorem integral_oscillation_symmetric (k r : ℝ) :
    (∫ t in -r..r, oscillation k t) = ((2 * r * sinc (k * r) : ℝ) : ℂ) := by
  by_cases hk : k = 0
  · simp [hk, oscillation]
    ring
  have h := intervalIntegral.integral_comp_mul_left
    (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) hk (a := -r) (b := r)
  rw [mul_neg, integral_exp_mul_I_eq_sinc] at h
  change (∫ t in -r..r, oscillation k t) = _ at h
  rw [h, Complex.real_smul]
  push_cast
  field_simp [hk]

theorem integral_oscillation_cell (k c r : ℝ) :
    (∫ t in c - r..c + r, oscillation k t) =
      ((2 * r * sinc (k * r) : ℝ) : ℂ) * oscillation k c := by
  have h := intervalIntegral.integral_comp_add_right (oscillation k) c
    (a := -r) (b := r)
  rw [show -r + c = c - r by ring, add_comm r c] at h
  rw [← h]
  simp_rw [oscillation_add]
  rw [intervalIntegral.integral_const_mul, integral_oscillation_symmetric, mul_comm]

def cellLeft (n j : ℕ) : ℝ := 2 * Real.pi * j / n

def cellMidpoint (n j : ℕ) : ℝ := (2 * j + 1) * Real.pi / n

def cell (n j : ℕ) : Set ℝ := Ico (cellLeft n j) (cellLeft n (j + 1))

/-- The actual one-period step function, extended by zero outside its grid cells. -/
def stepProfile {n : ℕ} (q : Fin n → ℝ) (scale : ℝ) (t : ℝ) : ℝ :=
  ∑ j : Fin n, (cell n j).indicator (fun _ => scale * q j) t

/-- Integer frequencies are retained, without replacing their signed aliases. -/
def signedMidpointCoefficient {n : ℕ} (q : Fin n → ℝ) (p : ℤ) : ℂ :=
  (∑ j : Fin n, (q j : ℂ) * oscillation (-p) (cellMidpoint n j)) / n

def profileCoefficient (f : ℝ → ℝ) (p : ℤ) : ℂ :=
  (∫ t : ℝ, (f t : ℂ) * oscillation (-p) t) / (2 * Real.pi)

theorem cell_integral {n : ℕ} (hn : 0 < n) (j : ℕ) (p : ℤ) :
    (∫ t in cell n j, oscillation (-p) t) =
      ((2 * Real.pi / n * sinc (p * Real.pi / n) : ℝ) : ℂ) *
        oscillation (-p) (cellMidpoint n j) := by
  have hnp : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlr : cellLeft n j ≤ cellLeft n (j + 1) := by
    unfold cellLeft
    push_cast
    apply div_le_div_of_nonneg_right _ hnp.le
    nlinarith [Real.pi_pos]
  rw [cell, integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hlr]
  rw [show cellLeft n j = cellMidpoint n j - Real.pi / n by
      unfold cellLeft cellMidpoint; ring,
    show cellLeft n (j + 1) = cellMidpoint n j + Real.pi / n by
      unfold cellLeft cellMidpoint; push_cast; ring,
    integral_oscillation_cell]
  congr 2
  rw [show -(p : ℝ) * (Real.pi / n) = -(p * Real.pi / n) by ring, sinc_neg]
  ring

theorem cellLeft_mono (n : ℕ) {i j : ℕ} (hij : i ≤ j) :
    cellLeft n i ≤ cellLeft n j := by
  unfold cellLeft
  gcongr

theorem cell_index_unique {n i j : ℕ} {t : ℝ}
    (hi : t ∈ cell n i) (hj : t ∈ cell n j) : i = j := by
  apply le_antisymm
  · by_contra h
    have hji : j + 1 ≤ i := by omega
    have := cellLeft_mono n hji
    have hil := hi.1
    have hjr := hj.2
    linarith
  · by_contra h
    have hij : i + 1 ≤ j := by omega
    have := cellLeft_mono n hij
    have hjl := hj.1
    have hir := hi.2
    linarith

theorem stepProfile_at_cell {n : ℕ} (q : Fin n → ℝ) (scale : ℝ)
    (j : Fin n) {t : ℝ} (ht : t ∈ cell n j) : stepProfile q scale t = scale * q j := by
  classical
  unfold stepProfile
  rw [Finset.sum_eq_single j]
  · exact indicator_of_mem ht _
  · intro k _ hkj
    apply indicator_of_notMem
    intro hk
    exact hkj (Fin.ext (cell_index_unique hk ht))
  · simp

theorem stepProfile_zero {n : ℕ} (q : Fin n → ℝ) (scale : ℝ) {t : ℝ}
    (ht : ∀ j : Fin n, t ∉ cell n j) : stepProfile q scale t = 0 := by
  classical
  simp [stepProfile, indicator_of_notMem, ht]

theorem stepProfile_bound {n : ℕ} (q : Fin n → ℝ) (scale A : ℝ)
    (hA : 0 ≤ A) (hq : ∀ j, |q j| ≤ A) (t : ℝ) :
    |stepProfile q scale t| ≤ |scale| * A := by
  by_cases ht : ∃ j : Fin n, t ∈ cell n j
  · obtain ⟨j, hj⟩ := ht
    rw [stepProfile_at_cell q scale j hj, abs_mul]
    exact mul_le_mul_of_nonneg_left (hq j) (abs_nonneg scale)
  · rw [stepProfile_zero q scale (not_exists.mp ht), abs_zero]
    positivity

theorem stepProfile_measurable {n : ℕ} (q : Fin n → ℝ) (scale : ℝ) :
    Measurable (stepProfile q scale) := by
  unfold stepProfile cell
  exact Finset.measurable_sum _ (fun j _ => measurable_const.indicator measurableSet_Ico)

theorem cell_oscillation_integrable (n j : ℕ) (k : ℝ) (c : ℂ) :
    Integrable ((cell n j).indicator (fun t => c * oscillation k t)) := by
  apply IntegrableOn.integrable_indicator _ measurableSet_Ico
  exact (continuous_const.mul (oscillation_continuous k)).integrableOn_Icc.mono_set
    Ico_subset_Icc_self

theorem profileCoefficient_eq {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (scale : ℝ) (p : ℤ) :
    profileCoefficient (stepProfile q scale) p =
      (scale * sinc (p * Real.pi / n) : ℝ) * signedMidpointCoefficient q p := by
  classical
  have hfun : (fun t => (stepProfile q scale t : ℂ) * oscillation (-p) t) =
      fun t => ∑ j : Fin n, (cell n j).indicator
        (fun t => ((scale * q j : ℝ) : ℂ) * oscillation (-p) t) t := by
    funext t
    simp only [stepProfile, Complex.ofReal_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    by_cases ht : t ∈ cell n j <;> simp [ht]
  unfold profileCoefficient
  rw [hfun, integral_finsetSum Finset.univ (fun (j : Fin n) _ =>
    cell_oscillation_integrable n j (-p) ((scale * q j : ℝ) : ℂ))]
  have hcell (j : Fin n) :
      (∫ t : ℝ, (cell n j).indicator
        (fun t => ((scale * q j : ℝ) : ℂ) * oscillation (-p) t) t) =
      ((scale * q j : ℝ) : ℂ) *
        (((2 * Real.pi / n * sinc (p * Real.pi / n) : ℝ) : ℂ) *
          oscillation (-p) (cellMidpoint n j)) := by
    rw [MeasureTheory.integral_indicator (show MeasurableSet (cell n j) from measurableSet_Ico),
      MeasureTheory.integral_const_mul, cell_integral hn]
  simp_rw [hcell]
  unfold signedMidpointCoefficient
  simp only [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hpC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

theorem oscillation_neg (k t : ℝ) : oscillation (-k) t = conj (oscillation k t) := by
  unfold oscillation
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, neg_mul, Complex.ofReal_neg]
  ring

theorem signedMidpointCoefficient_nat {n : ℕ} (q : Fin n → ℝ) (p : Fin n) :
    signedMidpointCoefficient q p.val = midpointCoefficient q p := by
  unfold signedMidpointCoefficient midpointCoefficient
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [midpointCharacter_eq_exp]
  push_cast
  rw [oscillation_neg]
  congr 2
  unfold oscillation cellMidpoint
  congr 1
  push_cast
  ring

theorem signedMidpointCoefficient_neg {n : ℕ} (q : Fin n → ℝ) (p : ℤ) :
    signedMidpointCoefficient q (-p) = conj (signedMidpointCoefficient q p) := by
  unfold signedMidpointCoefficient
  simp only [map_div₀, map_sum, map_mul, Complex.conj_ofReal, map_natCast, Int.cast_neg]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [← oscillation_neg]

theorem profileCoefficient_nat {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (scale : ℝ) (p : Fin n) :
    profileCoefficient (stepProfile q scale) p.val =
      (scale * sinc (p * Real.pi / n) : ℝ) * midpointCoefficient q p := by
  rw [profileCoefficient_eq hn, signedMidpointCoefficient_nat]
  norm_cast

theorem midpoint_alias {n : ℕ} (hn : 0 < n) (j : ℕ) (p : ℤ) :
    oscillation (-(p + n : ℤ)) (cellMidpoint n j) =
      -oscillation (-p) (cellMidpoint n j) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold oscillation cellMidpoint
  push_cast
  rw [show -(p + n : ℂ) * ((2 * j + 1) * Real.pi / n) * I =
      -(p : ℂ) * ((2 * j + 1) * Real.pi / n) * I +
        (-(j : ℂ)) * (2 * Real.pi * I) - Real.pi * I by
      field_simp; ring,
    Complex.exp_sub_pi_mul_I, Complex.exp_add]
  rw [show (-(j : ℂ)) * (2 * Real.pi * I) = ((-(j : ℤ) : ℤ) : ℂ) *
      (2 * Real.pi * I) by push_cast; ring,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem signedMidpointCoefficient_alias {n : ℕ} (hn : 0 < n)
    (q : Fin n → ℝ) (p : ℤ) :
    signedMidpointCoefficient q (p + n) = -signedMidpointCoefficient q p := by
  unfold signedMidpointCoefficient
  simp_rw [midpoint_alias hn]
  simp only [mul_neg, Finset.sum_neg_distrib, neg_div]

theorem cell_subset_period {n : ℕ} (hn : 0 < n) (j : Fin n) :
    cell n j ⊆ Ico 0 (2 * Real.pi) := by
  intro t ht
  have hl := cellLeft_mono n (Nat.zero_le j.val)
  have hr := cellLeft_mono n (Nat.succ_le_of_lt j.isLt)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp only [cellLeft, Nat.cast_zero, mul_zero, zero_div] at hl
  simp only [cellLeft] at hr
  rw [mul_div_cancel_right₀ _ hnR] at hr
  exact ⟨hl.trans ht.1, ht.2.trans_le hr⟩

theorem stepProfile_outside {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (scale : ℝ) {t : ℝ} (ht : t ∉ Ico 0 (2 * Real.pi)) :
    stepProfile q scale t = 0 := by
  apply stepProfile_zero
  intro j hj
  exact ht (cell_subset_period hn j hj)

theorem profileCoefficient_eq_interval {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (scale : ℝ) (p : ℤ) :
    profileCoefficient (stepProfile q scale) p =
      (∫ t in 0..2 * Real.pi, (stepProfile q scale t : ℂ) * oscillation (-p) t) /
        (2 * Real.pi) := by
  unfold profileCoefficient
  congr 1
  rw [intervalIntegral.integral_of_le (by positivity : 0 ≤ 2 * Real.pi),
    ← integral_Ico_eq_integral_Ioc]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  rw [stepProfile_outside hn q scale ht]
  simp

end
end StructuralNote.FixedDualClassificationStep
