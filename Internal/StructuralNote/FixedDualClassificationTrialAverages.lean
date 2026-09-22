import StructuralNote.FixedDualClassificationThirdReference

/-! Cell averages of an actual bounded measurable profile: box bounds and a
quantitative approximation of each Fourier coefficient. -/

namespace StructuralNote.FixedDualClassificationTrialAverages

open Real Complex Filter MeasureTheory Set Erdos1045.EventualExact
open FixedDualClassificationStep FixedDualClassificationCoefficientBound
open FixedDualClassificationThirdReference
open scoped BigOperators Topology
noncomputable section

def cellAverage (f : ℝ → ℝ) (n : ℕ) (j : Fin n) : ℝ :=
  (n : ℝ) / (2 * Real.pi) * ∫ t in cellLeft n j..cellLeft n (j + 1), f t

theorem cell_length {n : ℕ} (_hn : 0 < n) (j : ℕ) :
    cellLeft n (j + 1) - cellLeft n j = 2 * Real.pi / n := by
  unfold cellLeft
  push_cast
  ring

theorem cell_order {n : ℕ} (hn : 0 < n) (j : ℕ) : cellLeft n j ≤ cellLeft n (j + 1) := by
  have h := cell_length hn j
  have : (0 : ℝ) < 2 * Real.pi / n := by positivity
  linarith

theorem cellAverage_bound {n : ℕ} (hn : 0 < n) (f : ℝ → ℝ) {A : ℝ}
    (hbox : ∀ t, |f t| ≤ A) (j : Fin n) : |cellAverage f n j| ≤ A := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := cellLeft n j) (b := cellLeft n (j + 1)) (f := f) (C := A)
    (fun t _ => by simpa only [Real.norm_eq_abs] using hbox t)
  rw [Real.norm_eq_abs, cell_length hn, abs_of_pos (by positivity : 0 < 2 * Real.pi / n)] at h
  dsimp [cellAverage]
  rw [abs_mul, abs_of_pos (by positivity : 0 < (n : ℝ) / (2 * Real.pi))]
  have hmul := mul_le_mul_of_nonneg_left h (show 0 ≤ (n : ℝ) / (2 * Real.pi) by positivity)
  calc
    _ ≤ (n : ℝ) / (2 * Real.pi) * (A * (2 * Real.pi / n)) := hmul
    _ = A := by
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp

theorem oscillation_sub_bound (p x y : ℝ) :
    ‖oscillation p x - oscillation p y‖ ≤ |p| * |x - y| := by
  have he : oscillation p x - oscillation p y =
      oscillation p y * (oscillation p (x - y) - 1) := by
    rw [mul_sub, mul_one, ← oscillation_add]
    congr 1
    ring
  rw [he, norm_mul, show ‖oscillation p y‖ = 1 by
    simp only [oscillation, norm_exp_ofReal_mul_I], one_mul]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := p * (x - y))
  simpa only [oscillation, mul_comm Complex.I, Real.norm_eq_abs, abs_mul] using h

theorem cell_midpoint_distance {n : ℕ} (hn : 0 < n) (j : ℕ) {t : ℝ}
    (ht : t ∈ Set.uIoc (cellLeft n j) (cellLeft n (j + 1))) :
    |cellMidpoint n j - t| ≤ Real.pi / n := by
  rw [uIoc_of_le (cell_order hn j)] at ht
  have hl : cellLeft n j = cellMidpoint n j - Real.pi / n := by
    unfold cellLeft cellMidpoint
    ring
  have hr : cellLeft n (j + 1) = cellMidpoint n j + Real.pi / n := by
    unfold cellLeft cellMidpoint
    push_cast
    ring
  rw [hl, hr] at ht
  exact abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩

theorem cell_error_bound {n : ℕ} (hn : 0 < n) (f : ℝ → ℝ) {A : ℝ}
    (hA : 0 ≤ A) (hbox : ∀ t, |f t| ≤ A) (p : ℤ) (j : Fin n) :
    ‖∫ t in cellLeft n j..cellLeft n (j + 1),
      (f t : ℂ) * (oscillation (-p) (cellMidpoint n j) - oscillation (-p) t)‖ ≤
      (A * |(p : ℝ)| * (Real.pi / n)) * (2 * Real.pi / n) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := cellLeft n j) (b := cellLeft n (j + 1)) (C := A * |(p : ℝ)| * (Real.pi / n))
    (f := fun t => (f t : ℂ) * (oscillation (-p) (cellMidpoint n j) - oscillation (-p) t)) ?_
  · simpa only [cell_length hn, abs_of_pos (by positivity : 0 < 2 * Real.pi / n)] using h
  intro t ht
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hb := (oscillation_sub_bound (-(p : ℝ)) (cellMidpoint n j) t).trans
    (mul_le_mul_of_nonneg_left (cell_midpoint_distance hn j ht) (abs_nonneg _))
  rw [abs_neg] at hb
  calc
    _ ≤ A * (|(p : ℝ)| * (Real.pi / n)) := mul_le_mul (hbox t) hb (norm_nonneg _) hA
    _ = _ := by ring

theorem cellAverage_coefficient_sum {n : ℕ} (hn : 0 < n) (f : ℝ → ℝ) (p : ℤ) :
    signedMidpointCoefficient (cellAverage f n) p =
      (∑ j : Fin n, ∫ t in cellLeft n j..cellLeft n (j + 1),
        (f t : ℂ) * oscillation (-p) (cellMidpoint n j)) / (2 * Real.pi) := by
  unfold signedMidpointCoefficient
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal]
  simp only [cellAverage, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_natCast, Complex.ofReal_ofNat]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

theorem full_coefficient_sum {n : ℕ} (hn : 0 < n) {f : ℝ → ℝ}
    (hf : Measurable f) {A : ℝ} (hbox : ∀ t, |f t| ≤ A) (p : ℤ) :
    coefficient f p =
      (∑ j : Fin n, ∫ t in cellLeft n j..cellLeft n (j + 1),
        (f t : ℂ) * oscillation (-p) t) / (2 * Real.pi) := by
  have hs := intervalIntegral.sum_integral_adjacent_intervals (n := n) (a := cellLeft n)
    (fun k _ => oscillation_integrable hf hbox (-p) (cellLeft n k) (cellLeft n (k + 1)))
  rw [← Fin.sum_univ_eq_sum_range] at hs
  have he0 : cellLeft n 0 = 0 := by simp [cellLeft]
  have hen : cellLeft n n = 2 * Real.pi := by
    unfold cellLeft
    field_simp
  rw [he0, hen] at hs
  exact congrArg (fun z : ℂ => z / (2 * Real.pi)) hs.symm

theorem cellAverage_coefficient_error {n : ℕ} (hn : 0 < n) {f : ℝ → ℝ}
    (hf : Measurable f) {A : ℝ} (hA : 0 ≤ A) (hbox : ∀ t, |f t| ≤ A) (p : ℤ) :
    ‖signedMidpointCoefficient (cellAverage f n) p - coefficient f p‖ ≤
      A * |(p : ℝ)| * Real.pi / n := by
  rw [cellAverage_coefficient_sum hn, full_coefficient_sum hn hf hbox, ← sub_div,
    ← Finset.sum_sub_distrib, norm_div]
  have hint (j : Fin n) := bounded_intervalIntegrable hf hbox (cellLeft n j) (cellLeft n (j + 1))
  have herr (j : Fin n) :
      (∫ t in cellLeft n j..cellLeft n (j + 1), (f t : ℂ) * oscillation (-p) (cellMidpoint n j)) -
      (∫ t in cellLeft n j..cellLeft n (j + 1), (f t : ℂ) * oscillation (-p) t) =
      ∫ t in cellLeft n j..cellLeft n (j + 1),
        (f t : ℂ) * (oscillation (-p) (cellMidpoint n j) - oscillation (-p) t) := by
    rw [← intervalIntegral.integral_sub
      ((show IntervalIntegrable (fun t => (f t : ℂ)) volume _ _ from
        ⟨(hint j).1.ofReal, (hint j).2.ofReal⟩).mul_const _)
      (oscillation_integrable hf hbox _ _ _)]
    congr 1
    funext t
    ring
  simp_rw [herr]
  have hb := (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum
    (fun (j : Fin n) _ => cell_error_bound hn f hA hbox p j))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
  have hden : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
    norm_num [norm_mul, Real.pi_pos.le]
  rw [hden]
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
  convert hb using 1
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

theorem cellAverage_coefficient_tendsto {f : ℝ → ℝ} (hf : Measurable f)
    {A : ℝ} (hA : 0 ≤ A) (hbox : ∀ t, |f t| ≤ A) (p : ℤ) :
    Tendsto (fun n : ℕ => signedMidpointCoefficient (cellAverage f n) p) atTop
      (𝓝 (coefficient f p)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => norm_nonneg _))
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact cellAverage_coefficient_error hn hf hA hbox p
  · exact tendsto_const_div_atTop_nhds_zero_nat _

theorem amplitude_ge_pi_div_two {n : ℕ} (hn : 2 ≤ n) : Real.pi / 2 ≤ FiniteBox.amplitude n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h := Real.le_tan (x := Real.pi / (2 * n)) (by positivity) (by
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (n : ℝ))).mpr
    nlinarith [Real.pi_pos])
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ (n : ℝ) by positivity)
  unfold FiniteBox.amplitude
  calc
    Real.pi / 2 = (n : ℝ) * (Real.pi / (2 * n)) := by
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      field_simp
    _ ≤ _ := hm

end
end StructuralNote.FixedDualClassificationTrialAverages
