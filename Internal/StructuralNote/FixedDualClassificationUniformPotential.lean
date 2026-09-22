import StructuralNote.FixedDualClassificationSignedCutoff
import StructuralNote.FixedDualClassificationMultiplierLimit

/-! Uniform approximation of the actual grid potential by the actual
normalized step-profile convolution. -/

namespace StructuralNote.FixedDualClassificationUniformPotential

open Real Complex Filter MeasureTheory Set Erdos1045.EventualExact
open FourierMultiplier SchurLiftBounds FiniteBox
open FixedDualClassificationStep FixedDualClassificationStepPotential
open FixedDualClassificationMidpointSynthesis FixedDualClassificationFiniteTail
open FixedDualClassificationSignedCutoff FixedDualClassificationMultiplierLimit
open FixedDualClassificationKernelTail FixedDualClassificationOddSpectrum
open FixedDualClassificationCircleShift FixedDualClassificationPeriodicStep
open scoped Topology BigOperators ComplexConjugate
noncomputable section

theorem continuous_tail_sq_le {m : ℕ} (hm : 0 < m) (q : Fin (2 * m) → ℝ)
    (hq : Antiperiodic hm q) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hb : ∀ j, |q j| ≤ A) {scale : ℝ} (hscale : |scale| ≤ B) (θ : ℝ) (P : ℕ) :
    ‖(continuousPotential q scale θ : ℂ) -
      ∑ k ∈ signedCutoff P, stepTerm q scale θ k‖ ^ 2 ≤
      4 * tailMass (signedCutoff P) * (B * A) ^ 2 := by
  have hmeas := reflected_measurable (circleProfile_measurable q scale) θ
  have hbound : ∀ u ∈ Icc 0 Real.pi, |reflected (circleProfile q scale) θ u| ≤ B * A := by
    intro u _
    exact (reflected_bound (circleProfile_bound q scale A hA hb) θ u).trans
      (mul_le_mul_of_nonneg_right hscale hA)
  have h := potential_truncation_sq_le (box_memLp hmeas hbound) (signedCutoff P)
  have hm' := box_squareMass_le hmeas (mul_nonneg hB hA) hbound
  have he : truncation (reflected (circleProfile q scale) θ) (signedCutoff P) =
      ∑ k ∈ signedCutoff P, stepTerm q scale θ k := by
    unfold truncation
    apply Finset.sum_congr rfl
    intro k _
    rw [reflected_step_coefficient hm q hq]
    unfold stepTerm
    push_cast
    ring
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_left hm'
    (mul_nonneg (by norm_num) (tailMass_nonneg _)))

theorem low_difference_le {n P : ℕ} (hn : 4 * P < n) (heven : Even n)
    (q : Fin n → ℝ) {A : ℝ} (hA : 0 ≤ A) (hq : ∀ j, |q j| ≤ A)
    (scale : ℝ) (j : Fin n) :
    ‖(∑ p ∈ lowFrequencies n (2 * P), finiteTerm q j p) -
      ∑ k ∈ signedCutoff P, stepTerm q scale (cellMidpoint n j) k‖ ≤
      2 * A * ∑ k ∈ Finset.range P, multiplierError n scale k := by
  have hn0 : 0 < n := by omega
  let : NeZero n := ⟨by omega⟩
  rw [finite_sum_low hn heven, step_sum_signedCutoff, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ Finset.range P,
        ‖(finiteTerm q j (2 * k + 1) + conj (finiteTerm q j (2 * k + 1))) -
          (stepTerm q scale (cellMidpoint n j) k + conj (stepTerm q scale (cellMidpoint n j) k))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range P, 2 * (multiplierError n scale k * A) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [add_sub_add_comm, ← map_sub]
      have ht := term_difference_norm_le hn0 q hA hq scale j k
        (by have hk' := Finset.mem_range.mp hk; omega)
      exact (norm_add_le _ _).trans (by rw [norm_conj]; linarith)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring

theorem low_error_tendsto {scale : ℕ → ℝ} (hscale : Tendsto scale atTop (𝓝 1))
    (A : ℝ) (P : ℕ) :
    Tendsto (fun n : ℕ => 2 * A * ∑ k ∈ Finset.range P, multiplierError n (scale n) k)
      atTop (𝓝 0) := by
  have h := (tendsto_finsetSum (Finset.range P) (fun k _ => multiplierError_tendsto hscale k)).const_mul (2 * A)
  simpa only [Finset.sum_const_zero, mul_zero] using h

theorem uniform_potential_comparison {scale : ℕ → ℝ}
    (hscale : Tendsto scale atTop (𝓝 1)) {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ hm : 0 < m, ∀ q : Fin (2 * m) → ℝ,
      Antiperiodic hm q → (∀ j, |q j| ≤ A) → ∀ j : Fin (2 * m),
      |operator (2 * m) q j -
        continuousPotential q (scale (2 * m)) (cellMidpoint (2 * m) j)| < ε := by
  have hδ : 0 < ε / 3 := by positivity
  have hδsq : 0 < (ε / 3) ^ 2 := by positivity
  have hf : Tendsto (fun P : ℕ => 8 / ((P : ℝ) + 1) * A ^ 2) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 8 |>.mul_const (A ^ 2)
    simpa only [mul_zero, zero_mul, mul_one_div] using h
  have hc : Tendsto (fun P : ℕ => 4 * tailMass (signedCutoff P) * (2 * A) ^ 2)
      atTop (𝓝 0) := by
    have h := (tailMass_tendsto.comp signedCutoff_tendsto).const_mul 4 |>.mul_const ((2 * A) ^ 2)
    simpa only [Function.comp_def, mul_zero, zero_mul] using h
  obtain ⟨P, hPf, hPc⟩ := ((hf.eventually (gt_mem_nhds hδsq)).and
    (hc.eventually (gt_mem_nhds hδsq))).exists
  have hlow := (low_error_tendsto hscale A P).eventually (gt_mem_nhds hδ)
  have hs : ∀ᶠ n : ℕ in atTop, |scale n| < 2 :=
    hscale.abs.eventually (gt_mem_nhds (by norm_num : |(1 : ℝ)| < 2))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlow.and (hs.and (eventually_gt_atTop (4 * P))))
  refine ⟨N, fun m hmN hm q hq hb j => ?_⟩
  obtain ⟨hlo, hsc, hnP⟩ := hN (2 * m) (by omega)
  let D := ∑ p ∈ lowFrequencies (2 * m) (2 * P), finiteTerm q j p
  let C := ∑ k ∈ signedCutoff P, stepTerm q (scale (2 * m)) (cellMidpoint (2 * m) j) k
  have hd : ‖(operator (2 * m) q j : ℂ) - D‖ < ε / 3 := by
    have h := midpoint_lowFrequency_error (P := 2 * P) (by omega) (even_two_mul m) q j
    have hmass := meanSquare_le_of_bound (by omega) q hA hb
    have hdiv : 8 / ((2 * P : ℕ) + 1 : ℝ) ≤ 8 / ((P : ℝ) + 1) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      push_cast
      linarith
    have hsq : ‖(operator (2 * m) q j : ℂ) - D‖ ^ 2 < (ε / 3) ^ 2 :=
      (h.trans ((mul_le_mul_of_nonneg_left hmass (by positivity)).trans
        (mul_le_mul_of_nonneg_right hdiv (sq_nonneg A)))).trans_lt hPf
    exact (sq_lt_sq₀ (norm_nonneg _) hδ.le).mp hsq
  have hc' : ‖(continuousPotential q (scale (2 * m)) (cellMidpoint (2 * m) j) : ℂ) - C‖ < ε / 3 := by
    have h := continuous_tail_sq_le hm q hq hA (by norm_num : (0 : ℝ) ≤ 2) hb hsc.le
      (cellMidpoint (2 * m) j) P
    exact (sq_lt_sq₀ (norm_nonneg _) hδ.le).mp (h.trans_lt hPc)
  have hdc : ‖D - C‖ < ε / 3 :=
    (low_difference_le hnP (even_two_mul m) q hA hb (scale (2 * m)) j).trans_lt hlo
  have ht := (norm_sub_le_norm_sub_add_norm_sub (operator (2 * m) q j : ℂ) D
    (continuousPotential q (scale (2 * m)) (cellMidpoint (2 * m) j) : ℂ)).trans
      (add_le_add le_rfl (norm_sub_le_norm_sub_add_norm_sub D C
        (continuousPotential q (scale (2 * m)) (cellMidpoint (2 * m) j) : ℂ)))
  rw [norm_sub_rev C _] at ht
  have hfinal : ‖(operator (2 * m) q j : ℂ) -
      (continuousPotential q (scale (2 * m)) (cellMidpoint (2 * m) j) : ℂ)‖ < ε := by linarith
  simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hfinal

theorem normalized_potential_comparison {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ hm : 0 < m, ∀ q : Fin (2 * m) → ℝ,
      Antiperiodic hm q → (∀ j, |q j| ≤ A) → ∀ j : Fin (2 * m),
      |operator (2 * m) q j -
        continuousPotential q (profileScale (2 * m)) (cellMidpoint (2 * m) j)| < ε :=
  uniform_potential_comparison profileScale_tendsto hA hε

end
end StructuralNote.FixedDualClassificationUniformPotential
