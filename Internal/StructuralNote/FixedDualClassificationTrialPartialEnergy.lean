import StructuralNote.FixedDualClassificationTrialAverages

/-! Nine actual low-frequency terms of a cell-average trial are bounded by
the finite box maximum, and converge to their corresponding integral terms. -/

namespace StructuralNote.FixedDualClassificationTrialPartialEnergy

open Real Complex Filter MeasureTheory Erdos1045.EventualExact FourierMultiplier
open FixedDualClassificationStep FixedDualClassificationCoefficientBound
open FixedDualClassificationTrialAverages FixedDualClassificationMultiplierLimit
open FixedDualClassificationStepEnergy FixedDualClassificationFiniteTail
open FixedDualClassificationGridComparison FixedDualClassificationOddSpectrum
open scoped BigOperators Topology
noncomputable section

def thirdPartial (f : ℝ → ℝ) (n P : ℕ) : ℝ :=
  ∑ k ∈ Finset.range P, SchurWeights.weight n (3 * (2 * k + 1)) *
    ‖signedMidpointCoefficient (cellAverage f n) (3 * (2 * k + 1))‖ ^ 2

def thirdLimit (f : ℝ → ℝ) (P : ℕ) : ℝ :=
  ∑ k ∈ Finset.range P, (1 / (6 * (k : ℝ) + 4)) *
    ‖coefficient f (3 * (2 * k + 1))‖ ^ 2

theorem thirdPartial_le_energy {n P : ℕ} (hn : 12 * P < n) (heven : Even n)
    (f : ℝ → ℝ) :
    thirdPartial f n P ≤ normalizedBoxEnergy (operator n) (cellAverage f n) := by
  classical
  let : NeZero n := ⟨by omega⟩
  have hlow := (energy_lowFrequency_error (P := 2 * (3 * P)) (by omega : 0 < n)
    heven (cellAverage f n)).1
  rw [finite_positive_energy (by omega : 4 * (3 * P) < n) heven] at hlow
  apply le_trans _ (sub_nonneg.mp hlow)
  let g (k : ℕ) := SchurWeights.weight n (2 * k + 1) *
    ‖signedMidpointCoefficient (cellAverage f n) (2 * k + 1)‖ ^ 2
  have he : thirdPartial f n P = ∑ j ∈ (Finset.range P).image (fun k => 3 * k + 1), g j := by
    rw [Finset.sum_image (fun a _ b _ h => by omega)]
    apply Finset.sum_congr rfl
    intro k _
    have hnat : 2 * (3 * k + 1) + 1 = 3 * (2 * k + 1) := by omega
    have hint : (2 * (3 * k + 1) + 1 : ℤ) = 3 * (2 * k + 1) := by omega
    simp only [g, hnat]
    congr 2
    push_cast
    congr 2
    omega
  rw [he]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k _ _
    exact mul_nonneg (SchurWeights.weight_nonneg _ _) (sq_nonneg _)

theorem thirdPartial_le_B {m P : ℕ} (hm : 0 < m) (hn : 12 * P < 2 * m)
    (f : ℝ → ℝ) (hbox : ∀ t, |f t| ≤ Real.pi / 2) :
    thirdPartial f (2 * m) P ≤ FiniteBox.B hm := by
  apply (thirdPartial_le_energy hn (even_two_mul m) f).trans
  exact FiniteBox.energy_le_maximum hm (cellAverage f (2 * m)) (fun j =>
    (cellAverage_bound (by omega) f hbox j).trans (amplitude_ge_pi_div_two (by omega)))

theorem third_weight_tendsto (k : ℕ) :
    Tendsto (fun n : ℕ => SchurWeights.weight n (3 * (2 * k + 1))) atTop
      (𝓝 (1 / (6 * (k : ℝ) + 4))) := by
  have h := positive_multiplier_tendsto (3 * k + 1)
  have hn : 2 * (3 * k + 1) + 1 = 3 * (2 * k + 1) := by omega
  have hw : 2 * kernelCoefficient ((3 * k + 1 : ℕ) : ℤ) =
      1 / (6 * (k : ℝ) + 4) := by
    change positiveWeight (3 * k + 1) = _
    rw [positiveWeight_exact, if_neg (by omega : 3 * k + 1 ≠ 0)]
    push_cast
    congr 1
    ring
  simpa only [hn, hw] using h

theorem thirdPartial_tendsto {f : ℝ → ℝ} (hf : Measurable f) {A : ℝ}
    (hA : 0 ≤ A) (hbox : ∀ t, |f t| ≤ A) (P : ℕ) :
    Tendsto (fun n : ℕ => thirdPartial f n P) atTop (𝓝 (thirdLimit f P)) := by
  apply tendsto_finsetSum (Finset.range P)
  intro k _
  exact (third_weight_tendsto k).mul ((cellAverage_coefficient_tendsto hf hA hbox
    (3 * (2 * k + 1))).norm.pow 2)

theorem nine_term_value :
    (∑ k ∈ Finset.range 9,
      (1 / (6 * (k : ℝ) + 4)) * (1 / (2 * (k : ℝ) + 1)) ^ 2) =
      11460107888773 / 43158748192560 := by
  norm_num [Finset.sum_range_succ]

theorem nine_term_strict_margin :
    (531 : ℝ) / 2000 + 1 / 100000 < 11460107888773 / 43158748192560 := by
  norm_num

theorem eventual_B_ge_trial_limit {f : ℝ → ℝ} (hf : Measurable f)
    (hbox : ∀ t, |f t| ≤ Real.pi / 2) {P : ℕ} {C : ℝ} (hC : C < thirdLimit f P) :
    ∀ᶠ m : ℕ in atTop, ∀ hm : 0 < m, C ≤ FiniteBox.B hm := by
  have hmul : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 2 * m) tendsto_id
  have hlim := (thirdPartial_tendsto hf (by positivity : 0 ≤ Real.pi / 2) hbox P).comp hmul
  filter_upwards [hlim.eventually (lt_mem_nhds hC), eventually_gt_atTop (12 * P)]
    with m hmC hmP hm
  exact hmC.le.trans (thirdPartial_le_B hm (by omega) f hbox)

end
end StructuralNote.FixedDualClassificationTrialPartialEnergy
