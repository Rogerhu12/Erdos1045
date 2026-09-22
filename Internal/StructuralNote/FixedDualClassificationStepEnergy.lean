import StructuralNote.FixedDualClassificationSignedCutoff

/-! The manuscript's positive odd-frequency energy of the actual step profile,
with a uniform tail bound proved from its full Fourier Parseval identity. -/

namespace StructuralNote.FixedDualClassificationStepEnergy

open Real Complex Filter Erdos1045.EventualExact FourierMultiplier SchurLiftBounds
open FixedDualClassificationStep FixedDualClassificationParseval
open FixedDualClassificationOddSpectrum FixedDualClassificationFiniteTail
open FixedDualClassificationMidpointSynthesis FixedDualClassificationSignedCutoff
open scoped Topology BigOperators ComplexConjugate
noncomputable section

def positiveWeight (k : ℕ) : ℝ := 2 * kernelCoefficient (k : ℤ)

theorem positiveWeight_nonneg (k : ℕ) : 0 ≤ positiveWeight k := by
  simp only [positiveWeight, kernelCoefficient, naturalKernelCoefficient]
  split_ifs <;> positivity

theorem positiveWeight_le (k : ℕ) : positiveWeight k ≤ 1 / ((k : ℝ) + 1) := by
  by_cases hk : k = 0
  · subst k; norm_num [positiveWeight, kernelCoefficient, naturalKernelCoefficient]
  · simp only [positiveWeight, kernelCoefficient, naturalKernelCoefficient, if_neg hk]
    have hk0 : 0 < (k : ℝ) + 1 := by positivity
    field_simp
    linarith

theorem positiveWeight_le_one (k : ℕ) : positiveWeight k ≤ 1 :=
  (positiveWeight_le k).trans (by apply (div_le_one (by positivity)).mpr; linarith [Nat.cast_nonneg (α := ℝ) k])

def energyTerm {n : ℕ} (q : Fin n → ℝ) (scale : ℝ) (k : ℕ) : ℝ :=
  positiveWeight k * ‖profileCoefficient (stepProfile q scale) (2 * k + 1)‖ ^ 2

def continuousEnergy {n : ℕ} (q : Fin n → ℝ) (scale : ℝ) : ℝ := ∑' k, energyTerm q scale k

theorem positive_bessel {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) (scale : ℝ) (s : Finset ℕ) :
    ∑ k ∈ s, ‖profileCoefficient (stepProfile q scale) (2 * k + 1)‖ ^ 2 ≤
      scale ^ 2 * meanSquare q := by
  classical
  have hinj : Set.InjOn (fun k : ℕ => (2 * k + 1 : ℤ)) s := by intro a _ b _ h; dsimp only at h; omega
  rw [← Finset.sum_image (f := fun p : ℤ => ‖profileCoefficient (stepProfile q scale) p‖ ^ 2) hinj]
  convert profileCoefficient_bessel hn q scale (s.image (fun k : ℕ => (2 * k + 1 : ℤ))) using 1
  unfold meanSquare
  ring

theorem energy_summable {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) (scale : ℝ) :
    Summable (energyTerm q scale) := by
  apply summable_of_sum_le (fun k => mul_nonneg (positiveWeight_nonneg k) (sq_nonneg _))
  intro s
  apply le_trans _ (positive_bessel hn q scale s)
  exact Finset.sum_le_sum (fun k _ => mul_le_of_le_one_left (sq_nonneg _) (positiveWeight_le_one k))

theorem energyTerm_eq {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) (scale : ℝ) (k : ℕ) :
    energyTerm q scale k = positiveWeight k *
      (scale * sinc ((2 * k + 1 : ℕ) * Real.pi / n)) ^ 2 *
        ‖signedMidpointCoefficient q (2 * k + 1)‖ ^ 2 := by
  rw [energyTerm, profileCoefficient_eq hn]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Int.cast_one,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  ring

theorem continuousEnergy_tail {n P : ℕ} (hn : 0 < n) (q : Fin n → ℝ) (scale : ℝ) :
    0 ≤ continuousEnergy q scale - ∑ k ∈ Finset.range P, energyTerm q scale k ∧
    continuousEnergy q scale - ∑ k ∈ Finset.range P, energyTerm q scale k ≤
      scale ^ 2 * meanSquare q / ((P : ℝ) + 1) := by
  classical
  have hs := (energy_summable hn q scale).hasSum
  refine ⟨sub_nonneg.mpr (sum_le_hasSum _ (fun k _ =>
    mul_nonneg (positiveWeight_nonneg k) (sq_nonneg _)) hs), ?_⟩
  have hlim := hs.tendsto_sum_nat.sub_const (∑ k ∈ Finset.range P, energyTerm q scale k)
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop P] with J hJ
  rw [← Finset.sum_sdiff_eq_sub (Finset.range_mono hJ)]
  calc
    _ ≤ ∑ k ∈ Finset.range J \ Finset.range P,
        (1 / ((P : ℝ) + 1)) * ‖profileCoefficient (stepProfile q scale) (2 * k + 1)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply (positiveWeight_le k).trans
      apply one_div_le_one_div_of_le (by positivity)
      have hkp : P ≤ k := by simpa only [Finset.mem_range, not_lt] using (Finset.mem_sdiff.mp hk).2
      exact_mod_cast Nat.add_le_add_right hkp 1
    _ ≤ scale ^ 2 * meanSquare q / ((P : ℝ) + 1) := by
      rw [← Finset.mul_sum]
      simp only [div_eq_inv_mul, mul_one]
      exact mul_le_mul_of_nonneg_left (positive_bessel hn q scale _) (by positivity)

theorem finite_positive_energy {n P : ℕ} [NeZero n] (hn : 4 * P < n) (heven : Even n)
    (q : Fin n → ℝ) :
    partialEnergy q (lowFrequencies n (2 * P)) =
      ∑ k ∈ Finset.range P, SchurWeights.weight n (2 * k + 1) *
        ‖signedMidpointCoefficient q (2 * k + 1)‖ ^ 2 := by
  have h := sum_low_odd hn heven
    (fun p => ((SchurWeights.weight n p * normSq (realCoefficient q p) : ℝ) : ℂ))
    (fun p hp => by rw [SchurWeights.weight_eq_zero (fun ha => hp ha.1)]; simp)
  have hreal := congrArg Complex.re h
  simp only [Complex.re_sum, Complex.ofReal_re, add_re] at hreal
  simp_rw [weight_neg heven, realCoefficient_neg, normSq_conj] at hreal
  unfold partialEnergy
  rw [hreal, Finset.mul_sum]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  have hc := midpointCoefficient_normSq q (positiveFrequency hn k)
  rw [← signedMidpointCoefficient_nat] at hc
  rw [← hc, Complex.normSq_eq_norm_sq]
  simp only [positiveFrequency, Fin.val_mk, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  ring

end
end StructuralNote.FixedDualClassificationStepEnergy
