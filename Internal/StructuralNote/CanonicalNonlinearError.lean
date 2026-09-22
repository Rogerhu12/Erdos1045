import StructuralNote.ActualObjectiveLoss

/-! The explicit nonlinear objective errors are a vanishing multiple of the actual Schur residual energy. -/

noncomputable section
open scoped BigOperators Topology

namespace StructuralNote.CanonicalNonlinearError

open Erdos1045 Erdos1045.EventualExact Complex Configuration
open SchurSpectrum SchurLift SchurLiftBounds AngularFirstEnergy GeometricRelativeRemainder
open ActualObjectiveLoss

def quartic {n : ℕ} (hn : 0 < n) (c : Points n) : ℝ := AntipodalLog.fourthEnergy n (periodize hn c)

def canonicalBudget (n : ℕ) (B : ℝ) : ℝ := 16 * Real.pi ^ 4 / (n : ℝ) ^ 2 * B ^ 2

def coefficient (n : ℕ) (δ B A : ℝ) : ℝ :=
  1040 * δ ^ 2 + 1040 * Real.sqrt (2 * canonicalBudget n B) +
    1536 * A * Real.log n / (n : ℝ) ^ 2

def constantTerm (n : ℕ) (B A : ℝ) : ℝ :=
  520 * canonicalBudget n B + 4096 * A * Real.pi ^ 2 / (n : ℝ) ^ 2 * B

theorem quotient_add {n : ℕ} (c d w : Points n) (p : Fin n × Fin n) :
    quotient (c + d) w p = quotient c w p + quotient d w p := by
  simp only [quotient, Pi.add_apply]
  ring

theorem quotient_sq_le_quartic {n : ℕ} (hn : 0 < n) (c : Points n) (p : Fin n × Fin n) :
    ‖quotient c (SignedPressureAngular.root n) p‖ ^ 2 ≤ Real.sqrt (2 * quartic hn c) := by
  have hs := Finset.single_le_sum (fun p (_ : p ∈ (Finset.univ : Finset (Fin n × Fin n))) =>
    pow_nonneg (norm_nonneg (quotient c (SignedPressureAngular.root n) p)) 4) (Finset.mem_univ p)
  rw [quartic, fourthEnergy_eq_chord_sum]
  apply Real.le_sqrt_of_sq_le
  nlinarith only [hs]

theorem quartic_add_le {n : ℕ} (hn : 0 < n) (c d : Points n) :
    quartic hn (c + d) ≤ 8 * quartic hn c + 8 * quartic hn d := by
  simp only [quartic, fourthEnergy_eq_chord_sum]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun p _ => show
      ‖quotient (c + d) (SignedPressureAngular.root n) p‖ ^ 4 ≤
      8 * ‖quotient c (SignedPressureAngular.root n) p‖ ^ 4 +
      8 * ‖quotient d (SignedPressureAngular.root n) p‖ ^ 4 by
    rw [quotient_add]
    exact (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 4).trans
      (by simpa only [mul_add] using (SignedPressureRemainder.fourth_sum_le
        ‖quotient c (SignedPressureAngular.root n) p‖ ‖quotient d (SignedPressureAngular.root n) p‖)))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  linarith only [hs]

theorem quartic_le_of_quotient_square {n : ℕ} (hn : 0 < n) (c : Points n) {K : ℝ}
    (hq : ∀ p, ‖quotient c (SignedPressureAngular.root n) p‖ ^ 2 ≤ K) :
    quartic hn c ≤ K * pairEnergy hn c := by
  rw [quartic, fourthEnergy_eq_chord_sum, pairEnergy_eq_quotient_sum]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun p _ =>
    mul_le_mul_of_nonneg_right (hq p) (sq_nonneg ‖quotient c (SignedPressureAngular.root n) p‖))
  simp only [← pow_add, show 2 + 2 = 4 from rfl, ← Finset.mul_sum] at hs
  linarith only [hs]

theorem canonical_quartic_le {n : ℕ} (hn : 3 ≤ n) (q : Fin n → ℝ) {B : ℝ}
    (hq : meanSquare q ≤ B) : quartic (by omega) (canonicalLift q) ≤ canonicalBudget n B := by
  have hs := pow_le_pow_left₀ (meanSquare_nonneg q) hq 2
  exact (QuarticWindowBound.canonicalLift_fourthEnergy_le hn q).trans
    (mul_le_mul_of_nonneg_left hs (by positivity))

theorem residual_quartic_le {n : ℕ} (hn : 3 ≤ n) (c : Points n) (q : Fin n → ℝ)
    {δ B : ℝ} (_hδ : 0 ≤ δ) (hq : meanSquare q ≤ B)
    (hc : ∀ p, ‖quotient c (SignedPressureAngular.root n) p‖ ≤ δ) :
    quartic (by omega) (c - canonicalLift q) ≤
      (2 * δ ^ 2 + 2 * Real.sqrt (2 * canonicalBudget n B)) * pairEnergy (by omega) (c - canonicalLift q) := by
  apply quartic_le_of_quotient_square
  intro p
  have he := quotient_difference (SignedPressureAngular.root n) c (canonicalLift q) p
  change quotient c (SignedPressureAngular.root n) p - quotient (canonicalLift q) (SignedPressureAngular.root n) p =
    quotient (c - canonicalLift q) (SignedPressureAngular.root n) p at he
  rw [← he]
  have hnorm := norm_sub_le (quotient c (SignedPressureAngular.root n) p)
    (quotient (canonicalLift q) (SignedPressureAngular.root n) p)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hc2 := pow_le_pow_left₀ (norm_nonneg _) (hc p) 2
  have hcan := (quotient_sq_le_quartic (show 0 < n by omega) (canonicalLift q) p).trans
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (canonical_quartic_le hn q hq) (by norm_num : (0 : ℝ) ≤ 2)))
  nlinarith only [hsq, hc2, hcan,
    sq_nonneg (‖quotient c (SignedPressureAngular.root n) p‖ - ‖quotient (canonicalLift q) (SignedPressureAngular.root n) p‖)]

theorem center_sup_sq_le {n : ℕ} (hn : 3 ≤ n) (c : Points n) (q : Fin n → ℝ)
    (hmean : ∑ j, c j = 0) {B : ℝ} (hq : meanSquare q ≤ B) :
    ‖c‖ ^ 2 ≤ 64 * Real.pi ^ 2 / (n : ℝ) ^ 2 * B +
      24 * Real.log n / (n : ℝ) ^ 2 * pairEnergy (by omega) (c - canonicalLift q) := by
  have hB : 0 ≤ B := (meanSquare_nonneg q).trans hq
  have hcan : ‖canonicalLift q‖ ^ 2 ≤ 32 * Real.pi ^ 2 / (n : ℝ) ^ 2 * B := by
    apply ExtremalPolarCenter.sup_sq_of_pointwise _ (by positivity)
    intro j
    exact (canonicalLift_norm_sq_le hn q j).trans (mul_le_mul_of_nonneg_left hq (by positivity))
  have hvmean : ∑ j, (c - canonicalLift q) j = 0 := by
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, hmean, canonicalLift_mean_zero (show 0 < n by omega), sub_self]
  have hv := DiscreteSobolev.sup_sq_le (by omega) (c - canonicalLift q) hvmean
  have he : c = canonicalLift q + (c - canonicalLift q) := by abel
  have hh := norm_add_le (canonicalLift q) (c - canonicalLift q)
  rw [← he] at hh
  have hsq := pow_le_pow_left₀ (norm_nonneg c) hh 2
  linear_combination hsq + 2 * hcan + 2 * hv + sq_nonneg (‖canonicalLift q‖ - ‖c - canonicalLift q‖)

theorem nonlinear_error_le {n : ℕ} (hn : 3 ≤ n) (c : Points n) (q : Fin n → ℝ)
    (hmean : ∑ j, c j = 0) {δ B A : ℝ} (hδ : 0 ≤ δ) (hq : meanSquare q ≤ B)
    (hA : pairEnergy (by omega) c ≤ A)
    (hc : ∀ p, ‖quotient c (SignedPressureAngular.root n) p‖ ≤ δ) :
    65 * quartic (by omega) c + 64 * ‖c‖ ^ 2 * pairEnergy (by omega) c ≤
      constantTerm n B A + coefficient n δ B A * pairEnergy (by omega) (c - canonicalLift q) := by
  have hA0 : 0 ≤ A := (pairEnergy_nonneg (show 0 < n by omega) c).trans hA
  have he : canonicalLift q + (c - canonicalLift q) = c := by abel
  have hQ := quartic_add_le (show 0 < n by omega) (canonicalLift q) (c - canonicalLift q)
  rw [he] at hQ
  have hQc := canonical_quartic_le hn q hq
  have hQv := residual_quartic_le hn c q hδ hq hc
  have hsup := center_sup_sq_le hn c q hmean hq
  have hmul := mul_le_mul_of_nonneg_right hsup hA0
  have hmul' := mul_le_mul_of_nonneg_left hA (sq_nonneg ‖c‖)
  unfold constantTerm coefficient
  linear_combination 65 * hQ + 520 * hQc + 520 * hQv + 64 * hmul + 64 * hmul'

theorem constantTerm_eq (n : ℕ) (B A : ℝ) :
    constantTerm n B A = (8320 * Real.pi ^ 4 * B ^ 2 + 4096 * A * Real.pi ^ 2 * B) / (n : ℝ) ^ 2 := by
  unfold constantTerm canonicalBudget
  ring

open Filter

theorem coefficient_tendsto {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) (B A : ℝ) :
    Tendsto (fun k => coefficient (N k) (δ k) B A) atTop (𝓝 0) := by
  have hi : Tendsto (fun k => ((N k : ℝ) ^ 2)⁻¹) atTop (𝓝 0) := by
    have hh := (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hN) :
      Tendsto (fun k => (N k : ℝ)⁻¹) atTop (𝓝 0)).pow 2
    simpa only [Function.comp_def, inv_pow, zero_pow (by norm_num : 2 ≠ 0)] using hh
  have hcan : Tendsto (fun k => canonicalBudget (N k) B) atTop (𝓝 0) := by
    simpa only [canonicalBudget, div_eq_mul_inv, mul_zero, zero_mul] using
      (hi.const_mul (16 * Real.pi ^ 4)).mul_const (B ^ 2)
  have hs : Tendsto (fun k => Real.sqrt (2 * canonicalBudget (N k) B)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp (by simpa only [mul_zero] using hcan.const_mul 2)
  have hl : Tendsto (fun k => Real.log (N k) / (N k : ℝ) ^ 2) atTop (𝓝 0) := by
    have hh := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 2)).tendsto_div_nhds_zero
    simpa only [Function.comp_def, Real.rpow_two] using hh.comp (tendsto_natCast_atTop_atTop.comp hN)
  have hh := (((hδ.pow 2).const_mul 1040).add (hs.const_mul 1040)).add (hl.const_mul (1536 * A))
  simpa only [coefficient, zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero, mul_div_assoc] using hh

end StructuralNote.CanonicalNonlinearError
