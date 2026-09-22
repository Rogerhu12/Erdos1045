import StructuralNote.ExplicitKernelBalanced
import StructuralNote.FixedDualClassificationTrialNearMaximum

/-! Explicit Fourier comparison and phase localization for near-maximal words. -/

namespace StructuralNote.ExplicitKernelLocalization

open Real Complex Set Filter MeasureTheory
open Erdos1045.EventualExact FourierMultiplier FiniteBox SchurLiftBounds
open FixedDualPrimitive FixedDualClassificationKernelTail
open FixedDualClassificationOddSpectrum FixedDualClassificationSignedCutoff
open FixedDualClassificationFiniteTail FixedDualClassificationMultiplierLimit
open FixedDualClassificationStep FixedDualClassificationStepPotential
open FixedDualClassificationStepEnergy
open FixedDualClassificationMidpointSynthesis
open FixedDualClassificationUniformPotential FixedDualClassificationUniformEnergy
open FixedDualClassificationTrialCoefficients FixedDualClassificationTrialAverages
open FixedDualClassificationTrialPartialEnergy FixedDualClassificationTrialLowerBound
open ExplicitKernelRate ExplicitKernelBalanced
open scoped BigOperators Topology ComplexConjugate
noncomputable section

/-- An explicit reciprocal-square tail for the signed kernel cutoff. -/
theorem tailMass_signedCutoff_le (P : ℕ) (hP : 1 ≤ P) :
    tailMass (signedCutoff P) ≤ 1 / (4 * ((P : ℝ) + 1)) := by
  have hbase : Tendsto
      (fun s : Finset ℤ => ∑ k ∈ s, kernelCoefficient k ^ 2)
      atTop (𝓝 (squareMass kernel)) := kernelCoefficient_parseval
  have hlim : Tendsto
      (fun Q : ℕ => ∑ k ∈ signedCutoff Q, kernelCoefficient k ^ 2)
      atTop (𝓝 (squareMass kernel)) :=
    hbase.comp signedCutoff_tendsto
  rw [tailMass]
  apply le_of_tendsto (hlim.sub_const (∑ k ∈ signedCutoff P, kernelCoefficient k ^ 2))
  filter_upwards [eventually_ge_atTop P] with Q hPQ
  rw [sum_signedCutoff, sum_signedCutoff, ← Finset.sum_Ico_eq_sub _ hPQ]
  have hb := reciprocal_square_sum_le (P := P) (n := Q)
    (Finset.Ico P Q) (fun k : ℕ => k + 1)
    (fun i _ j _ hij => Nat.add_right_cancel hij)
    (fun i hi => by simp only [Finset.mem_Ico] at hi; omega)
  calc
    (∑ k ∈ Finset.Ico P Q,
        (kernelCoefficient (k : ℤ) ^ 2 + kernelCoefficient (Int.negSucc k) ^ 2)) =
        (1 / 8 : ℝ) * ∑ k ∈ Finset.Ico P Q, (((k + 1 : ℕ) : ℝ) ^ 2)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hkP := (Finset.mem_Ico.mp hk).1
      simp only [kernelCoefficient, naturalKernelCoefficient, if_neg (by omega : k ≠ 0)]
      push_cast
      field_simp
      ring
    _ ≤ (1 / 8 : ℝ) * (2 / ((P : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = 1 / (4 * ((P : ℝ) + 1)) := by field_simp; norm_num

/-- The profile normalization differs from one by an explicit quadratic amount. -/
theorem profileScale_bounds {n : ℕ} (hn : 2 ≤ n) :
    0 < profileScale n ∧ profileScale n ≤ 1 ∧
      1 - profileScale n ≤ Real.pi ^ 2 / (8 * (n : ℝ) ^ 2) := by
  let x : ℝ := Real.pi / (2 * n)
  have hnR : (0 : ℝ) < n := by positivity
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hxpi : x < Real.pi / 2 := by
    dsimp [x]
    have hn2R : (2 : ℝ) ≤ n := by exact_mod_cast hn
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * n)).2
    nlinarith [Real.pi_pos]
  have htan : 0 < Real.tan x := Real.tan_pos_of_pos_of_lt_pi_div_two hx0 hxpi
  have hscale : profileScale n = x / Real.tan x := by
    unfold profileScale FiniteBox.amplitude
    dsimp [x]
    field_simp
  have hpos : 0 < profileScale n := by rw [hscale]; positivity
  have hle : profileScale n ≤ 1 := by
    unfold profileScale
    exact (div_le_one (FiniteBox.amplitude_pos hn)).2 (amplitude_ge_pi_div_two hn)
  have hcospos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith, hxpi⟩
  have hcos_le : Real.cos x ≤ profileScale n := by
    rw [hscale]
    apply (le_div_iff₀ htan).2
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hcospos.ne']
    exact Real.sin_le hx0.le
  have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
  have hxid : x ^ 2 / 2 = Real.pi ^ 2 / (8 * (n : ℝ) ^ 2) := by
    dsimp [x]
    ring
  refine ⟨hpos, hle, ?_⟩
  rw [← hxid]
  linarith

theorem profileScale_sinc_error {n : ℕ} (hn : 2 ≤ n) {y : ℝ}
    (hy0 : 0 ≤ y) (hy : y ≤ 1 / 2) :
    |profileScale n * sinc y - 1| ≤
      Real.pi ^ 2 / (8 * (n : ℝ) ^ 2) + y := by
  have hs := profileScale_bounds hn
  have hsinc := sinc_interval hy0 hy
  have hs0 : 0 ≤ sinc y := by linarith
  have hs1 : sinc y ≤ 1 := hsinc.2
  have hprod0 : 0 ≤ profileScale n * sinc y := mul_nonneg hs.1.le hs0
  have hprod1 : profileScale n * sinc y ≤ 1 := by nlinarith
  rw [abs_of_nonpos (by linarith : profileScale n * sinc y - 1 ≤ 0)]
  have hpiece : profileScale n * (1 - sinc y) ≤ y := by
    have hnonneg : 0 ≤ 1 - sinc y := by linarith
    have hm := mul_le_mul_of_nonneg_right hs.2.1 hnonneg
    nlinarith [hm, hsinc.1]
  have hid : -(profileScale n * sinc y - 1) =
      (1 - profileScale n) + profileScale n * (1 - sinc y) := by ring
  rw [hid]
  linarith [hs.2.2]

def localizationCutoff : ℕ := 2 ^ 50
def comparisonOrder : ℕ := 2 ^ 200

theorem cutoff_ge_twenty : 20 ≤ localizationCutoff := by
  norm_num [localizationCutoff]

theorem comparisonOrder_ge_two : 2 ≤ comparisonOrder := by
  norm_num [comparisonOrder]

theorem sixteen_cutoff_le_order : 16 * localizationCutoff ≤ comparisonOrder := by
  norm_num [localizationCutoff, comparisonOrder]

theorem four_cutoff_lt_order : 4 * localizationCutoff < comparisonOrder := by
  norm_num [localizationCutoff, comparisonOrder]

theorem multiplierError_explicit {n k : ℕ} (hn : comparisonOrder ≤ n)
    (hk : k < localizationCutoff) :
    multiplierError n (profileScale n) k ≤
      10 * localizationCutoff / (n : ℝ) := by
  have hn2 : 2 ≤ n := by
    exact comparisonOrder_ge_two.trans hn
  have hn0 : (0 : ℝ) < n := by positivity
  have hP : 20 ≤ localizationCutoff := cutoff_ge_twenty
  by_cases hk0 : k = 0
  · subst k
    have hw0 : SchurWeights.weight n 1 = 0 :=
      SchurWeights.weight_eq_zero (by simp [SchurWeights.Active])
    simp [multiplierError, kernelCoefficient, naturalKernelCoefficient, hw0]
    positivity
  let p : ℕ := 2 * k + 1
  let y : ℝ := (p : ℝ) * Real.pi / n
  have hpodd : Odd p := ⟨k, by dsimp [p]⟩
  have hp3 : 3 ≤ p := by dsimp [p]; omega
  have hpP : p < 2 * localizationCutoff := by dsimp [p]; omega
  have hsize : 8 * (p + 1) ≤ n := by
    have hPn := sixteen_cutoff_le_order
    have := hPn.trans hn
    omega
  have hw := weight_error_le hpodd hp3 hsize
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hyb : y ≤ 8 * localizationCutoff / (n : ℝ) := by
    apply (div_le_div_iff_of_pos_right hn0).2
    have hpR : (p : ℝ) ≤ 2 * localizationCutoff := by exact_mod_cast hpP.le
    nlinarith [Real.pi_le_four, mul_le_mul_of_nonneg_left hpR Real.pi_pos.le]
  have hsmall : (8 : ℝ) * localizationCutoff / n ≤ 1 / 2 := by
    apply (div_le_iff₀ hn0).2
    have hPn := sixteen_cutoff_le_order
    have hPnR : (16 : ℝ) * localizationCutoff ≤ n := by exact_mod_cast hPn.trans hn
    linarith
  have hze := profileScale_sinc_error hn2 hy0 (hyb.trans hsmall)
  have hquad : Real.pi ^ 2 / (8 * (n : ℝ) ^ 2) ≤ 2 / n := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hpi2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_le_four]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * (n : ℝ) ^ 2)).2
    field_simp
    nlinarith
  have hze' : |profileScale n * sinc y - 1| ≤
      (2 + 8 * localizationCutoff) / (n : ℝ) := by
    calc
      _ ≤ Real.pi ^ 2 / (8 * (n : ℝ) ^ 2) + y := hze
      _ ≤ 2 / n + 8 * localizationCutoff / n := add_le_add hquad hyb
      _ = _ := by ring
  have hc : 2 * kernelCoefficient (k : ℤ) = 1 / ((p : ℝ) + 1) := by
    simp only [kernelCoefficient, naturalKernelCoefficient, if_neg hk0]
    dsimp [p]
    push_cast
    field_simp
    ring
  have hc0 : 0 ≤ 2 * kernelCoefficient (k : ℤ) := by rw [hc]; positivity
  have hc1 : 2 * kernelCoefficient (k : ℤ) ≤ 1 := by
    rw [hc]
    apply (div_le_one (by positivity : (0 : ℝ) < (p : ℝ) + 1)).2
    have hp0 : (0 : ℝ) ≤ p := by positivity
    linarith
  have htri := abs_sub_le (SchurWeights.weight n p)
    (2 * kernelCoefficient (k : ℤ))
    (2 * kernelCoefficient (k : ℤ) * (profileScale n * sinc y))
  have hsecond :
      |2 * kernelCoefficient (k : ℤ) -
          2 * kernelCoefficient (k : ℤ) * (profileScale n * sinc y)| ≤
        (2 + 8 * localizationCutoff) / (n : ℝ) := by
    rw [show 2 * kernelCoefficient (k : ℤ) -
        2 * kernelCoefficient (k : ℤ) * (profileScale n * sinc y) =
          -(2 * kernelCoefficient (k : ℤ)) *
            (profileScale n * sinc y - 1) by ring,
      abs_mul, abs_neg, abs_of_nonneg hc0]
    have hfac : 0 ≤ (2 + 8 * localizationCutoff) / (n : ℝ) := by positivity
    calc
      _ ≤ 2 * kernelCoefficient (k : ℤ) *
          ((2 + 8 * localizationCutoff) / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hze' hc0
      _ ≤ 1 * ((2 + 8 * localizationCutoff) / (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hc1 hfac
      _ = _ := one_mul _
  have hw' : |SchurWeights.weight n p - 2 * kernelCoefficient (k : ℤ)| ≤ 36 / n := by
    rw [hc]
    exact hw
  have htotal := htri.trans (add_le_add hw' hsecond)
  have hnum : (36 + (2 + 8 * localizationCutoff) : ℝ) ≤ 10 * localizationCutoff := by
    exact_mod_cast (show 36 + (2 + 8 * localizationCutoff) ≤
      10 * localizationCutoff by omega)
  have hfinal : |SchurWeights.weight n p -
      2 * kernelCoefficient (k : ℤ) * (profileScale n * sinc y)| ≤
      10 * localizationCutoff / (n : ℝ) := by calc
    _ ≤ (36 : ℝ) / (n : ℝ) +
        ((2 : ℝ) + 8 * (localizationCutoff : ℝ)) / (n : ℝ) := htotal
    _ = ((36 : ℝ) + ((2 : ℝ) + 8 * (localizationCutoff : ℝ))) / (n : ℝ) := by ring
    _ ≤ (10 : ℝ) * (localizationCutoff : ℝ) / (n : ℝ) :=
      div_le_div_of_nonneg_right hnum hn0.le
  simpa only [multiplierError, p, y] using hfinal

theorem energyMultiplierError_explicit {n k : ℕ} (hn : comparisonOrder ≤ n)
    (hk : k < localizationCutoff) :
    energyMultiplierError n (profileScale n) k ≤
      20 * localizationCutoff / (n : ℝ) := by
  have hn2 : 2 ≤ n := by
    exact comparisonOrder_ge_two.trans hn
  have hn0 : (0 : ℝ) < n := by positivity
  by_cases hk0 : k = 0
  · subst k
    have hw0 : SchurWeights.weight n 1 = 0 :=
      SchurWeights.weight_eq_zero (by simp [SchurWeights.Active])
    simp [energyMultiplierError, positiveWeight, kernelCoefficient,
      naturalKernelCoefficient, hw0]
    positivity
  let p : ℕ := 2 * k + 1
  let y : ℝ := (p : ℝ) * Real.pi / n
  let c : ℝ := 2 * kernelCoefficient (k : ℤ)
  let z : ℝ := profileScale n * sinc y
  have hpP : p < 2 * localizationCutoff := by dsimp [p]; omega
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hyb : y ≤ 8 * localizationCutoff / (n : ℝ) := by
    apply (div_le_div_iff_of_pos_right hn0).2
    have hpR : (p : ℝ) ≤ 2 * localizationCutoff := by exact_mod_cast hpP.le
    nlinarith [Real.pi_le_four, mul_le_mul_of_nonneg_left hpR Real.pi_pos.le]
  have hsmall : (8 : ℝ) * localizationCutoff / n ≤ 1 / 2 := by
    apply (div_le_iff₀ hn0).2
    have hPn := sixteen_cutoff_le_order
    have hPnR : (16 : ℝ) * localizationCutoff ≤ n := by exact_mod_cast hPn.trans hn
    linarith
  have hze := profileScale_sinc_error hn2 hy0 (hyb.trans hsmall)
  have hquad : Real.pi ^ 2 / (8 * (n : ℝ) ^ 2) ≤ 2 / n := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hpi2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_le_four]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * (n : ℝ) ^ 2)).2
    field_simp
    nlinarith
  have hze' : |z - 1| ≤ (2 + 8 * localizationCutoff) / (n : ℝ) := by
    dsimp [z]
    exact hze.trans (by
      calc
        _ ≤ (2 : ℝ) / (n : ℝ) +
            (8 : ℝ) * (localizationCutoff : ℝ) / (n : ℝ) := add_le_add hquad hyb
        _ = ((2 : ℝ) + 8 * (localizationCutoff : ℝ)) / (n : ℝ) := by ring)
  have hs := profileScale_bounds hn2
  have hsinc := sinc_interval hy0 (hyb.trans hsmall)
  have hsinc0 : 0 ≤ sinc y := by linarith [hsinc.1]
  have hz0 : 0 ≤ z := by dsimp [z]; exact mul_nonneg hs.1.le hsinc0
  have hz1 : z ≤ 1 := by
    dsimp [z]
    calc
      profileScale n * sinc y ≤ 1 * 1 :=
        mul_le_mul hs.2.1 hsinc.2 hsinc0 (by norm_num)
      _ = 1 := by ring
  have hc : c = 1 / ((p : ℝ) + 1) := by
    dsimp [c]
    simp only [kernelCoefficient, naturalKernelCoefficient, if_neg hk0]
    dsimp [p]
    push_cast
    field_simp
    ring
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hc1 : c ≤ 1 := by
    rw [hc]
    apply (div_le_one (by positivity : (0 : ℝ) < (p : ℝ) + 1)).2
    have hp0 : (0 : ℝ) ≤ p := by positivity
    linarith
  have hmul : |c * z - c * z ^ 2| ≤ (2 + 8 * localizationCutoff) / (n : ℝ) := by
    rw [show c * z - c * z ^ 2 = -(c * z) * (z - 1) by ring,
      abs_mul, abs_neg, abs_of_nonneg (mul_nonneg hc0 hz0)]
    have hcz : c * z ≤ 1 := by
      simpa only [one_mul] using mul_le_mul hc1 hz1 hz0 (by norm_num : (0 : ℝ) ≤ 1)
    have hfac : 0 ≤ (2 + 8 * localizationCutoff) / (n : ℝ) := by positivity
    exact (mul_le_mul_of_nonneg_left hze' (mul_nonneg hc0 hz0)).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hcz hfac)
  have hm := multiplierError_explicit hn hk
  change |SchurWeights.weight n p - c * z| ≤
    10 * localizationCutoff / (n : ℝ) at hm
  have htri := abs_sub_le (SchurWeights.weight n p) (c * z) (c * z ^ 2)
  have hnum : (10 * localizationCutoff + (2 + 8 * localizationCutoff) : ℝ) ≤
      20 * localizationCutoff := by
    exact_mod_cast (show 10 * localizationCutoff + (2 + 8 * localizationCutoff) ≤
      20 * localizationCutoff by
        have : 20 ≤ localizationCutoff := cutoff_ge_twenty
        omega)
  have hfinal : |SchurWeights.weight n p - c * z ^ 2| ≤
      20 * localizationCutoff / (n : ℝ) := by
    calc
      _ ≤ |SchurWeights.weight n p - c * z| + |c * z - c * z ^ 2| := htri
      _ ≤ (10 : ℝ) * localizationCutoff / n +
          ((2 : ℝ) + 8 * localizationCutoff) / n := add_le_add hm hmul
      _ = ((10 : ℝ) * localizationCutoff +
          ((2 : ℝ) + 8 * localizationCutoff)) / n := by ring
      _ ≤ (20 : ℝ) * localizationCutoff / n :=
        div_le_div_of_nonneg_right hnum hn0.le
  simpa only [energyMultiplierError, positiveWeight, if_neg hk0, p, y, c, z,
    mul_pow] using hfinal

theorem finitePotentialTail_numeric :
    (128 : ℝ) / (2 * localizationCutoff + 1) < (1 / 1200000 : ℝ) ^ 2 := by
  norm_num [localizationCutoff]

theorem continuousPotentialTail_numeric :
    (16 : ℝ) / (localizationCutoff + 1) < (1 / 1200000 : ℝ) ^ 2 := by
  norm_num [localizationCutoff]

theorem lowPotential_numeric :
    (80 : ℝ) * localizationCutoff ^ 2 / comparisonOrder < 1 / 1200000 := by
  norm_num [localizationCutoff, comparisonOrder]

theorem energyTail_numeric :
    (80 : ℝ) / (localizationCutoff + 1) < 1 / 800000 := by
  norm_num [localizationCutoff]

theorem lowEnergy_numeric :
    (320 : ℝ) * localizationCutoff ^ 2 / comparisonOrder < 1 / 800000 := by
  norm_num [localizationCutoff, comparisonOrder]

def finitePotentialLow {m : ℕ} (q : Fin (2 * m) → ℝ) (j : Fin (2 * m)) : ℂ :=
  ∑ p ∈ lowFrequencies (2 * m) (2 * localizationCutoff), finiteTerm q j p

def continuousPotentialLow {m : ℕ} (q : Fin (2 * m) → ℝ) (j : Fin (2 * m)) : ℂ :=
  ∑ k ∈ signedCutoff localizationCutoff,
    stepTerm q (profileScale (2 * m)) (cellMidpoint (2 * m) j) k

theorem explicit_finite_potential_tail {m : ℕ}
    (hn : comparisonOrder ≤ 2 * m) (hm : 0 < m)
    (q : Fin (2 * m) → ℝ) (hq : q ∈ Q hm) (j : Fin (2 * m)) :
    ‖(operator (2 * m) q j : ℂ) - finitePotentialLow q j‖ <
        1 / 1200000 := by
  unfold finitePotentialLow
  have hnP : 4 * localizationCutoff < 2 * m := by
    have hPc := four_cutoff_lt_order
    omega
  have hb (i : Fin (2 * m)) : |q i| ≤ 4 :=
    (hq.2 i).trans (WholeBoxObjective.amplitude_le_four (by omega))
  have hmass := meanSquare_le_of_bound (by omega : 0 < 2 * m) q
    (by norm_num : (0 : ℝ) ≤ 4) hb
  have hmass16 : meanSquare q ≤ (16 : ℝ) := by
    norm_num at hmass ⊢
    exact hmass
  have ht := midpoint_lowFrequency_error (P := 2 * localizationCutoff) (by omega)
    (even_two_mul m) q j
  apply (sq_lt_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 1200000)).mp
  apply lt_of_le_of_lt (ht.trans (mul_le_mul_of_nonneg_left hmass (by positivity)))
  calc
    8 / ((2 * localizationCutoff : ℕ) + 1 : ℝ) * 4 ^ 2 =
        128 / (2 * localizationCutoff + 1) := by push_cast; ring
    _ < (1 / 1200000 : ℝ) ^ 2 := finitePotentialTail_numeric

theorem explicit_continuous_potential_tail {m : ℕ} (hm : 0 < m)
    (q : Fin (2 * m) → ℝ) (hq : q ∈ Q hm) (j : Fin (2 * m)) :
    ‖(continuousPotential q (profileScale (2 * m)) (cellMidpoint (2 * m) j) : ℂ) -
      continuousPotentialLow q j‖ <
          1 / 1200000 := by
  unfold continuousPotentialLow
  have hb (i : Fin (2 * m)) : |q i| ≤ 4 :=
    (hq.2 i).trans (WholeBoxObjective.amplitude_le_four (by omega))
  have hscale := profileScale_bounds (show 2 ≤ 2 * m by omega)
  have hscaleAbs : |profileScale (2 * m)| ≤ 1 := by
    rw [abs_of_pos hscale.1]
    exact hscale.2.1
  have ht := continuous_tail_sq_le hm q hq.1
    (by norm_num : (0 : ℝ) ≤ 4) (by norm_num : (0 : ℝ) ≤ 1)
    hb hscaleAbs (cellMidpoint (2 * m) j) localizationCutoff
  have htail := tailMass_signedCutoff_le localizationCutoff
    ((by norm_num : 1 ≤ 20).trans cutoff_ge_twenty)
  apply (sq_lt_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 1200000)).mp
  apply lt_of_le_of_lt ht
  apply lt_of_le_of_lt
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left htail (by norm_num : (0 : ℝ) ≤ 4))
      (sq_nonneg ((1 : ℝ) * 4))
  · calc
      4 * (1 / (4 * ((localizationCutoff : ℝ) + 1))) * ((1 : ℝ) * 4) ^ 2 =
          16 / (localizationCutoff + 1) := by field_simp; ring
      _ < (1 / 1200000 : ℝ) ^ 2 := continuousPotentialTail_numeric

theorem explicit_low_potential_difference {m : ℕ}
    (hn : comparisonOrder ≤ 2 * m) (hm : 0 < m)
    (q : Fin (2 * m) → ℝ) (hq : q ∈ Q hm) (j : Fin (2 * m)) :
    ‖finitePotentialLow q j - continuousPotentialLow q j‖ <
          1 / 1200000 := by
  unfold finitePotentialLow continuousPotentialLow
  have hnP : 4 * localizationCutoff < 2 * m := by
    have hPc := four_cutoff_lt_order
    omega
  have hb (i : Fin (2 * m)) : |q i| ≤ 4 :=
    (hq.2 i).trans (WholeBoxObjective.amplitude_le_four (by omega))
  have ht := low_difference_le hnP (even_two_mul m) q
    (by norm_num : (0 : ℝ) ≤ 4) hb (profileScale (2 * m)) j
  have hsum : ∑ k ∈ Finset.range localizationCutoff,
      multiplierError (2 * m) (profileScale (2 * m)) k ≤
      (localizationCutoff : ℝ) *
        (10 * localizationCutoff / (2 * m : ℝ)) := by
    calc
      _ ≤ ∑ _k ∈ Finset.range localizationCutoff,
          (10 : ℝ) * localizationCutoff / (2 * m : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using
          multiplierError_explicit hn (Finset.mem_range.mp hk)
      _ = (localizationCutoff : ℝ) *
          (10 * localizationCutoff / (2 * m : ℝ)) := by simp
  apply lt_of_le_of_lt (ht.trans
    (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2 * 4)))
  have hnR0 : (comparisonOrder : ℝ) ≤ ((2 * m : ℕ) : ℝ) := Nat.cast_le.mpr hn
  have hnR : (comparisonOrder : ℝ) ≤ (2 * m : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hnR0
  calc
    (2 : ℝ) * 4 * ((localizationCutoff : ℝ) *
        (10 * localizationCutoff / (2 * m : ℝ))) =
        80 * (localizationCutoff : ℝ) ^ 2 / (2 * m : ℝ) := by ring
    _ ≤ 80 * (localizationCutoff : ℝ) ^ 2 / comparisonOrder := by
      apply div_le_div_of_nonneg_left
        (mul_nonneg (by norm_num) (sq_nonneg _))
        (Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_two comparisonOrder_ge_two))
      exact hnR
    _ < 1 / 1200000 := lowPotential_numeric

private theorem norm_sub_lt_of_three_steps {a b c d : ℂ}
    (hab : ‖a - b‖ < 1 / 1200000)
    (hbc : ‖b - c‖ < 1 / 1200000)
    (hcd : ‖c - d‖ < 1 / 1200000) :
    ‖a - d‖ < 1 / 400000 := by
  have he : a - d = (a - b) + (b - c) + (c - d) := by ring
  rw [he]
  calc
    ‖(a - b) + (b - c) + (c - d)‖
        ≤ ‖(a - b) + (b - c)‖ + ‖c - d‖ := norm_add_le _ _
    _ ≤ (‖a - b‖ + ‖b - c‖) + ‖c - d‖ := by
      have h := add_le_add_right (norm_add_le (a - b) (b - c)) ‖c - d‖
      simpa only [add_comm] using h
    _ < 1 / 400000 := by linarith

/-- Complex-norm form of the explicit potential comparison. -/
theorem explicit_normalized_potential_comparison_norm {m : ℕ}
    (hn : comparisonOrder ≤ 2 * m) (hm : 0 < m)
    (q : Fin (2 * m) → ℝ) (hq : q ∈ Q hm) (j : Fin (2 * m)) :
    ‖(operator (2 * m) q j : ℂ) -
      (continuousPotential q (profileScale (2 * m)) (cellMidpoint (2 * m) j) : ℂ)‖ <
        1 / 400000 := by
  have hd : ‖(operator (2 * m) q j : ℂ) - finitePotentialLow q j‖ < 1 / 1200000 :=
    explicit_finite_potential_tail hn hm q hq j
  have hc : ‖(continuousPotential q (profileScale (2 * m))
      (cellMidpoint (2 * m) j) : ℂ) - continuousPotentialLow q j‖ < 1 / 1200000 :=
    explicit_continuous_potential_tail hm q hq j
  have hlow : ‖finitePotentialLow q j - continuousPotentialLow q j‖ < 1 / 1200000 :=
    explicit_low_potential_difference hn hm q hq j
  have hc' : ‖continuousPotentialLow q j -
      (continuousPotential q (profileScale (2 * m)) (cellMidpoint (2 * m) j) : ℂ)‖ <
        1 / 1200000 := by
    rw [norm_sub_rev]
    exact hc
  exact norm_sub_lt_of_three_steps
    (a := (operator (2 * m) q j : ℂ)) (b := finitePotentialLow q j)
    (c := continuousPotentialLow q j)
    (d := (continuousPotential q (profileScale (2 * m))
      (cellMidpoint (2 * m) j) : ℂ)) hd hlow hc'

/-- Explicit potential half of the normalized grid comparison. -/
theorem explicit_normalized_potential_comparison {m : ℕ}
    (hn : comparisonOrder ≤ 2 * m) (hm : 0 < m)
    (q : Fin (2 * m) → ℝ) (hq : q ∈ Q hm) (j : Fin (2 * m)) :
    |operator (2 * m) q j -
      continuousPotential q (profileScale (2 * m)) (cellMidpoint (2 * m) j)| <
        1 / 400000 := by
  simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using
    explicit_normalized_potential_comparison_norm hn hm q hq j

/-- The finite Fourier tail is explicit at the fixed cutoff `2^50`. -/
theorem explicit_finite_energy_tail {m : ℕ} (hm : 0 < m)
    (q : Fin (2 * m) → ℝ) (hq : q ∈ Q hm) :
    0 ≤ normalizedBoxEnergy (operator (2 * m)) q -
        partialEnergy q (lowFrequencies (2 * m) (2 * localizationCutoff)) ∧
    normalizedBoxEnergy (operator (2 * m)) q -
        partialEnergy q (lowFrequencies (2 * m) (2 * localizationCutoff)) ≤
      16 / ((localizationCutoff : ℝ) + 1) := by
  have hb (i : Fin (2 * m)) : |q i| ≤ 4 :=
    (hq.2 i).trans (WholeBoxObjective.amplitude_le_four (by omega))
  have hmass := meanSquare_le_of_bound (by omega : 0 < 2 * m) q
    (by norm_num : (0 : ℝ) ≤ 4) hb
  have hmass16 : meanSquare q ≤ (16 : ℝ) := by
    norm_num at hmass ⊢
    exact hmass
  have ht := energy_lowFrequency_error (P := 2 * localizationCutoff)
    (by omega : 0 < 2 * m) (even_two_mul m) q
  refine ⟨ht.1, ht.2.trans ?_⟩
  calc
    meanSquare q / (((2 * localizationCutoff : ℕ) : ℝ) + 1)
        ≤ 16 / (((2 * localizationCutoff : ℕ) : ℝ) + 1) := by
      exact div_le_div_of_nonneg_right hmass16 (by positivity)
    _ ≤ 16 / ((localizationCutoff : ℝ) + 1) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      push_cast
      linarith

/-- The continuous odd-energy tail is explicit at the fixed cutoff `2^50`. -/
theorem explicit_continuous_energy_tail {m : ℕ} (hm : 0 < m)
    (q : Fin (2 * m) → ℝ) (hq : q ∈ Q hm) :
    0 ≤ continuousEnergy q (profileScale (2 * m)) -
        ∑ k ∈ Finset.range localizationCutoff,
          energyTerm q (profileScale (2 * m)) k ∧
    continuousEnergy q (profileScale (2 * m)) -
        ∑ k ∈ Finset.range localizationCutoff,
          energyTerm q (profileScale (2 * m)) k ≤
      16 / ((localizationCutoff : ℝ) + 1) := by
  have hb (i : Fin (2 * m)) : |q i| ≤ 4 :=
    (hq.2 i).trans (WholeBoxObjective.amplitude_le_four (by omega))
  have hmass := meanSquare_le_of_bound (by omega : 0 < 2 * m) q
    (by norm_num : (0 : ℝ) ≤ 4) hb
  have hmass16 : meanSquare q ≤ (16 : ℝ) := by
    norm_num at hmass ⊢
    exact hmass
  have hs := profileScale_bounds (show 2 ≤ 2 * m by omega)
  have hs2 : profileScale (2 * m) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (profileScale (2 * m))]
  have ht := continuousEnergy_tail (P := localizationCutoff)
    (by omega : 0 < 2 * m) q (profileScale (2 * m))
  refine ⟨ht.1, ht.2.trans ?_⟩
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    profileScale (2 * m) ^ 2 * meanSquare q
        ≤ 1 * 16 := by
      exact mul_le_mul hs2 hmass16 (meanSquare_nonneg q) (by norm_num)
    _ = 16 := by ring

/-- The retained finite and continuous energy sums differ explicitly. -/
theorem explicit_low_energy_difference {m : ℕ}
    (hn : comparisonOrder ≤ 2 * m) (hm : 0 < m)
    (q : Fin (2 * m) → ℝ) (hq : q ∈ Q hm) :
    |partialEnergy q (lowFrequencies (2 * m) (2 * localizationCutoff)) -
      ∑ k ∈ Finset.range localizationCutoff,
        energyTerm q (profileScale (2 * m)) k| < 1 / 800000 := by
  have hnP : 4 * localizationCutoff < 2 * m := by
    have hPc := four_cutoff_lt_order
    omega
  have hb (i : Fin (2 * m)) : |q i| ≤ 4 :=
    (hq.2 i).trans (WholeBoxObjective.amplitude_le_four (by omega))
  have ht := low_energy_difference_le hnP (even_two_mul m) q
    (by norm_num : (0 : ℝ) ≤ 4) hb (profileScale (2 * m))
  have hsum : ∑ k ∈ Finset.range localizationCutoff,
      energyMultiplierError (2 * m) (profileScale (2 * m)) k ≤
      (localizationCutoff : ℝ) *
        (20 * localizationCutoff / (2 * m : ℝ)) := by
    calc
      _ ≤ ∑ _k ∈ Finset.range localizationCutoff,
          (20 : ℝ) * localizationCutoff / (2 * m : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using
          energyMultiplierError_explicit hn (Finset.mem_range.mp hk)
      _ = (localizationCutoff : ℝ) *
          (20 * localizationCutoff / (2 * m : ℝ)) := by simp
  apply lt_of_le_of_lt (ht.trans
    (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 4 ^ 2)))
  have hnR0 : (comparisonOrder : ℝ) ≤ ((2 * m : ℕ) : ℝ) := Nat.cast_le.mpr hn
  have hnR : (comparisonOrder : ℝ) ≤ (2 * m : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hnR0
  calc
    (4 : ℝ) ^ 2 * ((localizationCutoff : ℝ) *
        (20 * localizationCutoff / (2 * m : ℝ))) =
        320 * (localizationCutoff : ℝ) ^ 2 / (2 * m : ℝ) := by ring
    _ ≤ 320 * (localizationCutoff : ℝ) ^ 2 / comparisonOrder := by
      apply div_le_div_of_nonneg_left
        (mul_nonneg (by norm_num) (sq_nonneg _))
        (Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_two comparisonOrder_ge_two))
      exact hnR
    _ < 1 / 800000 := lowEnergy_numeric

/-- Explicit energy half of the normalized grid comparison. -/
theorem explicit_normalized_energy_comparison {m : ℕ}
    (hn : comparisonOrder ≤ 2 * m) (hm : 0 < m)
    (q : Fin (2 * m) → ℝ) (hq : q ∈ Q hm) :
    |normalizedBoxEnergy (operator (2 * m)) q -
      continuousEnergy q (profileScale (2 * m))| < 1 / 400000 := by
  let D := partialEnergy q (lowFrequencies (2 * m) (2 * localizationCutoff))
  let C := ∑ k ∈ Finset.range localizationCutoff,
    energyTerm q (profileScale (2 * m)) k
  have hf := explicit_finite_energy_tail hm q hq
  have hc := explicit_continuous_energy_tail hm q hq
  have hl : |D - C| < 1 / 800000 := explicit_low_energy_difference hn hm q hq
  have hfd : |normalizedBoxEnergy (operator (2 * m)) q - D| ≤
      16 / ((localizationCutoff : ℝ) + 1) := by
    rw [abs_of_nonneg hf.1]
    exact hf.2
  have hcd : |C - continuousEnergy q (profileScale (2 * m))| ≤
      16 / ((localizationCutoff : ℝ) + 1) := by
    rw [abs_sub_comm, abs_of_nonneg hc.1]
    exact hc.2
  have htail : 16 / ((localizationCutoff : ℝ) + 1) +
      16 / ((localizationCutoff : ℝ) + 1) < 1 / 800000 := by
    have hp : (0 : ℝ) ≤ 1 / ((localizationCutoff : ℝ) + 1) := by positivity
    have hle : 16 / ((localizationCutoff : ℝ) + 1) +
        16 / ((localizationCutoff : ℝ) + 1) ≤
        80 / ((localizationCutoff : ℝ) + 1) := by
      calc
        _ = 32 / ((localizationCutoff : ℝ) + 1) := by ring
        _ ≤ 80 / ((localizationCutoff : ℝ) + 1) :=
          div_le_div_of_nonneg_right (by norm_num) (by positivity)
    exact hle.trans_lt energyTail_numeric
  have htri := abs_sub_le (normalizedBoxEnergy (operator (2 * m)) q) D
    (continuousEnergy q (profileScale (2 * m)))
  have htri2 := abs_sub_le D C (continuousEnergy q (profileScale (2 * m)))
  linarith

end
end StructuralNote.ExplicitKernelLocalization
