import StructuralNote.FixedDualClassificationTrialLowerBound
import StructuralNote.ExplicitKernelRate

/-! A concrete finite-grid lower bound from the nine-term third-wave trial. -/
namespace StructuralNote.ExplicitKernelTrial

open Real Complex Erdos1045.EventualExact
open FixedDualClassificationStep FixedDualClassificationCoefficientBound
open FixedDualClassificationTrialAverages
open FixedDualClassificationTrialCoefficients
open FixedDualClassificationTrialPartialEnergy
open FixedDualClassificationTrialLowerBound
open ExplicitKernelRate
open scoped BigOperators

noncomputable section

private theorem term_lower {n k : ℕ} (hn : 2 ^ 200 ≤ n) (hk : k < 9) :
    (1 / (6 * (k : ℝ) + 4)) *
          ‖coefficient trial (3 * (2 * k + 1))‖ ^ 2 - 2500 / n ≤
      SchurWeights.weight n (3 * (2 * k + 1)) *
        ‖signedMidpointCoefficient (cellAverage trial n)
          (3 * (2 * k + 1))‖ ^ 2 := by
  have hn0 : 0 < n := by
    have : 0 < 2 ^ 200 := pow_pos (by omega) _
    omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hn408 : (408 : ℝ) ≤ n := by
    exact_mod_cast (show 408 ≤ n by
      have hsmall : 408 ≤ 2 ^ 200 := by norm_num
      omega)
  have hsize : 8 * (3 * (2 * k + 1) + 1) ≤ n := by
    have hsmall : 8 * (3 * (2 * 8 + 1) + 1) ≤ 2 ^ 200 := by norm_num
    omega
  have hw := weight_error_le
    (n := n) (p := 3 * (2 * k + 1)) ⟨3 * k + 1, by omega⟩ (by omega) hsize
  have hqeq : (1 : ℝ) / ((3 * (2 * k + 1) : ℕ) + 1) =
      1 / (6 * (k : ℝ) + 4) := by
    push_cast
    ring
  rw [hqeq] at hw
  have hc0 := cellAverage_coefficient_error hn0 trial_measurable
    (by positivity : 0 ≤ Real.pi / 2) trial_bound
    ((3 * (2 * k + 1) : ℕ) : ℤ)
  have hp : (((3 * (2 * k + 1) : ℕ) : ℤ) : ℝ) = 6 * (k : ℝ) + 3 := by
    push_cast
    ring
  have hc : ‖signedMidpointCoefficient (cellAverage trial n)
      (3 * (2 * k + 1)) - coefficient trial (3 * (2 * k + 1))‖ ≤
      408 / n := by
    apply hc0.trans
    rw [hp, abs_of_pos (by positivity : (0 : ℝ) < 6 * k + 3)]
    apply div_le_div_of_nonneg_right _ hnR.le
    have hkR : (k : ℝ) ≤ 8 := by exact_mod_cast (show k ≤ 8 by omega)
    have hpi := Real.pi_lt_four.le
    calc
      Real.pi / 2 * (6 * (k : ℝ) + 3) * Real.pi ≤
          4 / 2 * (6 * 8 + 3) * 4 := by gcongr
      _ = 408 := by norm_num
  let a := ‖signedMidpointCoefficient (cellAverage trial n)
    (3 * (2 * k + 1))‖
  let b := ‖coefficient trial (3 * (2 * k + 1))‖
  let w := SchurWeights.weight n (3 * (2 * k + 1))
  let q : ℝ := 1 / (6 * (k : ℝ) + 4)
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hw0 : 0 ≤ w := SchurWeights.weight_nonneg _ _
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := by
    dsimp [q]
    exact (div_le_one (by positivity)).2 (by
      have := Nat.cast_nonneg (α := ℝ) k
      linarith)
  have hb1 : b ≤ 1 := by
    dsimp [b]
    rw [trial_coefficient_norm]
    exact (div_le_one (by positivity)).2 (by
      have := Nat.cast_nonneg (α := ℝ) k
      linarith)
  have he1 : 408 / (n : ℝ) ≤ 1 := by
    exact (div_le_one hnR).mpr hn408
  have hab : |a - b| ≤ 408 / n := by
    dsimp [a, b]
    exact (abs_norm_sub_norm_le _ _).trans hc
  have ha2 : a ≤ 2 := by
    have hatri : a ≤
        ‖signedMidpointCoefficient (cellAverage trial n) (3 * (2 * k + 1)) -
          coefficient trial (3 * (2 * k + 1))‖ + b := by
      dsimp [a, b]
      simpa only [sub_add_cancel] using norm_add_le
        (signedMidpointCoefficient (cellAverage trial n) (3 * (2 * k + 1)) -
          coefficient trial (3 * (2 * k + 1)))
        (coefficient trial (3 * (2 * k + 1)))
    linarith only [hatri, hc, he1, hb1]
  have hsquare : |a ^ 2 - b ^ 2| ≤ 1224 / n := by
    rw [show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring, abs_mul,
      abs_of_nonneg (add_nonneg ha0 hb0)]
    calc
      |a - b| * (a + b) ≤ (408 / n) * 3 := by
        gcongr
        linarith only [ha2, hb1]
      _ = 1224 / n := by ring
  have hw2 : w ≤ 2 := by
    have hupper := (abs_le.mp hw).2
    dsimp [w, q] at hupper ⊢
    have h36 : 36 / (n : ℝ) ≤ 1 := by
      apply (div_le_one hnR).mpr
      linarith only [hn408]
    linarith only [hupper, hq1, h36]
  have hdiff : q * b ^ 2 - w * a ^ 2 ≤ 2500 / n := by
    calc
      q * b ^ 2 - w * a ^ 2 = (q - w) * b ^ 2 + w * (b ^ 2 - a ^ 2) := by ring
      _ ≤ |q - w| * b ^ 2 + w * |b ^ 2 - a ^ 2| := by
        gcongr
        · exact le_abs_self _
        · exact le_abs_self _
      _ ≤ (36 / n) * 1 + 2 * (1224 / n) := by
        have hw' : |q - w| ≤ 36 / n := by
          rw [abs_sub_comm]
          simpa only [w, q] using hw
        have hsquare' : |b ^ 2 - a ^ 2| ≤ 1224 / n := by
          rw [abs_sub_comm]
          exact hsquare
        gcongr
        nlinarith only [hb0, hb1]
      _ ≤ 2500 / n := by
        rw [show 36 / (n : ℝ) * 1 + 2 * (1224 / n) = 2484 / n by ring]
        exact div_le_div_of_nonneg_right (by norm_num) hnR.le
  dsimp [a, b, w, q] at hdiff
  linarith only [hdiff]

theorem explicit_B_fixed_gap {m : ℕ} (hn : 2 ^ 200 ≤ 2 * m) (hm : 0 < m) :
    (531 : ℝ) / 2000 + 1 / 100000 ≤ FiniteBox.B hm := by
  have hn0 : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hsum : thirdLimit trial 9 - 9 * (2500 / (2 * m : ℝ)) ≤
      thirdPartial trial (2 * m) 9 := by
    unfold thirdLimit thirdPartial
    calc
      _ = ∑ k ∈ Finset.range 9,
          ((1 / (6 * (k : ℝ) + 4)) *
            ‖coefficient trial (3 * (2 * k + 1))‖ ^ 2 - 2500 / (2 * m : ℝ)) := by
        rw [Finset.sum_sub_distrib]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        norm_num
      _ ≤ _ := Finset.sum_le_sum fun k hk => by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using
          term_lower hn (Finset.mem_range.mp hk)
  have hsmall : 9 * (2500 / (2 * m : ℝ)) ≤
      thirdLimit trial 9 - ((531 : ℝ) / 2000 + 1 / 100000) := by
    rw [thirdLimit_nine]
    have hcast : (2 ^ 200 : ℝ) ≤ 2 * m := by exact_mod_cast hn
    have herr : 9 * (2500 / (2 * m : ℝ)) ≤ 9 * (2500 / (2 ^ 200 : ℝ)) := by
      gcongr
    apply herr.trans
    norm_num
  have htrial : (531 : ℝ) / 2000 + 1 / 100000 ≤ thirdPartial trial (2 * m) 9 := by
    linarith only [hsum, hsmall]
  exact htrial.trans (thirdPartial_le_B hm (by
    have hsmall : 12 * 9 < 2 ^ 200 := by norm_num
    omega) trial trial_bound)

end
end StructuralNote.ExplicitKernelTrial
