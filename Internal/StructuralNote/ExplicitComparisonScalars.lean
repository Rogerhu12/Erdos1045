import StructuralNote.ExplicitHessianThreshold
import StructuralNote.ExplicitPressureThreshold
import StructuralNote.FixedSchurNearWordAngular
import StructuralNote.FixedSchurNormalInnerBound

/-! Closed scalar bounds shared by the fixed-Schur comparison estimates. -/

namespace StructuralNote.ExplicitComparisonScalars

open Erdos1045 Erdos1045.EventualExact Complex
open Erdos1045.ExplicitThreshold ExplicitHessianThreshold
open CommonDomainRadius CommonDomainClosure CommonFiberBounds CommonClosureEnergy
open FixedSchurChartRadial FixedSchurDomainBounds FixedSchurNormalExpansion
open FixedSchurNearWordAngular FixedDualClassificationFinite SolWordHamming
open FiniteBox FourierMultiplier SchurLiftBounds
noncomputable section

theorem small_coefficients {n : ℕ} (hn : orderThreshold ≤ n) :
    16 ≤ n ∧ 10 * (CommonDomainRadius.logOrder n : ℝ) + 1024 ≤ n ∧
      4 * (CommonDomainRadius.logOrder n : ℝ) * Real.sqrt (Real.log n) / (n : ℝ) ^ 2 ≤ 1 / (1000 * n) ∧
      (10 * (CommonDomainRadius.logOrder n : ℝ) + 1049) / (n : ℝ) ^ 2 ≤ 1 / (1000 * n) := by
  have hn0 := order_pos hn
  have hH := logBudget_ge_one hn
  have hL := logOrder_bound hn
  have hsqrt : Real.sqrt (Real.log (n : ℝ)) ≤ logBudget n := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · linarith only [hH]
    · unfold logBudget at hH ⊢
      nlinarith only [hH, sq_nonneg (Real.log (n : ℝ))]
  have hp : 4 * (CommonDomainRadius.logOrder n : ℝ) * Real.sqrt (Real.log n) ≤ 8 * logBudget n ^ 2 := by
    calc
      _ ≤ 4 * (2 * logBudget n) * logBudget n := by
        gcongr
      _ = _ := by ring
  have hq : 10 * (CommonDomainRadius.logOrder n : ℝ) + 1049 ≤ 1069 * logBudget n := by
    linarith only [hL, hH]
  have h₁ := log_monomial_div_small (j := 2) (c := 8) hn (by norm_num) (by norm_num)
  have h₂ := log_monomial_div_small (j := 1) (c := 1069) hn (by norm_num) (by norm_num)
  simp only [pow_one] at h₂
  have hscale (A C : ℝ) (hAC : A ≤ C) (hC : C / n ≤ 1 / 1000) :
      A / (n : ℝ) ^ 2 ≤ 1 / (1000 * n) := by
    calc
      _ ≤ C / (n : ℝ) ^ 2 := div_le_div_of_nonneg_right hAC (sq_nonneg _)
      _ = (C / n) / n := by ring
      _ ≤ (1 / 1000 : ℝ) / n := div_le_div_of_nonneg_right hC hn0.le
      _ = _ := by ring
  refine ⟨by have := two_fifty_six_le_order hn; omega, order_bound hn, ?_, ?_⟩
  · exact hscale _ _ hp (by linarith only [h₁])
  · exact hscale _ _ hq (by linarith only [h₂])

theorem inner_angle_sup {m : ℕ} (hn : orderThreshold ≤ 2 * m) (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (hdom : InDomain (by omega) θ v) :
    (∀ j, |angleAverage (by omega) θ j| ≤ 1 / (1000 * (2 * m : ℝ))) ∧
    (∀ j, |angleDifference (by omega) θ j| ≤ 1 / (1000 * (2 * m : ℝ))) := by
  have hs := small_coefficients hn
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hs
  constructor
  · exact fun j => (domain_angleAverage_bound_all (by omega) θ v hdom j).trans hs.2.2.1
  · intro j
    apply (domain_angle_difference (by omega) θ v hdom j).trans
    apply le_trans ?_ hs.2.2.2
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    linarith

def angularThreshold (C : ℝ) : ℕ :=
  max 2048 (ExplicitPressureThreshold.signThreshold C (|C| + 1))

theorem near_angular_bound {m : ℕ} {C : ℝ} (hn : angularThreshold C ≤ 2 * m)
    (hm : 0 < m) (s t : SignPattern hm) (η : Fin (2 * m) → ℝ)
    (hs : deficit hm s ≤ C / (2 * m : ℝ) ^ 2)
    (ht : deficit hm t ≤ C / (2 * m : ℝ) ^ 2) :
    |(∑ j, (signedPotential s j - signedPotential t j) * η j) / 2| ≤
      6 * (hamming s t : ℝ) * Real.sqrt (meanSquare η) := by
  apply aligned_angular_bound ((le_max_left _ _).trans hn) s t η
  · exact fun j => (ExplicitPressureThreshold.near_maximum_signs ((le_max_right _ _).trans hn) hm s hs j).2
  · exact fun j => (ExplicitPressureThreshold.near_maximum_signs ((le_max_right _ _).trans hn) hm t ht j).2

end
end StructuralNote.ExplicitComparisonScalars
