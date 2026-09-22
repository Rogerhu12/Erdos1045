import StructuralNote.ExplicitKernelLocalization
import StructuralNote.ExplicitKernelTrial
import StructuralNote.ExplicitKernelPhase
import StructuralNote.ExplicitBalancedSelection

/-! Finite Fourier comparison closes the balanced-word selection threshold. -/
namespace StructuralNote.ExplicitKernelSelection
open Real Complex Set
open Erdos1045 Erdos1045.EventualExact Erdos1045.ExplicitThreshold
open FourierMultiplier FiniteBox FixedDualClassificationFinite
open FixedDualClassificationStep FixedDualClassificationStepEnergy
open FixedDualClassificationStepPotential FixedDualClassificationMultiplierLimit
open ExplicitKernelLocalization ExplicitKernelBalanced
noncomputable section

def orderThreshold (C : ℝ) : ℕ :=
  max (2 * wordClassificationThreshold)
    (max comparisonOrder
      (max (inverseThreshold |C| (1 / 400000))
        (ExplicitPressureThreshold.signThreshold C (|C| + 1))))

theorem near_maximum_entry {m : ℕ} {C : ℝ}
    (hn : orderThreshold C ≤ 2 * m) (hm : 0 < m)
    (q : Fin (2 * m) → ℝ) (hq : q ∈ Q hm)
    (hdef : B hm - normalizedBoxEnergy (operator (2 * m)) q ≤ C / (2 * m : ℝ) ^ 2) :
    (531 : ℝ) / 2000 < continuousEnergy q (profileScale (2 * m)) ∧
    (24 : ℝ) / 25 < ‖profileCoefficient (stepProfile q (profileScale (2 * m))) 3‖ ∧
    ∀ j : Fin (2 * m), |operator (2 * m) q j -
      continuousPotential q (profileScale (2 * m)) (cellMidpoint (2 * m) j)| ≤ 1 / 100 := by
  have hcompare : comparisonOrder ≤ 2 * m :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hinverse : inverseThreshold |C| (1 / 400000) ≤ 2 * m :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hn1 : (1 : ℝ) ≤ 2 * m := by exact_mod_cast (show 1 ≤ 2 * m by omega)
  have hn0 : (0 : ℝ) < 2 * m := lt_of_lt_of_le (by norm_num) hn1
  have hinv : |C| / (2 * m : ℝ) < 1 / 400000 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      inverse_small (by norm_num : (0 : ℝ) < 1 / 400000) hinverse
  have hC : C / (2 * m : ℝ) ^ 2 < 1 / 400000 := by
    calc
      _ ≤ |C| / (2 * m : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (le_abs_self C) (sq_nonneg _)
      _ ≤ |C| / (2 * m : ℝ) :=
        div_le_div_of_nonneg_left (abs_nonneg C) hn0 (by nlinarith only [hn1])
      _ < _ := hinv
  have hB := ExplicitKernelTrial.explicit_B_fixed_gap hcompare hm
  have henergy := explicit_normalized_energy_comparison hcompare hm q hq
  have hthreshold : (531 : ℝ) / 2000 < continuousEnergy q (profileScale (2 * m)) := by
    have herr := (abs_lt.mp henergy).2
    linarith only [hB, hdef, hC, herr]
  refine ⟨hthreshold, ThirdSchwarzDefect.normalized_third_sharp hm q hq hthreshold, ?_⟩
  intro j
  exact (explicit_normalized_potential_comparison hcompare hm q hq j).le.trans (by norm_num)

theorem finiteImprovement {m : ℕ} {C : ℝ}
    (hn : orderThreshold C ≤ 2 * m) :
    ExplicitBalancedSelection.FiniteImprovement m C (16 / 25) := by
  intro hm s hdef hnot
  have hword : wordClassificationThreshold ≤ m := by
    have h := (le_max_left _ _).trans hn
    change 2 * wordClassificationThreshold ≤ 2 * m at h
    omega
  have hsign : ExplicitPressureThreshold.signThreshold C (|C| + 1) ≤ 2 * m :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hentry := near_maximum_entry hn hm (vertex (amplitude (2 * m)) s)
    (vertex_mem_box (amplitude_pos (by omega)).le s) hdef
  obtain ⟨α, hα, hlocal⟩ :=
    ExplicitKernelPhase.localization_of_entry hsign hm s hdef hentry.2.1 hentry.2.2
  exact explicit_nonbalanced_improvement_of_raw_localization hword hm s hα hlocal hnot

end
end StructuralNote.ExplicitKernelSelection
