import StructuralNote.ExplicitComparisonGeometry
import StructuralNote.ExplicitComparisonStability
import StructuralNote.FixedSchurInnerRemainder

/-! Pointwise Hamming estimate for the actual objective remainder. -/
namespace StructuralNote.ExplicitComparisonRemainder
open scoped BigOperators Topology
open Complex Erdos1045 Erdos1045.EventualExact
open SchurSpectrum CommonDomainClosure FixedSchurChart FixedSchurLinear
open CommonFiberGeometry SignedPressureAngular FixedSchurObjective
open FixedSchurRemainderGeometry FixedSchurInnerSizes FixedSchurChartQuotients
open FixedSchurChartCenterBounds FixedSchurHammingStability SolWordHamming FixedSchurInnerRemainder
open GeometricRelativeRemainder
noncomputable section

def orderThreshold (B : ℝ) : ℕ := max ExplicitHessianThreshold.orderThreshold
  (Erdos1045.ExplicitThreshold.inverseThreshold (30 + 3 * B) (1 / 4))

theorem chosen_inner_sizes (B : ℝ) (hB : 0 ≤ B) {m : ℕ} (hN : orderThreshold B ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
        (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
        InDomain (by omega) θ v →
        pairEnergy (by omega) (fun j => (θ j : ℂ)) +
            pairEnergy (by omega) v ≤ B ^ 2 / (2 * m : ℝ) ^ 2 →
        ‖coordinate (by omega) s θ v‖ ≤ 5 ∧
          (∀ p, ‖quotient (FixedSchurLinear.center (coordinate (by omega) s θ v) v)
              (root (2 * m)) p‖ ≤ (30 + 3 * B) / (2 * m : ℝ)) ∧
          (30 + 3 * B) / (2 * m : ℝ) ≤ 1 / 4 := by
  have hprops := ExplicitHessianThresholdFixedSchur.coordinate_properties ((le_max_left _ _).trans hN)
  have hsmall := Erdos1045.ExplicitThreshold.inverse_small
    (by norm_num : (0 : ℝ) < 1 / 4) ((le_max_right _ _).trans hN)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hsmall
  clear hN
  intro hm s θ v hdom henergy
  have hp := hprops hm s θ v hdom
  have hq := hp.norm_le
  have hquot (p : Fin (2 * m) × Fin (2 * m)) :=
    center_chord_quotient_le_of_joint_energy hm θ v hB hdom henergy
      (coordinate (by omega) s θ v) hq p
  exact ⟨hq, hquot, hsmall.le⟩


private theorem sqrt_angular_bound {A B n : ℝ} (hB : 0 ≤ B) (hn : 0 < n)
    (hA : A ≤ 6 * B ^ 2 / n ^ 2) : Real.sqrt A ≤ 3 * B / n := by
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity, ?_⟩
  apply hA.trans
  calc
    6 * B ^ 2 / n ^ 2 ≤ 9 * B ^ 2 / n ^ 2 := by gcongr; norm_num
    _ = _ := by ring

theorem remainder_energy_bound (B : ℝ) (hB : 0 ≤ B) {m : ℕ} (hN : orderThreshold B ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s t : FiniteBox.SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      pairEnergy (by omega) (fun j => (θ j : ℂ)) + pairEnergy (by omega) v ≤
        B ^ 2 / (2 * m : ℝ) ^ 2 →
      |newRemainder (by omega) θ (FixedSchurLinear.center (coordinate (by omega) s θ v) v) -
        newRemainder (by omega) θ (FixedSchurLinear.center (coordinate (by omega) t θ v) v)| ≤
        coefficient B / (2 * m : ℝ) ^ 2 *
          Real.sqrt (pairEnergy (by omega)
            (FixedSchurLinear.center (coordinate (by omega) s θ v) v -
              FixedSchurLinear.center (coordinate (by omega) t θ v) v)) := by
  have hinner := chosen_inner_sizes B hB hN
  have hprops := ExplicitHessianThresholdFixedSchur.coordinate_properties ((le_max_left _ _).trans hN)
  have hquot := ExplicitComparisonGeometry.quotient_properties ((le_max_left _ _).trans hN)
  have hcenter := ExplicitComparisonGeometry.center_bounds ((le_max_left _ _).trans hN)
  clear hN
  intro hm s t θ v hdom henergy
  let C := FixedSchurLinear.center (coordinate (by omega) s θ v) v
  let C' := FixedSchurLinear.center (coordinate (by omega) t θ v) v
  have hs := hinner hm s θ v hdom henergy
  have ht := hinner hm t θ v hdom henergy
  have hqs := hquot hm s θ v hdom
  have hqt := hquot hm t θ v hdom
  have hc : HalfPeriodic (by omega) C := FixedSchurLinear.center_halfPeriodic hm _ _
    (hprops hm s θ v hdom).antiperiodic hdom.2.2.1.1
  have hc' : HalfPeriodic (by omega) C' := FixedSchurLinear.center_halfPeriodic hm _ _
    (hprops hm t θ v hdom).antiperiodic hdom.2.2.1.1
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hU : 0 ≤ (30 + 3 * B) / (2 * m : ℝ) := by positivity
  have h := actual_remainder_difference_energy hm θ C C' hdom.1 hc hc' hqs.1
    (fun p => (hqs.2.2.2 p).trans_lt (by norm_num))
    (fun p => (hqt.2.2.2 p).trans_lt (by norm_num)) hU hs.2.2 hs.2.1 ht.2.1 hqs.2.2.1
  have hAC : Real.sqrt (pairEnergy (by omega) C) ≤ 41 := by
    apply (Real.sqrt_le_iff).2
    exact ⟨by norm_num, (hcenter hm s θ v hdom).2.trans (by norm_num)⟩
  have hAC' : Real.sqrt (pairEnergy (by omega) C') ≤ 41 := by
    apply (Real.sqrt_le_iff).2
    exact ⟨by norm_num, (hcenter hm t θ v hdom).2.trans (by norm_num)⟩
  have hAD : Real.sqrt (pairEnergy (by omega) (diameterVector θ - root (2 * m))) ≤
      3 * B / (2 * m : ℝ) :=
    sqrt_angular_bound hB hn (displacement_energy_le_of_joint_energy hm θ v hB hdom henergy)
  apply h.trans
  calc
    _ ≤ 32 * (((30 + 3 * B) / (2 * m : ℝ)) * (3 * B / (2 * m : ℝ)) +
        ((30 + 3 * B) / (2 * m : ℝ)) ^ 2 * (41 + 41)) *
          Real.sqrt (pairEnergy (by omega) (C - C')) := by gcongr
    _ = _ := by unfold coefficient; ring


theorem remainder_hamming_bound (B : ℝ) (hB : 0 ≤ B) (s₀ : ℕ) {m : ℕ} (hN : orderThreshold B ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s t : FiniteBox.SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      pairEnergy (by omega) (fun j => (θ j : ℂ)) + pairEnergy (by omega) v ≤
        B ^ 2 / (2 * m : ℝ) ^ 2 → hamming s t ≤ s₀ →
      |newRemainder (by omega) θ (FixedSchurLinear.center (coordinate (by omega) s θ v) v) -
        newRemainder (by omega) θ (FixedSchurLinear.center (coordinate (by omega) t θ v) v)| ≤
        (coefficient B * Real.sqrt (12800 * (s₀ : ℝ))) /
          ((2 * m : ℝ) ^ 2 * Real.sqrt (2 * m : ℝ)) := by
  have hR := remainder_energy_bound B hB hN
  have hstable := ExplicitComparisonStability.hamming_stability ((le_max_left _ _).trans hN)
  clear hN
  intro hm s t θ v hdom henergy hham
  have h := hR hm s t θ v hdom henergy
  have he := (hstable hm s t θ v hdom).2.2
  have hh : (hamming s t : ℝ) ≤ s₀ := by exact_mod_cast hham
  have he' := he.trans (show 12800 * (hamming s t : ℝ) / (2 * m : ℝ) ≤
      12800 * (s₀ : ℝ) / (2 * m : ℝ) by gcongr)
  have hcoef : 0 ≤ coefficient B / (2 * m : ℝ) ^ 2 :=
    div_nonneg (coefficient_nonneg hB) (sq_nonneg _)
  apply h.trans
  calc
    _ ≤ coefficient B / (2 * m : ℝ) ^ 2 *
        Real.sqrt (12800 * (s₀ : ℝ) / (2 * m : ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt he') hcoef
    _ = _ := by rw [Real.sqrt_div (by positivity)]; ring


theorem objective_hamming_bound (B : ℝ) (hB : 0 ≤ B) (s₀ : ℕ) {m : ℕ} (hN : orderThreshold B ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s t : FiniteBox.SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      pairEnergy (by omega) (fun j => (θ j : ℂ)) + pairEnergy (by omega) v ≤
        B ^ 2 / (2 * m : ℝ) ^ 2 → hamming s t ≤ s₀ →
      |(F (FixedSchurChart.configuration (by omega) s θ v) -
          F (FixedSchurChart.configuration (by omega) t θ v)) -
        (normalizedBoxEnergy (FourierMultiplier.operator (2 * m))
            (coordinate (by omega) s θ v) -
          normalizedBoxEnergy (FourierMultiplier.operator (2 * m))
            (coordinate (by omega) t θ v))| ≤
        (coefficient B * Real.sqrt (12800 * (s₀ : ℝ))) /
          ((2 * m : ℝ) ^ 2 * Real.sqrt (2 * m : ℝ)) := by
  have hrem := remainder_hamming_bound B hB s₀ hN
  have hprops := ExplicitHessianThresholdFixedSchur.coordinate_properties ((le_max_left _ _).trans hN)
  clear hN
  intro hm s t θ v hdom henergy hham
  have hs := exact_split hm θ (coordinate (by omega) s θ v) v
    (hprops hm s θ v hdom).antiperiodic hdom.2.2.1.1 hdom.2.2.1.2.2
  have ht := exact_split hm θ (coordinate (by omega) t θ v) v
    (hprops hm t θ v hdom).antiperiodic hdom.2.2.1.1 hdom.2.2.1.2.2
  have he : (F (FixedSchurChart.configuration (by omega) s θ v) -
          F (FixedSchurChart.configuration (by omega) t θ v)) -
        (normalizedBoxEnergy (FourierMultiplier.operator (2 * m))
            (coordinate (by omega) s θ v) -
          normalizedBoxEnergy (FourierMultiplier.operator (2 * m))
            (coordinate (by omega) t θ v)) =
      newRemainder (by omega) θ (FixedSchurLinear.center (coordinate (by omega) s θ v) v) -
        newRemainder (by omega) θ (FixedSchurLinear.center (coordinate (by omega) t θ v) v) := by
    change F (fun j => FixedSchurEdgeGeometry.vertex θ
        (FixedSchurLinear.center (coordinate (by omega) s θ v) v) j) -
      F (fun j => FixedSchurEdgeGeometry.vertex θ
        (FixedSchurLinear.center (coordinate (by omega) t θ v) v) j) - _ = _
    linarith only [hs, ht]
  rw [he]
  exact hrem hm s t θ v hdom henergy hham



end
end StructuralNote.ExplicitComparisonRemainder
