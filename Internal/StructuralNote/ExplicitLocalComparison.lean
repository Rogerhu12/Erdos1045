import StructuralNote.ExplicitComparisonNormal
import StructuralNote.ExplicitComparisonRemainder
import StructuralNote.FixedSchurLocalComparison

/-! The common-parameter objective comparison with explicit thresholds. -/
namespace StructuralNote.ExplicitLocalComparison
open scoped BigOperators Topology
open Complex Erdos1045.EventualExact FiniteBox FourierMultiplier SchurSpectrum SchurLiftBounds
open CommonClosureEnergy CommonDomainClosure FixedSchurChart FixedSchurObjective
open FixedSchurDomainSmallness FixedSchurInnerAngles FixedSchurNearWordAngular
open FixedSchurLocalQuadratic FixedSchurInnerRemainder FixedDualClassificationFinite SolWordHamming
open FixedSchurComparisonScales FixedSchurLocalComparison
noncomputable section

def orderThreshold (B : ℝ) : ℕ := max (ExplicitComparisonNormal.orderThreshold B)
  (ExplicitComparisonRemainder.orderThreshold B)

def nearThreshold (B C : ℝ) : ℕ := max (orderThreshold B)
  (ExplicitComparisonScalars.angularThreshold C)

theorem local_comparison (B : ℝ) (hB : 0 ≤ B) (s₀ : ℕ) {m : ℕ} (hN : orderThreshold B ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s t : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      pairEnergy (by omega) (fun j => (θ j : ℂ)) + pairEnergy (by omega) v ≤
        B ^ 2 / (2 * m : ℝ) ^ 2 → hamming s t ≤ s₀ →
      |(F (configuration (by omega) s θ v) - F (configuration (by omega) t θ v)) -
        (normalizedBoxEnergy (operator (2 * m)) (baseWord (patternSign s)) -
          normalizedBoxEnergy (operator (2 * m)) (baseWord (patternSign t))) -
        (∑ j, (signedPotential s j - signedPotential t j) * angleDifference (by omega) θ j) / 2| ≤
        comparisonConstant B (s₀ : ℝ) / ((2 * m : ℝ) ^ 2 * Real.sqrt (2 * m : ℝ)) := by
  have hquad := ExplicitComparisonNormal.actual_quadratic_comparison B hB s₀ ((le_max_left _ _).trans hN)
  have hrem := ExplicitComparisonRemainder.objective_hamming_bound B hB s₀ ((le_max_right _ _).trans hN)
  clear hN
  intro hm s t θ v hdom henergy hham
  have hq := hquad hm s t θ v hdom henergy hham
  have hr := hrem hm s t θ v hdom henergy hham
  have hn : (1 : ℝ) ≤ 2 * m := by exact_mod_cast (show 1 ≤ 2 * m by omega)
  have hq' := hq.trans (inverse_cube_bound hn (quadraticConstant_nonneg hB (Nat.cast_nonneg s₀)))
  have htri (a b c d : ℝ) : |a - c - d| ≤ |a - b| + |b - c - d| := by
    rw [show a - c - d = (a - b) + (b - c - d) by ring]
    exact abs_add_le _ _
  apply (htri _ _ _ _).trans
  exact (add_le_add hr hq').trans_eq (by unfold comparisonConstant; ring)

theorem near_local_comparison (B : ℝ) (hB : 0 ≤ B) (C₀ : ℝ) (s₀ : ℕ) {m : ℕ} (hN : nearThreshold B C₀ ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s t : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      pairEnergy (by omega) (fun j => (θ j : ℂ)) + pairEnergy (by omega) v ≤
        B ^ 2 / (2 * m : ℝ) ^ 2 → hamming s t ≤ s₀ →
      deficit (by omega) s ≤ C₀ / (2 * m : ℝ) ^ 2 →
      deficit (by omega) t ≤ C₀ / (2 * m : ℝ) ^ 2 →
      |(F (configuration (by omega) s θ v) - F (configuration (by omega) t θ v)) -
        (normalizedBoxEnergy (operator (2 * m)) (baseWord (patternSign s)) -
          normalizedBoxEnergy (operator (2 * m)) (baseWord (patternSign t)))| ≤
        nearComparisonConstant B (s₀ : ℝ) / ((2 * m : ℝ) ^ 2 * Real.sqrt (2 * m : ℝ)) := by
  have hcompare := local_comparison B hB s₀ ((le_max_left _ _).trans hN)
  have hang := ExplicitComparisonScalars.near_angular_bound ((le_max_right _ _).trans hN)
  clear hN
  intro hm s t θ v hdom henergy hham hs ht
  have hmain := hcompare hm s t θ v hdom henergy hham
  have ha := hang (by omega) s t (angleDifference (by omega) θ) hs ht
  have hmoment := angleDifference_meanSquare_le_of_joint_energy (by omega) θ v hB hdom henergy
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hroot := angle_l2_bound hn hB hmoment
  have hh : (hamming s t : ℝ) ≤ s₀ := by exact_mod_cast hham
  have hab : |(∑ j, (signedPotential s j - signedPotential t j) * angleDifference (by omega) θ j) / 2| ≤
      (24 * Real.pi * B * (s₀ : ℝ)) / ((2 * m : ℝ) ^ 2 * Real.sqrt (2 * m : ℝ)) := by
    apply ha.trans
    calc
      _ ≤ 6 * (s₀ : ℝ) * (4 * Real.pi * B / ((2 * m : ℝ) ^ 2 * Real.sqrt (2 * m : ℝ))) := by gcongr
      _ = _ := by ring
  have htri (a b : ℝ) : |a| ≤ |a - b| + |b| := by
    simpa only [sub_add_cancel] using abs_add_le (a - b) b
  apply (htri _ _).trans
  exact (add_le_add hmain hab).trans_eq (by unfold nearComparisonConstant; ring)

end
end StructuralNote.ExplicitLocalComparison
