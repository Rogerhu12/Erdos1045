import StructuralNote.ExplicitPressureThreshold
import StructuralNote.FixedDualClassificationExteriorGaps
/-! Explicit localization from the quantitative third coefficient and potential comparison. -/
namespace StructuralNote.ExplicitKernelPhase

open Real Set Filter
open Erdos1045.EventualExact FourierMultiplier FiniteBox
open FixedDualClassificationStep FixedDualClassificationPeriodicStep
open FixedDualClassificationCircleShift FixedDualClassificationPhaseArc
open FixedDualClassificationParseval FixedDualClassificationMultiplierLimit
open FixedDualClassificationStepPotential FixedDualClassificationGridComparison
open FixedDualClassificationFunctional FixedDualClassificationLobeGeometry
open FixedDualClassificationTrialNearMaximum FixedDualClassificationFinite
open FixedDualClassificationZeroArcs SolNearMaximumSigns
open scoped Topology
open Real Set Filter Erdos1045.EventualExact FiniteBox
open FixedDualClassificationStep FixedDualClassificationFinite
open FixedDualClassificationSixArcSigns FixedDualClassificationZeroArcs
open FixedDualClassificationGridPeriodicity FiniteCompressionRanked
open FixedDualClassificationStep FixedDualClassificationZeroArcs
open FixedDualClassificationFinite FixedDualClassificationUnwrappedSigns
open FiniteCompressionRanked

open FixedDualClassificationSixArcSigns FixedDualClassificationExteriorGaps
noncomputable section


theorem signs_by_phase {m : ℕ} {C : ℝ}
    (hn : ExplicitPressureThreshold.signThreshold C (|C| + 1) ≤ 2 * m)
    (hm : 0 < m) (s : SignPattern hm)
    (hdef : deficit hm s ≤ C / (2 * m : ℝ) ^ 2)
    (hthird : (24 : ℝ) / 25 <
      ‖profileCoefficient (stepProfile (vertex (amplitude (2 * m)) s) (profileScale (2 * m))) 3‖)
    (hpotential : ∀ j : Fin (2 * m), |operator (2 * m) (vertex (amplitude (2 * m)) s) j -
      continuousPotential (vertex (amplitude (2 * m)) s) (profileScale (2 * m))
        (cellMidpoint (2 * m) j)| ≤ 1 / 100) :
    ∀ j : Fin (2 * m),
      let φ := thirdPhase
        (circleProfile (vertex (amplitude (2 * m)) s) (profileScale (2 * m)))
        (cellMidpoint (2 * m) j)
      sin (3 / 8 : ℝ) ≤ |cos φ| →
      (1 : ℝ) / 100 < |potential s j| ∧
      patternSign s j = if 0 ≤ cos φ then 1 else -1 := by
  intro j
  dsimp only
  intro haway
  let q := vertex (amplitude (2 * m)) s
  have hq : q ∈ Q hm := vertex_mem_box (amplitude_pos (by omega)).le s
  have hsign := (ExplicitPressureThreshold.near_maximum_signs hn hm s hdef j).2
  have hg := normalized_potential_sign hm q hq hthird.le (cellMidpoint (2 * m) j) haway
  have herr := abs_le.mp (hpotential j)
  change -(1 / 100 : ℝ) ≤ potential s j -
    continuousPotential q (profileScale (2 * m)) (cellMidpoint (2 * m) j) ∧
    potential s j - continuousPotential q (profileScale (2 * m))
      (cellMidpoint (2 * m) j) ≤ 1 / 100 at herr
  by_cases hpos : 0 ≤ cos (thirdPhase (circleProfile q (profileScale (2 * m)))
      (cellMidpoint (2 * m) j))
  · have hp := hg.1 hpos
    have hp' : (1 : ℝ) / 100 < potential s j := by linarith [herr.1]
    have hp0 : 0 < potential s j := by linarith
    rw [abs_of_pos hp0] at hsign ⊢
    refine ⟨hp', ?_⟩
    rw [if_pos hpos]
    rcases patternSign_is_sign s j with hs | hs
    · exact hs
    · rw [hs] at hsign
      nlinarith
  · have hp := hg.2 (le_of_not_ge hpos)
    have hp' : potential s j < -(1 / 100 : ℝ) := by linarith [herr.2]
    have hp0 : potential s j < 0 := by linarith
    rw [abs_of_neg hp0] at hsign ⊢
    refine ⟨by linarith, ?_⟩
    rw [if_neg hpos]
    rcases patternSign_is_sign s j with hs | hs
    · rw [hs] at hsign
      nlinarith
    · exact hs


theorem localization_of_entry {m : ℕ} {C : ℝ}
    (hn : ExplicitPressureThreshold.signThreshold C (|C| + 1) ≤ 2 * m)
    (hm : 0 < m) (s : SignPattern hm)
    (hdef : deficit hm s ≤ C / (2 * m : ℝ) ^ 2)
    (hthird : (24 : ℝ) / 25 <
      ‖profileCoefficient (stepProfile (vertex (amplitude (2 * m)) s) (profileScale (2 * m))) 3‖)
    (hpotential : ∀ j : Fin (2 * m), |operator (2 * m) (vertex (amplitude (2 * m)) s) j -
      continuousPotential (vertex (amplitude (2 * m)) s) (profileScale (2 * m))
        (cellMidpoint (2 * m) j)| ≤ 1 / 100) :
    ∃ α ∈ Icc (-(Real.pi / 3)) (Real.pi / 3), LocalizedSigns hm s α := by
  have h := signs_by_phase hn hm s hdef hthird hpotential
  let F := circleProfile (vertex (amplitude (2 * m)) s) (profileScale (2 * m))
  let α := -(thirdCoefficient F).arg / 3
  have hα : α ∈ Icc (-(Real.pi / 3)) (Real.pi / 3) := by
    constructor
    · dsimp only [α]
      linarith [Complex.arg_le_pi (thirdCoefficient F)]
    · dsimp only [α]
      linarith [Complex.neg_pi_lt_arg (thirdCoefficient F)]
  have hsites : ∀ j : Fin (2 * m),
      (∀ k : ℤ, (1 : ℝ) / 8 ≤ |cellMidpoint (2 * m) j - zeroCenter α k|) →
      patternSign s j = if 0 ≤ cos (3 * (cellMidpoint (2 * m) j - α)) then 1 else -1 := by
    intro j haway
    have hp : thirdPhase F (cellMidpoint (2 * m) j) =
        3 * (cellMidpoint (2 * m) j - α) := by unfold thirdPhase α; ring
    have hout := cosine_away_of_outside_arcs haway
    have hsite := h j
    change sin (3 / 8 : ℝ) ≤ |cos (thirdPhase F (cellMidpoint (2 * m) j))| → _ at hsite
    rw [hp] at hsite
    exact (hsite hout).2
  refine ⟨α, hα, ?_⟩
  intro j haway
  have hsite := hsites (site hm j) (haway_site_of_haway hm j α haway)
  rwa [← cos_third_cellMidpoint_site hm j α] at hsite

end
end StructuralNote.ExplicitKernelPhase
