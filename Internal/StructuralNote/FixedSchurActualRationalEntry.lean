import StructuralNote.FixedSchurActualCanonicalEntry
import StructuralNote.FixedSchurRationalRecoveryBounds

/-! Actual global extremizers have explicit rational parameters in the one
selected window, with exact coordinate recovery. -/

namespace StructuralNote.FixedSchurActualRationalEntry

open Complex Filter Erdos1045 Erdos1045.Configuration Erdos1045.EventualExact
open CommonRationalChart RationalCommonConfiguration
open FixedSchurLinear FixedSchurChart FixedSchurEquationSmooth
open FixedSchurCanonicalWordSymmetry FixedSchurActualCanonicalEntry
open FixedSchurRationalRecovery FixedSchurRationalRecoveryBounds
open FixedSchurRationalWindowDomain FixedSchurRationalWindowEnergy
open MatchingActivityActualChart CommonDomainRadius
open scoped Topology
noncomputable section

theorem eventual_actual_extremizer_rational_recovery :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z : Points (2 * m),
      ExtremalNormalization.DiameterExtremal z →
      ∃ (hm : 3 ≤ m) (x : SchurParameters m),
        CanonicalRepresentative hm z x ∧
        let s := canonicalPattern hm
        let C := center (coordinate (by omega) s x.1 x.2) x.2
        let X := FixedSchurRationalRecovery.parameters (by omega) s x.1 C
        theta (by omega) X = x.1 ∧
        normalizedCenter (by omega) (rationalSign s) X = C ∧
        RationalConfiguration.closure (by omega) (rationalSign s) X = 0 ∧
        selectedWindowEnergy (by omega) s X <
          (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) := by
  obtain ⟨m₀, hentry⟩ := eventual_actual_extremizer_has_canonicalRepresentative
  let B : ℝ := actualChartEnergyConstant + 1
  have hB : 0 ≤ B := by dsimp [B]; linarith [actualChartEnergyConstant_nonneg]
  obtain ⟨m₁, hrecovery⟩ := eventually_atTop.1 (eventual_inner_rational_recovery B hB)
  refine ⟨max m₀ m₁, ?_⟩
  intro m hm z hz
  obtain ⟨hm3, x, hx, henergy⟩ := hentry m (by omega) z hz
  refine ⟨hm3, x, hx, ?_⟩
  apply hrecovery m (by omega) (by omega) (canonicalPattern hm3) x.1 x.2 hx.1
  apply henergy.trans
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  dsimp only [B]
  nlinarith [actualChartEnergyConstant_nonneg]

end
end StructuralNote.FixedSchurActualRationalEntry
