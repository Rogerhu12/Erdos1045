import StructuralNote.FixedSchurWordEnergy
import StructuralNote.SignPatternSymmetry

/-! Same-parameter chart stability in the manuscript's half-period Hamming distance. -/

namespace StructuralNote.FixedSchurHammingStability

open Filter Erdos1045.EventualExact
open FiniteBox SchurSpectrum CommonDomainClosure FixedSchurLinear FixedSchurChart
open FixedSchurWordStability FixedSchurWordEnergy SolWordHamming SignPatternSymmetry
open scoped BigOperators Topology

noncomputable section

theorem eventual_hamming_stability : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s t : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      (∑ j, |coordinate (by omega) s θ v j - coordinate (by omega) t θ v j|) ≤
          40 * (hamming s t : ℝ) ∧
      (∀ j, |EdgeCoordinates.J (coordinate (by omega) s θ v) j -
        EdgeCoordinates.J (coordinate (by omega) t θ v) j| ≤
          80 * (hamming s t : ℝ) / (2 * m : ℝ)) ∧
      pairEnergy (by omega)
        (center (coordinate (by omega) s θ v) v - center (coordinate (by omega) t θ v) v) ≤
          12800 * (hamming s t : ℝ) / (2 * m : ℝ) := by
  classical
  filter_upwards [eventual_coordinate_l1_stability, eventual_J_pointwise_stability,
    eventual_center_energy_stability] with m hq hJ hC
  intro hm s t θ v hdom
  have hcard : ((Finset.univ.filter (fun j => patternSign s j ≠ patternSign t j)).card : ℝ) =
      2 * (hamming s t : ℝ) := by
    exact_mod_cast fullChangedSupport_card s t
  have hq' := hq hm s t θ v hdom
  have hJ' := hJ hm s t θ v hdom
  have hC' := hC hm s t θ v hdom
  rw [hcard] at hq' hC'
  refine ⟨by nlinarith, ?_, ?_⟩
  · intro j
    have h := hJ' j
    rw [hcard] at h
    convert h using 1; ring
  · convert hC' using 1; ring

end
end StructuralNote.FixedSchurHammingStability
