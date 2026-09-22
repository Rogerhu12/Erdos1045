import StructuralNote.FixedSchurLocalComparison
import StructuralNote.FiniteWordClassification
import StructuralNote.FixedSchurChartGeometry
import EventualExact.NormalizedExtremalFekete

/-! Exact balanced-word selection for an extremal configuration already
represented in the fixed-Schur chart with the actual inner energy budget.
Entry of arbitrary geometric maximizers remains a separate theorem. -/

namespace StructuralNote.FixedSchurChartSelection

open Filter Complex Erdos1045 Erdos1045.EventualExact FiniteBox FourierMultiplier SchurSpectrum
open CommonDomainClosure FixedSchurChart FixedSchurObjective FixedSchurDomainSmallness
open FixedSchurLocalComparison FixedSchurChartGeometry FixedDualClassificationFinite
open FiniteWordClassification SolWordHamming
open FixedSchurComparisonScales
open scoped BigOperators Topology

noncomputable section

theorem eventually_extremal_chart_word_balanced (B : ℝ) (hB : 0 ≤ B) (C₀ : ℝ) :
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      pairEnergy (by omega) (fun j => (θ j : ℂ)) + pairEnergy (by omega) v ≤
        B ^ 2 / (2 * m : ℝ) ^ 2 →
      deficit (by omega) s ≤ C₀ / (2 * m : ℝ) ^ 2 →
      ExtremalNormalization.DiameterExtremal (configuration (by omega) s θ v) →
      BalancedWord (by omega) s := by
  obtain ⟨η, hη, himprove⟩ := eventually_nonbalanced_improvement C₀
  filter_upwards [himprove, eventual_near_local_comparison B hB C₀ 2,
    eventual_geometric_properties, eventually_error_smaller_than_gain hη (nearComparisonConstant B 2)]
    with m hfinite hcompare hgeo hsmall
  intro hm s θ v hdom henergy hdef hmax
  by_contra hnot
  obtain ⟨t, hh, hg, _, hdt⟩ := hfinite (by omega) s hdef hnot
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hgain : 0 ≤ η / (2 * m : ℕ) ^ 2 := by positivity
  have htdef : deficit (by omega) t ≤ C₀ / (2 * m : ℝ) ^ 2 := by
    linarith only [hdt, hdef, hgain]
  have hc := hcompare hm s t θ v hdom henergy hh hdef htdef
  have htgeo := hgeo hm t θ v hdom
  have hF : F (configuration (by omega) t θ v) ≤ F (configuration (by omega) s θ v) :=
    Real.log_le_log (Configuration.discriminant_pos _ htgeo.injective)
      (hmax.2 _ htgeo.diameter)
  have hg' : η / (2 * m : ℝ) ^ 2 ≤
      normalizedBoxEnergy (operator (2 * m)) (baseWord (patternSign t)) -
        normalizedBoxEnergy (operator (2 * m)) (baseWord (patternSign s)) := by
    change η / ((2 * m : ℕ) : ℝ) ^ 2 ≤
      normalizedBoxEnergy (operator (2 * m)) (baseWord (patternSign t)) -
        normalizedBoxEnergy (operator (2 * m)) (baseWord (patternSign s)) at hg
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hg
  have hc' := (abs_le.mp hc).2
  norm_num only [Nat.cast_ofNat] at hc'
  linarith only [hF, hg', hc', hsmall]

end
end StructuralNote.FixedSchurChartSelection

