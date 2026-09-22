import StructuralNote.ExplicitLocalComparison
import StructuralNote.FixedSchurChartSelection

/-! Pointwise transfer of finite-word improvement to the actual maximizing chart. -/
namespace StructuralNote.ExplicitBalancedSelection

open Erdos1045 Erdos1045.EventualExact Complex
open FiniteBox FourierMultiplier SchurSpectrum CommonDomainClosure
open FixedSchurChart FixedSchurObjective FixedSchurChartGeometry
open FixedDualClassificationFinite FixedSchurLocalComparison
open FiniteWordClassification SolWordHamming
open FixedSchurDomainSmallness
noncomputable section

def FiniteImprovement (m : ℕ) (C η : ℝ) : Prop :=
  ∀ (hm : 0 < m) (s : SignPattern hm),
    deficit hm s ≤ C / (2 * m : ℝ) ^ 2 → ¬ BalancedWord hm s →
    ∃ t : SignPattern hm, hamming s t ≤ 2 ∧
      η / (2 * m : ℕ) ^ 2 ≤
        normalizedBoxEnergy (operator (2 * m)) (vertex (amplitude (2 * m)) t) -
        normalizedBoxEnergy (operator (2 * m)) (vertex (amplitude (2 * m)) s) ∧
      0 ≤ deficit hm t ∧ deficit hm t + η / (2 * m : ℕ) ^ 2 ≤ deficit hm s

def orderThreshold (B C η : ℝ) : ℕ := max (ExplicitLocalComparison.nearThreshold B C)
  (Erdos1045.ExplicitThreshold.inverseSqrtThreshold (nearComparisonConstant B 2) η)

theorem extremal_chart_word_balanced {m : ℕ} {B C η : ℝ} (hB : 0 ≤ B) (hη : 0 < η)
    (hn : orderThreshold B C η ≤ 2 * m) (hm : 2 ≤ m)
    (hfinite : FiniteImprovement m C η)
    (hgeometry : ∀ (s : SignPattern (by omega)) (θ : Fin (2 * m) → ℝ)
      (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v → GeometricProperties hm s θ v)
    (s : SignPattern (by omega)) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (hdom : InDomain (by omega) θ v)
    (henergy : pairEnergy (by omega) (fun j => (θ j : ℂ)) + pairEnergy (by omega) v ≤
      B ^ 2 / (2 * m : ℝ) ^ 2)
    (hdef : deficit (by omega) s ≤ C / (2 * m : ℝ) ^ 2)
    (hmax : ExtremalNormalization.DiameterExtremal (configuration (by omega) s θ v)) :
    BalancedWord (by omega) s := by
  have hcompare := ExplicitLocalComparison.near_local_comparison B hB C 2 ((le_max_left _ _).trans hn)
  have hsmall := Erdos1045.ExplicitThreshold.comparison_error_small hη ((le_max_right _ _).trans hn)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hsmall
  clear hn
  by_contra hnot
  obtain ⟨t, hh, hg, _, hdt⟩ := hfinite (by omega) s hdef hnot
  have hgain : 0 ≤ η / (2 * m : ℕ) ^ 2 := by positivity
  have htdef : deficit (by omega) t ≤ C / (2 * m : ℝ) ^ 2 := by
    linarith only [hdt, hdef, hgain]
  have hc := hcompare hm s t θ v hdom henergy hh hdef htdef
  have htgeo := hgeometry t θ v hdom
  have hF : F (configuration (by omega) t θ v) ≤ F (configuration (by omega) s θ v) :=
    Real.log_le_log (Configuration.discriminant_pos _ htgeo.injective) (hmax.2 _ htgeo.diameter)
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
end StructuralNote.ExplicitBalancedSelection
