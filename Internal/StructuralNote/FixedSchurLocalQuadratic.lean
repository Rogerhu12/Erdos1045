import StructuralNote.FixedSchurNormalInnerDifference
import StructuralNote.FixedSchurNormalInnerEnergy
import StructuralNote.FixedSchurWordExpansionBounds
import StructuralNote.FixedSchurNearWordAngular

/-! Actual normal-coordinate quadratic comparison at identical parameters. -/

namespace StructuralNote.FixedSchurLocalQuadratic

open Filter Complex Erdos1045.EventualExact FiniteBox FourierMultiplier SchurSpectrum SchurLiftBounds
open CommonClosureEnergy CommonDomainClosure FixedSchurChart
open FixedSchurNormalExpansion FixedSchurNormalInnerBound FixedSchurInnerAngles
open FixedSchurNormalInnerEnergy FixedSchurNormalInnerDifference FixedSchurQuadraticExpansion FixedSchurWordExpansionBounds
open FixedSchurDomainSmallness FixedSchurNearWordAngular SolWordHamming
open scoped BigOperators Topology

noncomputable section

def quadraticConstant (B S : ℝ) : ℝ :=
  12 * S * normalEnergyConstant B + 3 * differenceConstant B S +
    4 * Real.pi ^ 2 * B ^ 2 + normalEnergyConstant B ^ 2

theorem quadraticConstant_nonneg {B S : ℝ} (hB : 0 ≤ B) (hS : 0 ≤ S) :
    0 ≤ quadraticConstant B S := by
  unfold quadraticConstant
  have hE := normalEnergyConstant_nonneg B
  have hD := differenceConstant_nonneg hB hS
  positivity

theorem normal_expansion_reconstruction {n : ℕ} (hn : 0 < n)
    (θ q σ : Fin n → ℝ) :
    baseWord σ + angularField σ (angleDifference hn θ) + normalError hn θ q σ = q := by
  funext j
  simp only [baseWord, angularField, normalError, Pi.add_apply]
  ring

theorem eventual_actual_quadratic_comparison (B : ℝ) (hB : 0 ≤ B) (s₀ : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 2 ≤ m) (s t : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      pairEnergy (by omega) (fun j => (θ j : ℂ)) + pairEnergy (by omega) v ≤
        B ^ 2 / (2 * m : ℝ) ^ 2 → hamming s t ≤ s₀ →
      |(normalizedBoxEnergy (operator (2 * m)) (coordinate (by omega) s θ v) -
          normalizedBoxEnergy (operator (2 * m)) (coordinate (by omega) t θ v)) -
        (normalizedBoxEnergy (operator (2 * m)) (baseWord (patternSign s)) -
          normalizedBoxEnergy (operator (2 * m)) (baseWord (patternSign t))) -
        (∑ j, (signedPotential s j - signedPotential t j) * angleDifference (by omega) θ j) / 2| ≤
        quadraticConstant B (s₀ : ℝ) / (2 * m : ℝ) ^ 3 := by
  filter_upwards [eventual_normal_error_meanSquare B hB,
    eventual_normal_error_l1_difference B hB s₀, eventually_ge_atTop 1024] with m he herr hmN
  intro hm s t θ v hdom henergy hham
  have hs := he hm s θ v hdom henergy
  have ht := he hm t θ v hdom henergy
  have hd := herr hm s t θ v hdom henergy hham
  have hangle := angleDifference_meanSquare_le_of_joint_energy (by omega) θ v hB hdom henergy
  have hh : (hamming s t : ℝ) ≤ s₀ := by exact_mod_cast hham
  have h := scalar_word_comparison (show 2048 ≤ 2 * m by omega) s t
    (angleDifference (by omega) θ)
    (normalError (by omega) θ (coordinate (by omega) s θ v) (patternSign s))
    (normalError (by omega) θ (coordinate (by omega) t θ v) (patternSign t))
    (normalEnergyConstant_nonneg B) (Nat.cast_nonneg s₀) hh hangle hs ht hd
  rw [normal_expansion_reconstruction, normal_expansion_reconstruction] at h
  apply h.trans_eq
  congr 1
  unfold quadraticConstant
  ring

end
end StructuralNote.FixedSchurLocalQuadratic

