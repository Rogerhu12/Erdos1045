import StructuralNote.FixedSchurNormalHessianBound
import StructuralNote.FixedSchurChosenRemainderBudget
import StructuralNote.HessianReferencePotential

/-! Assembly of the actual Hessian estimate, isolating the second moment input.
The following file discharges that input from the actual normal equations. -/

namespace StructuralNote.FixedSchurHessianEstimate

open Complex Filter Erdos1045.EventualExact SchurSpectrum FourierMultiplier SchurLiftBounds
open CommonDomainClosure CommonFiberCanonicalDirections FixedSchurChosenLinearization
open FixedSchurConfigurationDerivatives FixedSchurActualHessianSplit
open FixedSchurNormalHessianBound FixedSchurChosenRemainderBudget
open FixedSchurCircularCurvature FixedSchurHessianScales CommonDomainRadius
open LogDiscriminantSecondDerivative FixedSchurChart
open scoped BigOperators Topology

noncomputable section

theorem eventual_hessian_error_of_second_moment : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      let E := pairEnergy (by omega) (fun j => (η j : ℂ))
      let K := E + pairEnergy (by omega) h
      meanSquare (chosenSecondDerivative (by omega) s θ η v h) ≤ K ^ 2 →
      |second (configuration (by omega) s θ v) (velocityPath (by omega) s θ η v h 0)
        (acceleration (by omega) s θ η v h) - (2 * pairPotential (by omega) h - 2 * E)| ≤
        304000000000 / Real.sqrt (2 * m : ℝ) * K := by
  filter_upwards [eventual_actual_hessian_split, eventual_normal_hessian_bound,
    eventual_chosen_remainder_budget, eventual_circular_curvature,
    eventually_logOrder_le_sqrt] with m hsplit hnormal hrem hcirc hscale
  intro hm s θ η v h hdom hdir E K hq
  have hE : 0 ≤ E := pairEnergy_nonneg _ _
  have hA := pairEnergy_nonneg (show 0 < 2 * m by omega) h
  have hK : 0 ≤ K := add_nonneg hE hA
  have hEK : E ≤ K := by dsimp [K]; linarith only [hA]
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have ht := log_ratio_le_inv_sqrt hn hscale
  have htK := mul_le_mul_of_nonneg_right ht hK
  have hEK' := mul_le_mul_of_nonneg_left hEK
    (show 0 ≤ ((logOrder (2 * m) : ℝ) / (2 * m : ℝ)) by positivity)
  have hc := hcirc hm s θ η v hdom
  change |circularValue θ η + 2 * E| ≤ _ at hc
  have hv := hnormal hm s θ η v h hdom hdir
  have hr := hrem hm s θ η v h hdom hdir hq
  change |normalValue (by omega) s θ η v h| ≤ 3000000000 / Real.sqrt (2 * m : ℝ) * K at hv
  change |remainderValue (by omega) s θ η v h| ≤
    300000000000 * ((logOrder (2 * m) : ℝ) / (2 * m : ℝ)) * K at hr
  rw [hsplit hm s θ η v h hdom hdir]
  have he : circularValue θ η + normalValue (by omega) s θ η v h +
      2 * pairPotential (by omega) h + remainderValue (by omega) s θ η v h -
        (2 * pairPotential (by omega) h - 2 * E) =
      (circularValue θ η + 2 * E) + normalValue (by omega) s θ η v h +
        remainderValue (by omega) s θ η v h := by ring
  rw [he]
  have habs := (abs_add_le ((circularValue θ η + 2 * E) + normalValue (by omega) s θ η v h)
    (remainderValue (by omega) s θ η v h)).trans
      (add_le_add (abs_add_le (circularValue θ η + 2 * E)
        (normalValue (by omega) s θ η v h)) le_rfl)
  have hpos : 0 ≤ K / Real.sqrt (2 * m : ℝ) := by positivity
  ring_nf at hc hv hr htK hEK' habs hpos ⊢
  linarith only [hc, hv, hr, htK, hEK', habs, hpos]

theorem eventual_negative_hessian_of_second_moment : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      let K := pairEnergy (by omega) (fun j => (η j : ℂ)) + pairEnergy (by omega) h
      meanSquare (chosenSecondDerivative (by omega) s θ η v h) ≤ K ^ 2 →
      second (configuration (by omega) s θ v) (velocityPath (by omega) s θ η v h 0)
        (acceleration (by omega) s θ η v h) ≤ -K / 64 := by
  have hsmall := (constant_div_sqrt_tendsto 304000000000).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / 64 by norm_num))
  filter_upwards [eventual_hessian_error_of_second_moment, hsmall] with m herror hsmall
  intro hm s θ η v h hdom hdir K hq
  have hK : 0 ≤ K := add_nonneg (pairEnergy_nonneg _ _) (pairEnergy_nonneg _ _)
  have hE := pairEnergy_nonneg (show 0 < 2 * m by omega) (fun j => (η j : ℂ))
  have he := (abs_le.mp (herror hm s θ η v h hdom hdir hq)).2
  have hb := mul_le_mul_of_nonneg_right hsmall.le hK
  have hn := HessianReferencePotential.kernel_negative hm h hdir.2.2
  rw [HessianReferencePotential.quadratic_eq_potential (show 0 < 2 * m by omega)] at hn
  dsimp [K] at hb ⊢
  linarith only [he, hb, hn, hE]

end
end StructuralNote.FixedSchurHessianEstimate
