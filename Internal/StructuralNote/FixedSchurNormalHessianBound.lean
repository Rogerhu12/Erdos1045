import StructuralNote.FixedSchurActualHessianSplit
import StructuralNote.FixedSchurChosenSecondBounds
import StructuralNote.FixedSchurChosenFirstBounds
import StructuralNote.FixedSchurHessianScales

/-! The true scalar Schur Hessian is a uniform inverse-square-root error. -/

namespace StructuralNote.FixedSchurNormalHessianBound

open Complex Filter Erdos1045.EventualExact SchurSpectrum FourierMultiplier SchurLiftBounds
open CommonDomainClosure CommonFiberCanonicalDirections FixedSchurChosenLinearization
open FixedSchurActualHessianSplit FixedSchurChosenSecondBounds FixedSchurChosenFirstBounds
open FixedSchurQuadraticDerivatives FixedSchurChart FixedSchurHessianScales
open scoped BigOperators Topology

noncomputable section

theorem eventual_normal_hessian_bound : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      |normalValue (by omega) s θ η v h| ≤
        3000000000 / Real.sqrt (2 * m : ℝ) *
          (pairEnergy (by omega) (fun j => (η j : ℂ)) + pairEnergy (by omega) h) := by
  filter_upwards [eventual_chosen_second_l1, eventual_chosen_first_coarse,
    eventual_coordinate_properties, eventually_ge_atTop 1024] with m hsecond hfirst hcoord hsize
  intro hm s θ η v h hdom hdir
  let E := pairEnergy (show 0 < 2 * m by omega) (fun j => (η j : ℂ))
  let A := pairEnergy (show 0 < 2 * m by omega) h
  let K := E + A
  have hE : 0 ≤ E := pairEnergy_nonneg _ _
  have hA : 0 ≤ A := pairEnergy_nonneg _ _
  have hK : 0 ≤ K := add_nonneg hE hA
  have hroot : Real.sqrt (A * E) ≤ K := by
    apply (Real.sqrt_le_iff).2
    exact ⟨hK, by dsimp [K]; nlinarith only [sq_nonneg (A - E)]⟩
  have hN : (1 : ℝ) ≤ 2 * m := by exact_mod_cast (show 1 ≤ 2 * m by omega)
  have hi := inverse_le_inverse_sqrt hN
  have hiK := mul_le_mul_of_nonneg_right hi hK
  have hr := div_le_div_of_nonneg_right hroot (Real.sqrt_nonneg (2 * m : ℝ))
  have hq1 := (hfirst hm s θ η v h hdom hdir).1
  have hq2 := hsecond hm s θ η v h hdom hdir
  change meanSquare (chosenFirstDerivative (by omega) s θ η v h) ≤ 80000 * K / (2 * m : ℝ) at hq1
  change (∑ j, |chosenSecondDerivative (by omega) s θ η v h j|) / (2 * m : ℝ) ≤
    240000000 * (K / (2 * m : ℝ) + Real.sqrt (A * E) / Real.sqrt (2 * m : ℝ)) at hq2
  have hb := quadraticSecond_abs_le (show 2048 ≤ 2 * m by omega)
    (coordinate (by omega) s θ v) (chosenFirstDerivative (by omega) s θ η v h)
    (chosenSecondDerivative (by omega) s θ η v h) (hcoord hm s θ v hdom).norm_le
  change |normalValue (by omega) s θ η v h| ≤ _ at hb
  have hpos : 0 ≤ K / Real.sqrt (2 * m : ℝ) := by positivity
  change |normalValue (by omega) s θ η v h| ≤ 3000000000 / Real.sqrt (2 * m : ℝ) * K
  ring_nf at hiK hr hq1 hq2 hb hpos ⊢
  linarith only [hiK, hr, hq1, hq2, hb, hpos]

end
end StructuralNote.FixedSchurNormalHessianBound
