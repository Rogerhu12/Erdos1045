import StructuralNote.FixedSchurActualHessianSplit
import StructuralNote.FixedSchurRemainderHessianBudget
import StructuralNote.FixedSchurChosenDerivativeSymmetry
import StructuralNote.FixedSchurAngularDerivativeEnergy

/-! Discharging the physical remainder budget on the chosen chart.
The sole quantitative input left to this lemma is the second normal moment. -/

namespace StructuralNote.FixedSchurChosenRemainderBudget

open Complex Filter Erdos1045.EventualExact SchurSpectrum SchurLift SchurLiftBounds FourierMultiplier
open CommonDomainClosure CommonFiberCanonicalPaths CommonFiberCanonicalDirections
open FixedSchurChosenPath FixedSchurChosenLinearization FixedSchurConfigurationDerivatives
open FixedSchurActualHessianSplit FixedSchurChosenRemainderSecond FixedSchurRemainderHessianBudget
open FixedSchurChosenDerivativeSymmetry FixedSchurAngularDerivativeEnergy
open FixedSchurChart FixedSchurChartQuotients FixedSchurChartCenterBounds
open CommonFiberHessianGeometryEnergy CommonDomainRadius
open scoped BigOperators Topology

noncomputable section

set_option maxHeartbeats 800000 in
theorem eventual_chosen_remainder_budget : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      let K := pairEnergy (by omega) (fun j => (η j : ℂ)) + pairEnergy (by omega) h
      meanSquare (chosenSecondDerivative (by omega) s θ η v h) ≤ K ^ 2 →
      |remainderValue (by omega) s θ η v h| ≤
        300000000000 * ((logOrder (2 * m) : ℝ) / (2 * m : ℝ)) * K := by
  have hnat : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 2 * m) tendsto_id
  have hsmall := (HessianErrorLimits.logOrder_div_tendsto.comp hnat).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / 144 by norm_num))
  filter_upwards [eventual_coordinate_properties, eventual_center_bounds,
    eventual_center_velocity_energy, eventual_chosen_derivatives_antiperiodic,
    eventual_angular_derivative_energy, hsmall] with m hcoord hcenter hvel hanti hang hsmall
  simp only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat] at hsmall
  intro hm s θ η v h hdom hdir K hq
  let E := pairEnergy (show 0 < 2 * m by omega) (fun j => (η j : ℂ))
  have hE : 0 ≤ E := pairEnergy_nonneg _ _
  have hA := pairEnergy_nonneg (show 0 < 2 * m by omega) h
  have hK : 0 ≤ K := add_nonneg hE hA
  have hEK : E ≤ K := by dsimp [K, E]; linarith only [hA]
  have hE2 : E ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ hE hEK 2
  have hN : (1 : ℝ) ≤ 2 * m := by exact_mod_cast (show 1 ≤ 2 * m by omega)
  have hNp : (0 : ℝ) < 2 * m := by linarith
  have hlog := Real.log_le_sub_one_of_pos hNp
  have hlog2 : Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 ≤ 1 := by
    apply (div_le_one (sq_pos_of_pos hNp)).2
    nlinarith only [hlog, hN, sq_nonneg (2 * (m : ℝ) - 1)]
  have hangle := hang hm s θ η v hdom hdir.2.1
  have hB : pairEnergy (by omega) (angularAcceleration θ η) ≤ 500 * K ^ 2 := by
    have hh := hangle.2
    have hprod := mul_le_mul_of_nonneg_right hlog2 (sq_nonneg E)
    change _ ≤ 500 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 * E ^ 2 at hh
    change pairEnergy (by omega)
      (fun j => -CommonFiberGeometry.diameterVector θ j * (η j : ℂ) ^ 2) ≤ _
    ring_nf at hh hprod ⊢
    linarith only [hh, hprod, hE2]
  have hlift := canonicalLift_pairEnergy_le hm _ (hanti hm s θ η v h hdom hdir).2
  have hacc : pairEnergy (by omega) (canonicalLift (chosenSecondDerivative (by omega) s θ η v h)) ≤
      32 * K ^ 2 := by linarith only [hlift, hq]
  have hC : pairEnergy (by omega) (centerPath (by omega) s θ η v h 0) ≤ 1602 := by
    simpa only [centerPath, chosenQPath, chosenParameterPath, affinePath, zero_smul, add_zero]
      using (hcenter hm s θ v hdom).2
  have hV : pairEnergy (by omega) (centerVelocityPath (by omega) s θ η v h 0) ≤ 5120002 * K :=
    hvel hm s θ η v h hdom hdir
  have hW : pairEnergy (by omega) (angularVelocityPath θ η v h 0) ≤ 18 * K := by
    have hh := hangle.1.trans (mul_le_mul_of_nonneg_left hEK (by norm_num : (0 : ℝ) ≤ 18))
    have he : angularVelocityPath θ η v h 0 =
        fun j => I * CommonFiberGeometry.diameterVector θ j * (η j : ℂ) := by
      funext j
      simp only [angularVelocityPath, chosenParameterPath, affinePath, zero_smul, add_zero]
    rwa [he]
  unfold remainderValue
  apply remainder_energy_budget (by omega) _ _ _ _ _ _ (by positivity) hsmall.le hK ?_ ?_
    hC hV hW hacc hB
  · intro p
    simpa only [centerPath, chosenQPath, chosenParameterPath, affinePath, zero_smul, add_zero,
      mul_div_assoc] using domain_center_quotient hm θ v hdom _ (hcoord hm s θ v hdom).norm_le p
  · intro p
    have he : angularErrorPath θ η v h 0 = CommonFiberHessianGeometryChord.angularError θ := by
      funext j
      simp only [angularErrorPath, chosenParameterPath, affinePath, zero_smul, add_zero,
        CommonFiberHessianGeometryChord.angularError, Pi.sub_apply]
    rw [he]
    simpa only [mul_div_assoc] using domain_angularError_ratio (by omega) θ v hdom p.1 p.2

end
end StructuralNote.FixedSchurChosenRemainderBudget
