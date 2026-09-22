import StructuralNote.ExplicitFixedSchurFirstMoments
import StructuralNote.ExplicitHessianThresholdFixedSchurSecondMoments
import StructuralNote.ExplicitHessianThresholdFixedSchurGeometry
import StructuralNote.FixedSchurStrictCurvature
/-! The actual fixed-Schur Hessian bound with a fixed arithmetic threshold. -/
namespace StructuralNote.ExplicitFixedSchurHessianEstimate
open Complex Filter Erdos1045 Erdos1045.EventualExact SchurSpectrum FourierMultiplier
open CommonDomainClosure CommonFiberCanonicalDirections FixedSchurChosenPath
open FixedSchurConfigurationDerivatives FixedSchurChosenLinearization
open FixedSchurPotentialDerivatives FixedSchurQuadraticDerivatives
open FixedSchurCircularCurvature FixedSchurChosenRemainderSecond
open FixedSchurGeometricRemainderHessian FixedSchurObjectiveSmooth
open FixedSchurChart FixedSchurChartQuotients FixedSchurChartGeometry
open LogDiscriminantSecondDerivative FixedSchurObjective
open CommonFiberGeometry
open scoped BigOperators Topology
open Complex Filter Erdos1045.EventualExact SchurSpectrum FourierMultiplier SchurLiftBounds
open CommonDomainClosure CommonFiberCanonicalDirections FixedSchurChosenLinearization
open FixedSchurActualHessianSplit FixedSchurChosenSecondBounds FixedSchurChosenFirstBounds
open FixedSchurQuadraticDerivatives FixedSchurChart FixedSchurHessianScales
open Complex Filter Erdos1045.EventualExact SchurSpectrum SchurLift SchurLiftBounds FourierMultiplier
open CommonDomainClosure CommonFiberCanonicalPaths CommonFiberCanonicalDirections
open FixedSchurChosenPath FixedSchurChosenLinearization FixedSchurConfigurationDerivatives
open FixedSchurActualHessianSplit FixedSchurChosenRemainderSecond FixedSchurRemainderHessianBudget
open FixedSchurChosenDerivativeSymmetry FixedSchurAngularDerivativeEnergy
open FixedSchurChart FixedSchurChartQuotients FixedSchurChartCenterBounds
open CommonFiberHessianGeometryEnergy CommonDomainRadius
open FixedSchurConfigurationDerivatives FixedSchurActualHessianSplit
open FixedSchurNormalHessianBound FixedSchurChosenRemainderBudget
open FixedSchurCircularCurvature FixedSchurHessianScales CommonDomainRadius
open LogDiscriminantSecondDerivative FixedSchurChart
open Complex Filter Erdos1045.EventualExact SchurSpectrum
open CommonDomainClosure CommonFiberCanonicalDirections CommonFiberCanonicalPaths
open FixedSchurChosenLinearization FixedSchurChosenSecondBounds
open FixedSchurConfigurationDerivatives FixedSchurHessianEstimate FixedSchurObjectivePaths
open FixedSchurEquationSmooth FixedSchurChart LogDiscriminantSecondDerivative
noncomputable section

theorem actual_hessian_split {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) : ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      second (configuration (by omega) s θ v) (velocityPath (by omega) s θ η v h 0)
        (acceleration (by omega) s θ η v h) =
      circularValue θ η + normalValue (by omega) s θ η v h +
        2 * pairPotential (by omega) h + remainderValue (by omega) s θ η v h := by
  have hjets := ExplicitCanonicalEntryObjectivePaths.chosen_path_jets hN
  have hquot := ExplicitComparisonGeometry.quotient_properties hN
  have hcoord := ExplicitHessianThresholdFixedSchur.coordinate_properties hN
  have hgeo := ExplicitHessianThresholdFixedSchurGeometry.geometric_properties hN
  have hquad := ExplicitCanonicalEntryObjectivePaths.chosen_quadratic_second hN
  have hrem := ExplicitCanonicalEntryObjectivePaths.actual_remainder_second hN
  have hlog := ExplicitCanonicalEntryObjectivePaths.actual_log_second_derivative hN
  clear hN
  intro hm s θ η v h hdom hdir
  let Z : ℝ → ℝ := fun t => F (configurationPath (by omega) s θ η v h t)
  let D : ℝ → ℝ := fun t => F (diameterVector (chosenParameterPath θ η v h t).1)
  let V : ℝ → ℝ := fun t => normalizedBoxEnergy (operator (2 * m))
    (chosenQPath (by omega) s θ η v h t)
  let P : ℝ → ℝ := fun t => pairPotential (by omega) (chosenParameterPath θ η v h t).2
  let R : ℝ → ℝ := fun t => newRemainder (by omega)
    (chosenParameterPath θ η v h t).1 (centerPath (by omega) s θ η v h t)
  have hn := affine_domain_near_zero (show 0 < m by omega) (θ, v) (η, h) hdom hdir
  have hj := hjets hm s θ η v h hdom hdir
  have hq := Filter.eventually_all.mpr (fun j => (hj j).1)
  have hsplit : Z =ᶠ[𝓝 0] (fun t => D t + V t + P t + R t) := by
    filter_upwards [hn] with t ht
    have he := exact_split hm (chosenParameterPath θ η v h t).1
      (chosenQPath (by omega) s θ η v h t) (chosenParameterPath θ η v h t).2
      (hcoord hm s _ _ ht).antiperiodic ht.2.2.1.1 ht.2.2.1.2.2
    change Z t - D t = V t + P t + R t at he
    linarith only [he]
  have hdiff : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ D t ∧
      DifferentiableAt ℝ V t ∧ DifferentiableAt ℝ P t ∧ DifferentiableAt ℝ R t := by
    filter_upwards [hn, hq] with t ht hqt
    have hZd := hasDerivAt_pi.mpr (configurationPath_hasDerivAt (by omega) s θ η v h t hqt)
    have hDd : DifferentiableAt ℝ (fun r => diameterVector (chosenParameterPath θ η v h r).1) t := by
      have hd (j : Fin (2 * m)) :=
        (angularErrorPath_hasDerivAt θ η v h t j).add_const (SignedPressureAngular.root (2 * m) j)
      have he : (fun r j => angularErrorPath θ η v h r j + SignedPressureAngular.root (2 * m) j) =
          (fun r => diameterVector (chosenParameterPath θ η v h r).1) := by
        funext r j
        simp only [angularErrorPath, Pi.sub_apply, sub_add_cancel]
      have hd' := hasDerivAt_pi.mpr hd
      rw [he] at hd'
      exact hd'.differentiableAt
    have hDF : DifferentiableAt ℝ D t := by
      have hF := (F_contDiffAt_of_injective (hquot hm s _ _ ht).1).differentiableAt (by simp)
      have hc := hF.comp t hDd
      exact hc
    have hZF : DifferentiableAt ℝ Z t := by
      have hF := (F_contDiffAt_of_injective (hgeo hm s _ _ ht).injective).differentiableAt (by simp)
      have hc := hF.comp t hZd.differentiableAt
      exact hc
    have hPC := (potential_hasDerivAt (show 0 < 2 * m by omega)
      (centerPath_hasDerivAt (by omega) s θ η v h t hqt)).differentiableAt
    refine ⟨hDF, (energy_hasDerivAt hqt).differentiableAt,
      (potential_hasDerivAt (by omega) (parameter_center_hasDerivAt θ η v h · t)).differentiableAt, ?_⟩
    exact (hZF.sub hDF).sub hPC
  have hd : HasDerivAt (deriv D) (circularValue θ η) 0 :=
    circular_log_second θ η v h (hquot hm s θ v hdom).1
  have hv : HasDerivAt (deriv V) (normalValue (by omega) s θ η v h) 0 :=
    hquad hm s θ η v h hdom hdir
  have hp : HasDerivAt (deriv P) (2 * pairPotential (by omega) h) 0 :=
    affine_potential_second (by omega) θ η v h
  have hr : HasDerivAt (deriv R) (remainderValue (by omega) s θ η v h) 0 :=
    hrem hm s θ η v h hdom hdir
  have hs := (second_sum_four hd hv hp hr hdiff).congr_of_eventuallyEq hsplit.deriv
  exact (hlog hm s θ η v h hdom hdir).unique hs

theorem normal_hessian_bound {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) : ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      |normalValue (by omega) s θ η v h| ≤
        3000000000 / Real.sqrt (2 * m : ℝ) *
          (pairEnergy (by omega) (fun j => (η j : ℂ)) + pairEnergy (by omega) h) := by
  have hsecond := ExplicitFixedSchurSecondMoments.chosen_second_l1 hN
  have hfirst := ExplicitFixedSchurFirstMoments.chosen_first_coarse hN
  have hcoord := ExplicitHessianThresholdFixedSchur.coordinate_properties hN
  have hsize : 1024 ≤ m := by
    have hh : 2048 ≤ ExplicitHessianThreshold.orderThreshold := by
      change (2 : ℕ) ^ 11 ≤ 2 ^ 100000
      exact Nat.pow_le_pow_right (by decide : 0 < 2) (by decide)
    have hmge : 2048 ≤ 2 * m := hh.trans hN
    clear hN hh
    omega
  clear hN
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

set_option maxHeartbeats 800000 in
theorem chosen_remainder_budget {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) : ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      let K := pairEnergy (by omega) (fun j => (η j : ℂ)) + pairEnergy (by omega) h
      meanSquare (chosenSecondDerivative (by omega) s θ η v h) ≤ K ^ 2 →
      |remainderValue (by omega) s θ η v h| ≤
        300000000000 * ((logOrder (2 * m) : ℝ) / (2 * m : ℝ)) * K := by
  have hcoord := ExplicitHessianThresholdFixedSchur.coordinate_properties hN
  have hcenter := ExplicitComparisonGeometry.center_bounds hN
  have hvel := ExplicitFixedSchurFirstMoments.center_velocity_energy hN
  have hanti := ExplicitFixedSchurHessianGeometry.chosen_derivatives_antiperiodic hN
  have hang := ExplicitFixedSchurHessianGeometry.angular_derivative_energy hN
  have hsmall := ExplicitFixedSchurHessianGeometry.log_ratio_small hN
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hsmall
  clear hN
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

theorem hessian_error_of_second_moment {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) : ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      let E := pairEnergy (by omega) (fun j => (η j : ℂ))
      let K := E + pairEnergy (by omega) h
      meanSquare (chosenSecondDerivative (by omega) s θ η v h) ≤ K ^ 2 →
      |second (configuration (by omega) s θ v) (velocityPath (by omega) s θ η v h 0)
        (acceleration (by omega) s θ η v h) - (2 * pairPotential (by omega) h - 2 * E)| ≤
        304000000000 / Real.sqrt (2 * m : ℝ) * K := by
  have hsplit := actual_hessian_split hN
  have hnormal := normal_hessian_bound hN
  have hrem := chosen_remainder_budget hN
  have hcirc := ExplicitFixedSchurHessianGeometry.circular_curvature hN
  have hscale := ExplicitFixedSchurHessianGeometry.logOrder_le_sqrt hN
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hscale
  clear hN
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

theorem negative_hessian_of_second_moment {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) : ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      let K := pairEnergy (by omega) (fun j => (η j : ℂ)) + pairEnergy (by omega) h
      meanSquare (chosenSecondDerivative (by omega) s θ η v h) ≤ K ^ 2 →
      second (configuration (by omega) s θ v) (velocityPath (by omega) s θ η v h 0)
        (acceleration (by omega) s θ η v h) ≤ -K / 64 := by
  have herror := hessian_error_of_second_moment hN
  have hsmall := ExplicitFixedSchurHessianGeometry.hessian_coefficient_small hN
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hsmall
  clear hN
  intro hm s θ η v h hdom hdir K hq
  have hK : 0 ≤ K := add_nonneg (pairEnergy_nonneg _ _) (pairEnergy_nonneg _ _)
  have hE := pairEnergy_nonneg (show 0 < 2 * m by omega) (fun j => (η j : ℂ))
  have he := (abs_le.mp (herror hm s θ η v h hdom hdir hq)).2
  have hb := mul_le_mul_of_nonneg_right hsmall.le hK
  have hn := HessianReferencePotential.kernel_negative hm h hdir.2.2
  rw [HessianReferencePotential.quadratic_eq_potential (show 0 < 2 * m by omega)] at hn
  dsimp [K] at hb ⊢
  linarith only [he, hb, hn, hE]

theorem actual_hessian_estimate {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) : ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      let E := pairEnergy (by omega) (fun j => (η j : ℂ))
      let K := E + pairEnergy (by omega) h
      let H := second (configuration (by omega) s θ v) (velocityPath (by omega) s θ η v h 0)
        (acceleration (by omega) s θ η v h)
      |H - (2 * pairPotential (by omega) h - 2 * E)| ≤
        304000000000 / Real.sqrt (2 * m : ℝ) * K ∧ H ≤ -K / 64 := by
  have herr := hessian_error_of_second_moment hN
  have hneg := negative_hessian_of_second_moment hN
  have hsecond := ExplicitFixedSchurSecondMoments.chosen_second_coarse hN
  clear hN
  intro hm s θ η v h hdom hdir
  have hq := hsecond hm s θ η v h hdom hdir
  exact ⟨herr hm s θ η v h hdom hdir hq, hneg hm s θ η v h hdom hdir hq⟩

end
end StructuralNote.ExplicitFixedSchurHessianEstimate
