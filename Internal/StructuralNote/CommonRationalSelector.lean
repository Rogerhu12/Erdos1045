import StructuralNote.CommonRationalRecovery
import StructuralNote.RationalBranchSelector

/-! The reverse selector for actual common-fiber configurations. The rational
variables are constructed explicitly; their energy and root windows are proved.
Injectivity is transported exactly across the resulting rigid motion. -/

namespace StructuralNote.CommonRationalSelector

open Erdos1045.EventualExact LensClosure SchurSpectrum
open CommonClosureEnergy CommonTangentialParameters CommonFiberGeometry CommonRationalChart
open CommonRationalRecovery CommonDomainClosure RationalCommonConfiguration
open scoped BigOperators
noncomputable section

theorem closure_of_recovery {m : ℕ} (hm : 2 ≤ m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ) (X : RationalConfiguration.Variables m → ℝ)
    (hX : RationalAngleBranch.SmallWindow X) (hs : ∀ j, σ j ^ 2 = 1)
    (hθ : theta (by omega) X = θ) (hv : recoveredVector (by omega) σ X = v)
    (hξ : recoveredCorrection (by omega) σ X = ξ)
    (hz : closure (phase (by omega) θ) (fun j => 2 * Real.cos (halfAngle (by omega) θ j))
      σ (coordinates (by omega) v) ξ = 0) : RationalConfiguration.closure (by omega) σ X = 0 := by
  have he : closure (phase (by omega) (theta (by omega) X))
      (fun j => 2 * Real.cos (halfAngle (by omega) (theta (by omega) X) j))
      σ (coordinates (by omega) (recoveredVector (by omega) σ X)) (recoveredCorrection (by omega) σ X) =
      unit (-angleMean (by omega) X) * RationalConfiguration.closure (by omega) σ X := by
    change (∑ j, fiberIncrement (by omega) (theta (by omega) X) (recoveredVector (by omega) σ X)
      σ (recoveredCorrection (by omega) σ X) j) = _
    simp_rw [fiberIncrement_eq_rotated hm σ X hX hs]
    rw [← Finset.mul_sum]
    rfl
  rw [hθ, hv, hξ, hz] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (by
    intro hh
    have hn := norm_unit (-angleMean (by omega) X)
    rw [hh, norm_zero] at hn
    norm_num at hn)

theorem eventual_inverse_chart :
    ∃ N : ℕ, ∀ (m : ℕ) (hm : N + 1048576 ≤ m) (θ : Fin (2 * m) → ℝ)
      (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ), InDomain (by omega) θ v →
      (∀ j, σ j ^ 2 = 1) → ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2 →
      closure (phase (by omega) θ) (fun j => 2 * Real.cos (halfAngle (by omega) θ j))
        σ (coordinates (by omega) v) ξ = 0 →
      let X := parameters (by omega) θ v σ ξ
      RationalAngleBranch.SmallWindow X ∧ theta (by omega) X = θ ∧
        recoveredVector (by omega) σ X = v ∧ recoveredCorrection (by omega) σ X = ξ ∧
        RationalConfiguration.closure (by omega) σ X = 0 ∧
        ‖recoveredCorrection (by omega) σ X‖ < CommonSelectorRoot.rootWindow (2 * m) ∧
        RationalBranchSelector.EnergyWindow (by omega) σ X ∧
        (∀ j, configuration (by omega) θ v σ ξ j = unit (initialAngle (by omega) θ) *
          (RationalConfiguration.configuration (by omega) σ X j - centerMean (by omega) σ X)) := by
  obtain ⟨N, hN⟩ := CommonRationalWindowBounds.eventual_domain_chart_bounds
  refine ⟨N, ?_⟩
  intro m hm θ v σ ξ hdom hs hξ hz
  dsimp only
  have hm0 : 0 < m := by omega
  have hm2 : 2 ≤ m := by omega
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm0
  obtain ⟨hθb, htb⟩ := hN m (by omega) θ v hdom ξ hξ
  have hsmall := small_parameters hm0 θ v σ ξ hs hθb htb
  have ha (j : Fin m) : |relativeAngle hm0 θ j| < Real.pi := by
    have hh := abs_sub_le (θ (CommonClosureEnergy.halfIndex j)) 0 (initialAngle hm0 θ)
    simp only [sub_zero, zero_sub, abs_neg] at hh
    have hb := hθb ⟨0, by omega⟩
    change |initialAngle hm0 θ| < _ at hb
    have hr : 1 / (8 * (2 * m : ℝ)) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
    unfold relativeAngle
    linarith [hθb (CommonClosureEnergy.halfIndex j), Real.pi_gt_three]
  have ht4 (j : Fin m) : (heightParameter (coordinates hm0 v) ξ j) ^ 2 ≤ 4 := by
    have hr : 1 / (4 * (2 * m : ℝ)) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
    have hb := (htb j).trans hr
    nlinarith [sq_abs (heightParameter (coordinates hm0 v) ξ j), abs_nonneg (heightParameter (coordinates hm0 v) ξ j)]
  have hR (j : Fin m) : 0 < 1 + (crossingRelative hm0 θ v σ ξ j).re := by
    have ht1 : |heightParameter (coordinates hm0 v) ξ j| ≤ 1 := (htb j).trans
      ((div_le_one (by positivity)).2 (by linarith))
    have hav : |relativeAverage hm0 θ j| < 1 / 4 := by
      unfold relativeAverage angleAverage initialAngle
      have he := abs_sub_le ((θ (CommonClosureEnergy.halfIndex j) +
        θ (FiniteFourierLift.successor (by omega) (CommonClosureEnergy.halfIndex j))) / 2) 0 (θ ⟨0, by omega⟩)
      simp only [sub_zero, zero_sub, abs_neg, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at he
      have hr : 1 / (8 * (2 * m : ℝ)) ≤ 1 / 16 := by gcongr; linarith
      have hb := abs_add_le (θ (CommonClosureEnergy.halfIndex j))
        (θ (FiniteFourierLift.successor (by omega) (CommonClosureEnergy.halfIndex j)))
      linarith [hθb (CommonClosureEnergy.halfIndex j),
        hθb (FiniteFourierLift.successor (by omega) (CommonClosureEnergy.halfIndex j)), hθb ⟨0, by omega⟩]
    have htq : |heightParameter (coordinates hm0 v) ξ j| ≤ 1 / 4 := (htb j).trans (by gcongr; linarith)
    have hc := crossingRelative_close hm0 θ v σ ξ j (hs j) ht1
    have hr := RationalChartInverse.real_part_pos_of_close (by linarith : ‖crossingRelative hm0 θ v σ ξ j - 1‖ < 1)
    linarith
  have ht := tangential_parameters hm0 θ v σ ξ hdom.1 hdom.2.1 ha hs ht4 hR
  have hθ := theta_parameters hm0 θ v σ ξ hdom.1 hdom.2.1 ha
  have hv := vector_parameters hm2 θ v σ ξ hdom.2.2.1 ht
  have hc := correction_parameters hm2 θ v σ ξ hdom.2.2.1 ht
  have hH := closure_of_recovery hm2 θ v σ ξ _ hsmall hs hθ hv hc hz
  refine ⟨hsmall, hθ, hv, hc, hH, ?_, ?_, ?_⟩
  · rw [hc]
    exact hξ.trans_lt (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      CommonSelectorRoot.constructed_radius_lt_window (show 2097152 ≤ 2 * m by omega))
  · unfold RationalBranchSelector.EnergyWindow
    rw [hθ, hv]
    exact hdom.2.2.2
  · intro j
    have he := configuration_eq_rigid_motion hm2 σ (parameters hm0 θ v σ ξ) hsmall hs hH j
    rw [hθ, hv, hc, angleMean_parameters hm0 θ v σ ξ hdom.1 hdom.2.1 ha, neg_neg] at he
    exact he

end
end StructuralNote.CommonRationalSelector
