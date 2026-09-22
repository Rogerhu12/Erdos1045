import StructuralNote.MatchingActivityRadialDiameterError
import StructuralNote.CommonFiberHessianGeometryGradient
import StructuralNote.RadialObjectivePrice

/-! The gradient estimate for actual unsaturated configurations follows from
their pointwise step bound, uniformly over all cyclic lags. -/

namespace StructuralNote.MatchingActivityRadialGradient

open Erdos1045 Erdos1045.EventualExact Complex Configuration
open FiniteFourierLift FourierMultiplier SchurSpectrum SchurLift LensClosure
open StrongPointwiseCoordinates StrongPointwiseSteps StrongBudgetConsequences
open ActualCrossingGeometry ExtremalPolarCenter NormalizedPolarRepresentation SignedPressureRemainder StrongObjectiveEstimate SinglePressureEstimate
open GeometricRelativeRemainder SignedPressureAngular CommonFiberGeometry
open CommonFiberHessianGeometryChord CommonFiberHessianGeometryGradient
open MatchingActivityRadialModelEnergy MatchingActivityRadialDiameterError MatchingActivityNonlocalPairs
open RadialObjectivePrice LocalGradient
noncomputable section

def configurationStepConstant : ℝ := diameterStepConstant + physicalStepConstant

theorem configurationStepConstant_nonneg : 0 ≤ configurationStepConstant :=
  add_nonneg diameterStepConstant_nonneg constants_nonneg.1

theorem gradientDeviation_of_step {n : ℕ} (hn : 4 ≤ n) (z : Points n) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδs : δ ≤ 1 / 2)
    (hstep : ∀ j, ‖difference (by omega) (z - root n) j‖ ≤ δ / n) :
    gradientDeviation z ≤ 2 * δ * (1 + Real.log n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  let u := periodize (show 0 < n by omega) (z - root n)
  have hu : Function.Periodic u n := periodize_periodic (by omega) _
  have hp (i : Fin n) (h : ℕ) (hh : h ∈ Finset.Ico 1 n) : ‖LocalDFT.pairRatio n u i h‖ ≤ δ := by
    have he := pairRatio_of_step (show 0 < n by omega) u hu
      (NonlocalFeasibility.periodize_step_bound (by omega) (z - root n) hstep)
      (show 0 < h by have := Finset.mem_Ico.mp hh; omega) (Finset.mem_Ico.mp hh).2 i
    have hid : (n : ℝ) / 4 * (δ / n) = δ / 4 := by field_simp
    rw [hid] at he
    linarith
  have hz : (fun j : Fin n => LocalPhase.regularRoot n ^ (j : ℕ) + u j) = z := by
    funext j
    simp only [u, periodize_fin, Pi.sub_apply, root, add_sub_cancel]
  have hpoint (i : Fin n) : ‖realGradient z i - ((n : ℂ) - 1) * LocalPhase.regularRoot n ^ (i : ℕ)‖ ≤
      2 * n * δ * (1 + Real.log n) := by
    have he := realGradient_uniform_lags (show 0 < n by omega) u hu hδ hδs hp i
    rw [hz] at he
    have hreg := LocalGradient.realGradient_regular (show 0 < n by omega) i
    rw [hreg] at he
    exact he
  have hnrm : ‖fun i : Fin n => realGradient z i - ((n : ℂ) - 1) * LocalPhase.regularRoot n ^ (i : ℕ)‖ ≤
      2 * n * δ * (1 + Real.log n) := by
    apply pi_norm_le_iff_of_nonneg (by have := Real.log_nonneg hn1; positivity) |>.2
    exact hpoint
  unfold gradientDeviation
  apply (div_le_iff₀ hn0).2
  exact hnrm.trans_eq (by ring)

theorem model_configuration_step {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ)
    (hb : PointwiseBounds hm β u)
    (hθ : ∀ j, |normalizedAngle m u j| ≤ 1 / (1000 * (2 * m : ℝ))) (j : Fin (2 * m)) :
    ‖difference (by omega) (normalizedPoint m β u - root (2 * m)) j‖ ≤
      configurationStepConstant / (2 * m : ℝ) ^ 2 := by
  have hd := modelDiameter_step hm β u hb hθ j
  have hc := hb.2.2.2.2.2.2 j
  have he : difference (show 0 < 2 * m by omega) (normalizedPoint m β u - root (2 * m)) j =
      difference (by omega) (modelDiameter m β u - root (2 * m)) j + difference (by omega) (actualCenter m β u) j := by
    simp only [difference, Pi.sub_apply, normalizedPoint_decomposition, modelDiameter]
    ring
  rw [he]
  exact ((norm_add_le _ _).trans (add_le_add hd hc)).trans_eq (by unfold configurationStepConstant; ring)

theorem model_gradient_deviation {m : ℕ} (hm : 2 ≤ m) (β : ℂ) (u : ℕ → ℂ)
    (hb : PointwiseBounds (m := m) (by omega) β u)
    (hθ : ∀ j, |normalizedAngle m u j| ≤ 1 / (1000 * (2 * m : ℝ)))
    (hsmall : configurationStepConstant / (2 * m : ℝ) ≤ 1 / 2) :
    gradientDeviation (normalizedPoint m β u) ≤
      2 * (configurationStepConstant / (2 * m : ℝ)) * (1 + Real.log (2 * m : ℝ)) := by
  have he := gradientDeviation_of_step (show 4 ≤ 2 * m by omega) (normalizedPoint m β u)
    (δ := configurationStepConstant / (2 * m : ℝ)) (div_nonneg configurationStepConstant_nonneg (by positivity)) hsmall
  simp only [Nat.cast_mul, Nat.cast_ofNat] at he
  apply he
  intro j
  exact (model_configuration_step (by omega) β u hb hθ j).trans_eq (by ring)

end
end StructuralNote.MatchingActivityRadialGradient
