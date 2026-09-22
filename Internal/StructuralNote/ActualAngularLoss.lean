import StructuralNote.PolarChordControl

/-! The angular loss for actual normalized extremal coordinates, with all path geometry proved. -/

noncomputable section
open scoped BigOperators Topology

namespace StructuralNote.ActualAngularLoss

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization Filter
open PolarAngleControl PolarRepresentation PolarCenterEnergy PolarCenterNormalization
open NormalizedPolarRepresentation ExtremalPolarCenter
open GeometricRelativeRemainder SignedPressureAngular PolarChordControl AngularPathGeometry
open AngularObjectiveCurvature SchurSpectrum DiscreteEnergy

def coordinateBudget (n : ℕ) (η : ℝ) : ℝ :=
  6 * η + 6 * Real.sqrt (sizeBudget n) +
    2 * Real.sqrt (sizeBudget n) * (4 * η + 2 * Real.sqrt (sizeBudget n))

theorem coordinateBudget_tendsto {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {η : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun k => coordinateBudget (N k) (η k)) atTop (𝓝 0) := by
  have hs : Tendsto (fun k => Real.sqrt (sizeBudget (N k))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp (sizeBudget_tendsto hN)
  simpa only [coordinateBudget, mul_zero, add_zero] using
    ((hη.const_mul 6).add (hs.const_mul 6)).add ((hs.const_mul 2).mul ((hη.const_mul 4).add (hs.const_mul 2)))

theorem model_coordinate_bounds {m : ℕ} (hm : 2 ≤ m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (hmodel : NormalizedRelativeEdgeModel z σ α β u η) (hp : PolarBounds m u η)
    (hβ : ‖β‖ ≤ 1) (hs : sizeBudget (2 * m) ≤ 1 / 16) :
    ‖polarCenter m β u‖ ≤ coordinateBudget (2 * m) η ∧
      ‖normalizedAngle m u‖ ≤ coordinateBudget (2 * m) η ∧
      (∀ p, ‖quotient (polarCenter m β u) (root (2 * m)) p‖ ≤ coordinateBudget (2 * m) η) ∧
      ∀ p, ‖quotient (fun j => (normalizedAngle m u j : ℂ)) (root (2 * m)) p‖ ≤ coordinateBudget (2 * m) η := by
  have hη0 := hmodel.error_nonneg
  have hS := Real.sqrt_nonneg (sizeBudget (2 * m))
  have hθhalf : ‖angles m u‖ ≤ 1 / 2 := by
    have hh := angles_size (by omega) u hp
    nlinarith [norm_nonneg (angles m u)]
  have hCsize : ‖ExtremalPolarCenter.physicalCenter m β u‖ ≤ Real.sqrt (sizeBudget (2 * m)) :=
    Real.le_sqrt_of_sq_le (physicalCenter_size (by omega) hβ u hp)
  have hC := correctedCenter_norm_le (show 0 < 2 * m by omega) (angles m u)
    (ExtremalPolarCenter.physicalCenter m β u) hθhalf
    (physicalCenter_mean_zero (by omega) β u hmodel.periodic hmodel.mean_zero)
  change ‖polarCenter m β u‖ ≤ 2 * ‖ExtremalPolarCenter.physicalCenter m β u‖ at hC
  have hθsize : ‖angles m u‖ ≤ 2 * Real.sqrt (sizeBudget (2 * m)) := by
    have hh := Real.le_sqrt_of_sq_le (angles_size (by omega) u hp)
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)] at hh
    norm_num at hh
    exact hh
  have hθ := normalizedAngle_norm_le (show 0 < m by omega) u
  change ‖normalizedAngle m u‖ ≤ 2 * ‖angles m u‖ at hθ
  have hprod : 0 ≤ 2 * Real.sqrt (sizeBudget (2 * m)) *
      (4 * η + 2 * Real.sqrt (sizeBudget (2 * m))) := by positivity
  unfold coordinateBudget
  refine ⟨by linarith only [hC, hCsize, hprod, hS, hη0],
    by linarith only [hθ, hθsize, hprod, hS, hη0], ?_, ?_⟩
  · intro p
    have hb := model_center_quotient hm hmodel hp hβ hs p
    linarith only [hb, hS, hη0]
  · intro p
    have he : quotient (fun j => (normalizedAngle m u j : ℂ)) (root (2 * m)) p =
        quotient (fun j => (rawAngle m u j : ℂ)) (root (2 * m)) p := by
      simp only [quotient, normalizedAngle, ofReal_sub]
      congr 1
      ring
    rw [he]
    have hb := model_angle_quotient hm hmodel hp p
    linarith only [hb, hprod, hS, hη0]

theorem eventual_model_angular_loss {M : ℕ → ℕ} (hM : Tendsto M atTop atTop)
    {η : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0)) :
    ∀ᶠ k in atTop, ∀ (z : Points (2 * M k)) (σ : Equiv.Perm (Fin (2 * M k)))
      (α β : ℂ) (u : ℕ → ℂ) (hm : 0 < M k),
      NormalizedRelativeEdgeModel z σ α β u (η k) → ExtremalNormalization.DiameterExtremal z →
      ExtremalEnergyBound.totalEnergy (2 * M k) u ≤ 32 * Real.pi ^ 2 →
      angularLogDiscriminant (normalizedAngle (M k) u)
        (configuration (root (2 * M k)) (polarCenter (M k) β u)) 1 ≤
      angularLogDiscriminant (normalizedAngle (M k) u)
        (configuration (root (2 * M k)) (polarCenter (M k) β u)) 0 +
        8 * Real.sqrt (AntipodalLog.fourthEnergy (2 * M k) (periodize (by omega) (polarCenter (M k) β u)) +
          ‖polarCenter (M k) β u‖ ^ 2 * pairEnergy (by omega) (polarCenter (M k) β u)) *
            Real.sqrt (realEnergy (by omega) (normalizedAngle (M k) u)) -
        realEnergy (by omega) (normalizedAngle (M k) u) / 2 := by
  have hN : Tendsto (fun k => 2 * M k) atTop atTop := tendsto_atTop_mono (fun _ => by omega) hM
  filter_upwards [hM.eventually_ge_atTop 2,
    hη.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 4),
    (sizeBudget_tendsto hN).eventually_le_const (by norm_num : (0 : ℝ) < 1 / 16),
    (coordinateBudget_tendsto hN hη).eventually_le_const (by norm_num : (0 : ℝ) < 1 / 512)] with k hm2 he hs hsmall
  intro z σ α β u hm hmodel hz hE
  have hp := model_polar_bounds hm2 hmodel hE (hs.trans (by norm_num))
  have hb := ExtremalScaleBound.model_matching_deficit_bound hm2 hmodel he hz hE
  have hcoords := model_coordinate_bounds hm2 hmodel hp hb.1 hs
  have hc := correctedCenter_halfPeriodic hm (angles (M k) u) (ExtremalPolarCenter.physicalCenter (M k) β u)
    (angles_halfPeriodic hm u hmodel.periodic) (physicalCenter_halfPeriodic hm β u hmodel.periodic)
  apply angular_loss_of_coordinate_bounds hm (polarCenter (M k) β u) (normalizedAngle (M k) u)
    hc (normalizedAngle_halfPeriodic hm u hmodel.periodic) _ hsmall hcoords.1 hcoords.2.1 hcoords.2.2.1 hcoords.2.2.2
  unfold coordinateBudget
  have := hmodel.error_nonneg
  positivity

end StructuralNote.ActualAngularLoss
