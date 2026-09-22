import StructuralNote.ActualSignedPressure
import StructuralNote.PressureAngularAbsorption

/-! Actual finite pressure with fixed positive losses after all remainder absorption. -/

noncomputable section
open scoped BigOperators Topology

namespace StructuralNote.ActualPressureAbsorption

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization Filter
open SchurSpectrum SchurLiftBounds DiscreteEnergy FourierMultiplier ExtremalPolarCenter NormalizedPolarRepresentation
open SignedCrossingPressure SignedPressureRemainder ActualSignedAngular ActualSignedPressure
open PressureAngularAbsorption StrongObjectiveEstimate PolarAngleControl

def pressureConstant : ℝ := angularConstant + 9 * (31 * Real.pi / 64) * Real.pi ^ 4 / 4

theorem model_pressure_absorbed {m : ℕ} (hm : 8 ≤ m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hη : η ≤ 1 / 1024)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (hJ : objective (regular (2 * m)) - objective (z ∘ σ) ≤ 33 * Real.pi ^ 2 / 256)
    (hc : CenterBounds (m := m) (by omega) β u)
    (herr : meanSquare (polarConstraint (by omega) β u - ExtremalSchurGap.evenConstraint m u) ≤
      Real.pi ^ 2 / 2048)
    (hG : ‖operator (2 * m) (polarConstraint (by omega) β u)‖ ≤ 31 * Real.pi / 64)
    (hS : sizeBudget (2 * m) ≤ 1 / 256)
    (hN : 512 * Real.pi ^ 2 / (2 * m) ≤ 1 / 2)
    (hE : 4 * (31 * Real.pi / 64) * Real.pi ^ 2 / (2 * m) ≤ 1 / 16)
    (hR : radialErrorCoefficient (2 * m) (31 * Real.pi / 64) ≤ 1 / 8)
    (hD : residualCoefficient (2 * m) ≤ 1 / 256) :
    normalizedBoxEnergy (operator (2 * m)) (polarConstraint (by omega) β u) ≤
      FiniteBox.B (by omega : 0 < m) + 5 * radialMass m β u / 8 +
        residualEnergy (by omega) (polarCenter m β u) / 256 +
        realEnergy (by omega) (normalizedAngle m u) / 8 +
        pressureConstant / (2 * m : ℝ) ^ 2 := by
  have hsmall := model_small_crossing_parameters hm h hη hz hJ hS hN
  have hp := model_finite_pressure (show 0 < m by omega) h hz.1 hsmall.1 hsmall.2 hG
  have ha := model_angular_sum_le (show 2 ≤ m by omega) h hη hJ hc herr hG
  have hmass := model_constraint_mass (show 2 ≤ m by omega) h hη hJ herr
  have hy := angular_budget_absorption (show 3 ≤ 2 * m by omega)
    (polarCenter m β u) (polarConstraint (by omega) β u) (normalizedAngle m u)
    hc.mean_zero hmass hc.energy
  have hr := model_remainder_le hm h hη hz hJ hc (hS.trans (by norm_num)) hG
  have hτ : 0 ≤ radialMass m β u := by
    unfold radialMass
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun j _ => sub_nonneg.mpr
      (PolarRepresentation.model_radius_le_one (by omega) h hz.1 j)
  have hrad := radial_price_le_half (show 16 ≤ 2 * m by omega)
    (le_refl (31 * Real.pi / 64)) hτ
  have hmulD := mul_le_mul_of_nonneg_right hD
    (pairEnergy_nonneg (show 0 < 2 * m by omega)
      (polarCenter m β u - SchurLift.canonicalLift (polarConstraint (by omega) β u)))
  have hmulE := mul_le_mul_of_nonneg_right hE
    (pairEnergy_nonneg (show 0 < 2 * m by omega) (fun j => (normalizedAngle m u j : ℂ)))
  have hmulR := mul_le_mul_of_nonneg_right hR hτ
  simp only [actualAngularBudget, Nat.cast_mul, Nat.cast_ofNat] at ha hy hrad hmulD hmulE
  unfold residualEnergy
  simp only [radialErrorCoefficient, Nat.cast_mul, Nat.cast_ofNat] at hmulR
  have hcst : angularConstant / (2 * m : ℝ) ^ 2 +
      9 * (31 * Real.pi / 64) * Real.pi ^ 4 / (4 * (2 * m : ℝ) ^ 2) =
      pressureConstant / (2 * m : ℝ) ^ 2 := by unfold pressureConstant; ring
  change 4 * (31 * Real.pi / 64) * Real.pi ^ 2 / (2 * m) *
    realEnergy (by omega) (normalizedAngle m u) ≤
      1 / 16 * realEnergy (by omega) (normalizedAngle m u) at hmulE
  dsimp only [polarConstraint] at hp ha hy hr hmulD ⊢
  linarith only [hp, ha, hy, hr, hrad, hmulD, hmulE, hmulR, hcst]

theorem eventual_model_pressure_absorbed {M : ℕ → ℕ} (hM : Tendsto M atTop atTop) :
    ∀ᶠ k in atTop, ∀ (z : Points (2 * M k)) (σ : Equiv.Perm (Fin (2 * M k)))
      (α β : ℂ) (u : ℕ → ℂ) (η : ℝ) (hm : 0 < M k),
      NormalizedRelativeEdgeModel z σ α β u η → η ≤ 1 / 1024 →
      ExtremalNormalization.DiameterExtremal z →
      objective (regular (2 * M k)) - objective (z ∘ σ) ≤ 33 * Real.pi ^ 2 / 256 →
      CenterBounds hm β u →
      meanSquare (polarConstraint hm β u - ExtremalSchurGap.evenConstraint (M k) u) ≤ Real.pi ^ 2 / 2048 →
      ‖operator (2 * M k) (polarConstraint hm β u)‖ ≤ 31 * Real.pi / 64 →
      normalizedBoxEnergy (operator (2 * M k)) (polarConstraint hm β u) ≤
        FiniteBox.B hm + 5 * radialMass (M k) β u / 8 +
          residualEnergy (by omega) (polarCenter (M k) β u) / 256 +
          realEnergy (by omega) (normalizedAngle (M k) u) / 8 +
          pressureConstant / (2 * M k : ℝ) ^ 2 := by
  have hN : Tendsto (fun k => 2 * M k) atTop atTop := tendsto_atTop_mono (fun _ => by omega) hM
  have hb := ((tendsto_const_div_atTop_nhds_zero_nat (512 * Real.pi ^ 2)).comp hN).eventually_le_const
    (by norm_num : (0 : ℝ) < 1 / 2)
  have he := ((tendsto_const_div_atTop_nhds_zero_nat (4 * (31 * Real.pi / 64) * Real.pi ^ 2)).comp hN).eventually_le_const
    (by norm_num : (0 : ℝ) < 1 / 16)
  filter_upwards [hM.eventually_ge_atTop 8,
    (sizeBudget_tendsto hN).eventually_le_const (by norm_num : (0 : ℝ) < 1 / 256), hb, he,
    (radialErrorCoefficient_tendsto hN (31 * Real.pi / 64)).eventually_le_const (by norm_num : (0 : ℝ) < 1 / 8),
    (residualCoefficient_tendsto hN).eventually_le_const (by norm_num : (0 : ℝ) < 1 / 256)]
    with k hm8 hs hb he hr hd
  intro z σ α β u η hm h hη hz hJ hc herr hG
  exact model_pressure_absorbed hm8 h hη hz hJ hc herr hG hs
    (by simpa only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat] using hb)
    (by simpa only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat] using he) hr hd

end StructuralNote.ActualPressureAbsorption
