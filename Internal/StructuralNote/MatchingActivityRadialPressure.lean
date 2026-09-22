import StructuralNote.MatchingActivityRadialSourceSharp
import StructuralNote.HessianAcceleration

/-! The pressure cost of one actual outward radial direction has a fixed
gap below its leading gain. The closure correction only costs a constant. -/

namespace StructuralNote.MatchingActivityRadialPressure

open Erdos1045 Erdos1045.EventualExact Complex Configuration Filter
open LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open CommonClosureEnergy CommonFiberGeometry MatchingActivityRadialClosure MatchingActivityRadialPair
open MatchingActivityRadialBounds MatchingActivityRadialVelocity MatchingActivityRadialFeasible
open MatchingActivityRadialSource MatchingActivityRadialSourceSharp MatchingActivityRadialProjection
open LensIncrementDerivatives LensClosurePathDerivatives ClosedSourceIntegration
open scoped BigOperators
noncomputable section

theorem centerVelocity_halfPeriodic {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (a : ℂ) (g : (Fin m → ℝ) → ℂ) (i : Fin m)
    (hchart : IsFeasibleRadialChart hm θ σ ν r a g)
    (hpos : ∀ j, 0 < (pair (halfAngle hm θ j) (r j) (r (nextIndex hm j))).re)
    (ht : ∀ j, ν j ^ 2 < 4) :
    HalfPeriodic hm (centerVelocity hm θ σ ν r g i) := by
  apply HessianAcceleration.integral_repeat_halfPeriodic
  exact corrected_sum _ _ _ _ _ _ (actual_closure_derivative hm θ σ ν r a g i hchart hpos ht)

theorem centerVelocity_normal_sum {m : ℕ} (hm : 8 ≤ m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (a : ℂ) (g : (Fin m → ℝ) → ℂ) (i : Fin m)
    (hchart : IsFeasibleRadialChart (by omega) θ σ ν r a g)
    (hpos : ∀ j, 1 ≤ (pair (halfAngle (by omega) θ j) (r j) (r (nextIndex (by omega) j))).re)
    (hr : ∀ j, |r j| ≤ 1) (hφ : ∀ j, |halfAngle (by omega) θ j| ≤ 1 / 4)
    (hsmall : ∀ j, |radialPhase (by omega) θ r j - midpoint m j| + |ν j| ≤ 4 / (2 * m : ℝ))
    (hb : ∀ j, ‖body (radialLength (by omega) θ r j) (σ j) (ν j)‖ ≤ 1 / 4) :
    (∑ j : Fin m, |normal (midpoint m j) (difference (by omega)
      (centerVelocity (by omega) θ σ ν r g i) (CommonClosureEnergy.halfIndex j))|) ≤
        9 / 4 + 64 / (2 * m : ℝ) := by
  have hmR : (8 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hε : 4 / (2 * m : ℝ) ≤ 1 / 4 := (div_le_iff₀ (by positivity)).2 (by linarith)
  have hsmall' (j : Fin m) : |radialPhase (by omega) θ r j - midpoint m j| + |ν j| ≤ 1 / 4 := (hsmall j).trans hε
  have hν (j : Fin m) : |ν j| ≤ 1 / 4 := by linarith [hsmall' j, abs_nonneg (radialPhase (by omega) θ r j - midpoint m j)]
  have hp (j : Fin m) : 0 < (pair (halfAngle (by omega) θ j) (r j) (r (nextIndex (by omega) j))).re := lt_of_lt_of_le (by norm_num) (hpos j)
  have ht (j : Fin m) : ν j ^ 2 < 4 := by nlinarith [(abs_le.mp (hν j)).1, (abs_le.mp (hν j)).2]
  have hs := directSource_sum_sharp (by omega) θ σ ν r i hpos hr hφ hchart.1 (fun j => (hν j).trans (by norm_num)) hb
  have hv := actual_closureSpeed_le (by omega) θ σ ν r a g i hchart hpos hr hφ hsmall' (fun j => (hb j).trans (by norm_num))
  have he := actual_closure_derivative (by omega) θ σ ν r a g i hchart hp ht
  have hd := integrateCorrected_difference (by omega) _ _ _ _ _ _ he
  change difference (by omega) (centerVelocity (by omega) θ σ ν r g i) = _ at hd
  rw [hd]
  have hh := corrected_normal_sum (radialPhase (by omega) θ r) σ ν (closureSpeed r g i)
    (directSource (by omega) θ σ ν r i) hchart.1 (fun j => (hν j).trans (by norm_num)) hsmall
  have hval (j : Fin m) : BoxLensLift.repeatHalf (show 0 < m by omega)
      (corrected (radialPhase (by omega) θ r) σ ν 0 (closureSpeed r g i) (directSource (by omega) θ σ ν r i))
      (CommonClosureEnergy.halfIndex j) = corrected (radialPhase (by omega) θ r) σ ν 0
        (closureSpeed r g i) (directSource (by omega) θ σ ν r i) j :=
    CommonTangentialParameters.repeatHalf_halfIndex (by omega) _ j
  simp_rw [hval]
  have hprod := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hm0.le)
    (show 0 ≤ 4 / (2 * m : ℝ) by positivity)
  have hid : (m : ℝ) * (16 / m) * (4 / (2 * m)) = 64 / (2 * m) := by field_simp; ring
  rw [hid] at hprod
  linarith

theorem pressure_work_coefficient {m : ℕ} (hm : 8 ≤ m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (a : ℂ) (g : (Fin m → ℝ) → ℂ) (i : Fin m)
    (hchart : IsFeasibleRadialChart (by omega) θ σ ν r a g)
    (hpos : ∀ j, 1 ≤ (pair (halfAngle (by omega) θ j) (r j) (r (nextIndex (by omega) j))).re)
    (hr : ∀ j, |r j| ≤ 1) (hφ : ∀ j, |halfAngle (by omega) θ j| ≤ 1 / 4)
    (hsmall : ∀ j, |radialPhase (by omega) θ r j - midpoint m j| + |ν j| ≤ 4 / (2 * m : ℝ))
    (hb : ∀ j, ‖body (radialLength (by omega) θ r j) (σ j) (ν j)‖ ≤ 1 / 4)
    (p : Fin (2 * m) → ℝ) {G : ℝ} (hp : ∀ j, |p j| ≤ G) :
    |finitePairing p (constraint (by omega) (centerVelocity (by omega) θ σ ν r g i)) / (2 * m : ℝ)| ≤
      (9 * G / 8) * (2 * m : ℝ) + 32 * G := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmR : (8 : ℝ) ≤ m := by exact_mod_cast hm
  have hν (j : Fin m) : |ν j| ≤ 1 / 4 := by
    have hε : 4 / (2 * m : ℝ) ≤ 1 / 4 := (div_le_iff₀ (by positivity)).2 (by linarith)
    linarith [hsmall j, abs_nonneg (radialPhase (by omega) θ r j - midpoint m j)]
  have hU := centerVelocity_halfPeriodic (by omega) θ σ ν r a g i hchart
    (fun j => lt_of_lt_of_le (by norm_num) (hpos j))
    (fun j => by nlinarith [(abs_le.mp (hν j)).1, (abs_le.mp (hν j)).2])
  have hH := centerVelocity_normal_sum hm θ σ ν r a g i hchart hpos hr hφ hsmall hb
  have hsin := SignedPressureRemainder.reciprocal_sine_le (show 2 ≤ 2 * m by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hsin
  have he := pressure_work_bound (by omega) _ hU p hp hH hsin.1
  have hG : 0 ≤ G := (abs_nonneg (p ⟨0, by omega⟩)).trans (hp _)
  have hrec : 1 / Real.sin (Real.pi / (2 * m : ℝ)) ≤ (2 * m : ℝ) / 2 := by
    calc
      _ = 2 * (1 / (2 * Real.sin (Real.pi / (2 * m : ℝ)))) := by ring
      _ ≤ 2 * ((2 * m : ℝ) / 4) := mul_le_mul_of_nonneg_left hsin.2 (by norm_num)
      _ = _ := by ring
  calc
    _ ≤ G * (9 / 4 + 64 / (2 * m : ℝ)) / Real.sin (Real.pi / (2 * m : ℝ)) := he
    _ = (G * (9 / 4 + 64 / (2 * m : ℝ))) * (1 / Real.sin (Real.pi / (2 * m : ℝ))) := by ring
    _ ≤ (G * (9 / 4 + 64 / (2 * m : ℝ))) * ((2 * m : ℝ) / 2) := mul_le_mul_of_nonneg_left hrec (by positivity)
    _ = _ := by field_simp; ring

end
end StructuralNote.MatchingActivityRadialPressure
