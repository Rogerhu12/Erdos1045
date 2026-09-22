import StructuralNote.StrongObjectiveEstimate

/-! The signed crossing inequalities for the actual normalized diameter configuration. -/

noncomputable section
open scoped BigOperators

namespace StructuralNote.ActualCrossingGeometry

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization GapRigidity
open PolarRepresentation PolarCenterEnergy NormalizedPolarRepresentation ExtremalPolarCenter
open FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum AntipodalDecomposition
open SignedCrossingPressure SignedPressureRemainder SignedPressureAngular

def midpoint (n : ℕ) (j : Fin n) : ℝ := (2 * (j : ℝ) + 1) * Real.pi / n

theorem frame_circle (n : ℕ) (j : Fin n) : frame n j = circle (midpoint n j) := by
  rw [frame, midpointCharacter_eq_exp]
  simp only [Nat.cast_one, one_mul, midpoint, circle]

theorem conj_frame_circle (n : ℕ) (j : Fin n) : (starRingEnd ℂ) (frame n j) = circle (-midpoint n j) := by
  rw [frame_circle]
  apply Complex.ext <;> simp [circle, Complex.exp_re, Complex.exp_im]

theorem root_left_circle (n : ℕ) (j : Fin n) : root n j = circle (midpoint n j - Real.pi / n) := by
  have he := character_eq_exp n 1 j
  simp only [character, mul_one, Nat.cast_one] at he
  rw [root, he]
  unfold circle midpoint
  congr 2
  push_cast
  ring

theorem root_right_circle {n : ℕ} (hn : 2 ≤ n) (j : Fin n) :
    root n (successor (by omega) j) = circle (midpoint n j + Real.pi / n) := by
  rw [← finRotate_eq_successor hn, root_rotate hn, root_left_circle]
  change circle (midpoint n j - Real.pi / n) * circle (2 * Real.pi / n) = _
  rw [circle_mul]
  congr 1
  ring

def normalizedPoint (m : ℕ) (β : ℂ) (u : ℕ → ℂ) (j : Fin (2 * m)) : ℂ :=
  circle (normalizedAngle m u j) * ((radius m ‖β‖ u j : ℂ) * root (2 * m) j + polarCenter m β u j)

theorem model_diameter {m : ℕ} {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (hmodel : NormalizedRelativeEdgeModel z σ α β u η) (hz : DiameterAtMost 2 z) :
    DiameterAtMost 2 (normalizedPoint m β u) := by
  have he (j : Fin (2 * m)) : z (σ j) =
      (α + (β / (‖β‖ : ℂ)) * physicalTranslation m ‖β‖ u) +
      ((β / (‖β‖ : ℂ)) * phase (-meanAngle m u)) * normalizedPoint m β u j := by
    have hh := model_normalized_coordinates hmodel j
    rw [← ActualPressureGap.polarCenter_eq_normalizedCenter m β u] at hh
    simpa only [normalizedPoint, phase, neg_neg, root, reference, mul_assoc] using hh
  intro i j
  have hd := hz (σ i) (σ j)
  rw [he i, he j, show
    (α + (β / (‖β‖ : ℂ)) * physicalTranslation m ‖β‖ u) +
      ((β / (‖β‖ : ℂ)) * phase (-meanAngle m u)) * normalizedPoint m β u i -
    ((α + (β / (‖β‖ : ℂ)) * physicalTranslation m ‖β‖ u) +
      ((β / (‖β‖ : ℂ)) * phase (-meanAngle m u)) * normalizedPoint m β u j) =
      ((β / (‖β‖ : ℂ)) * phase (-meanAngle m u)) * (normalizedPoint m β u i - normalizedPoint m β u j) by ring,
    norm_mul, normalizedRotation_norm hmodel.scale_ne_zero, one_mul] at hd
  exact hd

theorem radius_halfTurn {m : ℕ} (hm : 0 < m) (r : ℝ) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) (j : Fin (2 * m)) :
    radius m r u (halfTurn hm j) = radius m r u j := by
  have hp := radius_periodic hm r u hu
  have hfull : Function.Periodic (radius m r u) (2 * m) := by
    intro k
    rw [show k + 2 * m = k + m + m by omega, hp, hp]
  change radius m r u ((j.val + m) % (2 * m)) = _
  rw [← CyclicAngles.periodic_mod _ hfull, hp]

theorem actual_antipodal_parts {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) (j : Fin (2 * m)) :
    oddPart (halfTurn hm) (normalizedPoint m β u) j =
      (radius m ‖β‖ u j : ℂ) * circle (normalizedAngle m u j) * root (2 * m) j ∧
    evenPart (halfTurn hm) (normalizedPoint m β u) j = circle (normalizedAngle m u j) * polarCenter m β u j := by
  have hc := PolarCenterNormalization.correctedCenter_halfPeriodic hm (angles m u)
    (ExtremalPolarCenter.physicalCenter m β u) (angles_halfPeriodic hm u hu) (physicalCenter_halfPeriodic hm β u hu)
  change HalfPeriodic hm (polarCenter m β u) at hc
  simp only [oddPart, evenPart, normalizedPoint, normalizedAngle_halfPeriodic hm u hu,
    radius_halfTurn hm ‖β‖ u hu, ActualAngularFirst.root_halfTurn hm, hc j]
  constructor <;> ring

theorem actual_rotated_crossing {m : ℕ} (hm : 0 < m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (hmodel : NormalizedRelativeEdgeModel z σ α β u η) (hz : DiameterAtMost 2 z) (j : Fin (2 * m)) :
    ‖radialSum (Real.pi / (2 * m))
        (normalizedAngle m u (successor (by omega) j) - normalizedAngle m u j)
        (radialDeficit m β u j) (radialDeficit m β u (successor (by omega) j)) +
      centerStep (normalizedAngle m u (successor (by omega) j) - normalizedAngle m u j)
        (rotatedCenter m β u j j) (rotatedCenter m β u j (successor (by omega) j))‖ ≤ 2 ∧
    ‖radialSum (Real.pi / (2 * m))
        (normalizedAngle m u (successor (by omega) j) - normalizedAngle m u j)
        (radialDeficit m β u j) (radialDeficit m β u (successor (by omega) j)) -
      centerStep (normalizedAngle m u (successor (by omega) j) - normalizedAngle m u j)
        (rotatedCenter m β u j j) (rotatedCenter m β u j (successor (by omega) j))‖ ≤ 2 := by
  let k := successor (show 0 < 2 * m by omega) j
  let θ := normalizedAngle m u
  let μ := midpoint (2 * m) j
  let a := Real.pi / ((2 * m : ℕ) : ℝ)
  have hc := diameter_cross_constraints (normalizedPoint m β u) (model_diameter hmodel hz) (halfTurn hm) j k
  rw [(actual_antipodal_parts hm β u hmodel.periodic j).1,
    (actual_antipodal_parts hm β u hmodel.periodic k).1,
    (actual_antipodal_parts hm β u hmodel.periodic j).2,
    (actual_antipodal_parts hm β u hmodel.periodic k).2,
    root_left_circle, root_right_circle (by omega)] at hc
  have hr (l : Fin (2 * m)) : (radius m ‖β‖ u l : ℂ) = (1 - radialDeficit m β u l : ℝ) := by
    unfold radialDeficit
    push_cast
    ring
  have hrad : (radius m ‖β‖ u j : ℂ) * circle (θ j) * circle (μ - a) +
      (radius m ‖β‖ u k : ℂ) * circle (θ k) * circle (μ + a) =
      ((1 - radialDeficit m β u j : ℝ) : ℂ) * circle (μ - a + θ j) +
      ((1 - radialDeficit m β u k : ℝ) : ℂ) * circle (μ + a + θ k) := by
    rw [hr j, hr k, mul_assoc, mul_assoc, circle_mul, circle_mul]
    congr 2 <;> congr 1 <;> ring
  change ‖((radius m ‖β‖ u j : ℂ) * circle (θ j) * circle (μ - a) +
      (radius m ‖β‖ u k : ℂ) * circle (θ k) * circle (μ + a)) + _‖ ≤ 2 ∧
    ‖((radius m ‖β‖ u j : ℂ) * circle (θ j) * circle (μ - a) +
      (radius m ‖β‖ u k : ℂ) * circle (θ k) * circle (μ + a)) - _‖ ≤ 2 at hc
  rw [hrad] at hc
  have hc0 : rotatedCenter m β u j j = circle (-μ) * polarCenter m β u j := by
    rw [rotatedCenter, conj_frame_circle]
  have hc1 : rotatedCenter m β u j k = circle (-μ) * polarCenter m β u k := by
    rw [rotatedCenter, conj_frame_circle]
  rw [show Real.pi / (2 * m : ℝ) = a by simp only [a, Nat.cast_mul, Nat.cast_ofNat]]
  change ‖radialSum a (θ k - θ j) (radialDeficit m β u j) (radialDeficit m β u k) +
    centerStep (θ k - θ j) (rotatedCenter m β u j j) (rotatedCenter m β u j k)‖ ≤ 2 ∧
    ‖radialSum a (θ k - θ j) (radialDeficit m β u j) (radialDeficit m β u k) -
    centerStep (θ k - θ j) (rotatedCenter m β u j j) (rotatedCenter m β u j k)‖ ≤ 2
  rw [hc0, hc1, ← rotate_actual_radial μ a (θ j) (θ k), ← rotate_actual_center μ (θ j) (θ k)]
  constructor
  · rw [← mul_add, norm_mul, circle_norm, one_mul]
    exact hc.1
  · rw [← mul_sub, norm_mul, circle_norm, one_mul]
    exact hc.2

end StructuralNote.ActualCrossingGeometry
