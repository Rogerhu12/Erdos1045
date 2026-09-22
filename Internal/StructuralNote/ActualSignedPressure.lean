import StructuralNote.ActualCrossingGeometry

/-! Signed pressure for the actual diameter coordinates, with the crossing hypotheses discharged. -/

noncomputable section
open scoped BigOperators Topology

namespace StructuralNote.ActualSignedPressure

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization
open FourierMultiplier FiniteFourierLift ExtremalPolarCenter NormalizedPolarRepresentation
open SignedCrossingPressure SignedPressureRemainder ActualCrossingGeometry ActualSignedAngular
open PolarAngleControl PolarRepresentation

theorem model_finite_pressure {m : ℕ} (hm : 0 < m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hz : DiameterAtMost 2 z)
    (hb : ∀ j, radialDeficit m β u j + radialDeficit m β u (finRotate (2 * m) j) ≤ 1 / 2)
    (hφ : ∀ j, |Real.pi / (2 * m) +
      (normalizedAngle m u (successor (by omega) j) - normalizedAngle m u j) / 2| ≤ 1 / 2)
    {G : ℝ} (hG : ‖operator (2 * m) (polarConstraint hm β u)‖ ≤ G) :
    normalizedBoxEnergy (operator (2 * m)) (polarConstraint hm β u) ≤ FiniteBox.B hm +
      G / ((2 * m) * Real.sin (Real.pi / (2 * m))) * radialMass m β u +
      actualAngularSum hm β u + actualRemainder hm β u := by
  have hb0 (j : Fin (2 * m)) : 0 ≤ radialDeficit m β u j :=
    sub_nonneg.mpr (model_radius_le_one hm h hz j)
  have hcross := actual_rotated_crossing hm h hz
  have hg (j : Fin (2 * m)) : |operator (2 * m) (polarConstraint hm β u) j| ≤ G := by
    have hh := norm_le_pi_norm (operator (2 * m) (polarConstraint hm β u)) j
    rw [Real.norm_eq_abs] at hh
    exact hh.trans hG
  have hp := finite_signed_pressure (show 2 ≤ 2 * m by omega) (finRotate (2 * m))
    (fun j => normalizedAngle m u (successor (by omega) j) - normalizedAngle m u j)
    (radialDeficit m β u) (operator (2 * m) (polarConstraint hm β u))
    (fun j => rotatedCenter m β u j j)
    (fun j => rotatedCenter m β u j (successor (by omega) j)) hb0 hb
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hφ)
    (fun j => by simpa only [finRotate_eq_successor (show 2 ≤ 2 * m by omega), Nat.cast_mul, Nat.cast_ofNat] using (hcross j).1)
    (fun j => by simpa only [finRotate_eq_successor (show 2 ≤ 2 * m by omega), Nat.cast_mul, Nat.cast_ofNat] using (hcross j).2) hg
  have hn (j : Fin (2 * m)) : normalComponent (2 * m) (Real.pi / ((2 * m : ℕ) : ℝ))
      (rotatedCenter m β u j j) (rotatedCenter m β u j (successor (by omega) j)) =
      polarConstraint hm β u j := by
    rw [rotatedCenter, rotatedCenter, normalComponent_eq_normal (by omega)]
    exact congrFun (ActualPressureGap.polarConstraint_eq_normal hm β u).symm j
  simp_rw [hn] at hp
  have hs := PressureSupport.box_support hm (polarConstraint hm β u)
  simp only [finitePairing] at hs
  have ha : actualAngularSum hm β u =
      (Real.pi / (2 * m)) / (2 * Real.sin (Real.pi / (2 * m))) *
        (∑ j, |operator (2 * m) (polarConstraint hm β u) j| *
          (normalizedAngle m u (successor (by omega) j) - normalizedAngle m u j)) +
      (1 / (4 * Real.sin (Real.pi / (2 * m)))) *
        (∑ j, operator (2 * m) (polarConstraint hm β u) j *
          (rotatedCenter m β u j (successor (by omega) j) + rotatedCenter m β u j j).im *
          (normalizedAngle m u (successor (by omega) j) - normalizedAngle m u j)) := by
    simp only [actualAngularSum, actual_tangentialSum hm β u]
  rw [ha]
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hp hs
  unfold actualRemainder radialMass
  linarith only [hp, hs]

theorem model_small_crossing_parameters {m : ℕ} (hm : 8 ≤ m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hη : η ≤ 1 / 1024)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (hJ : objective (regular (2 * m)) - objective (z ∘ σ) ≤ 33 * Real.pi ^ 2 / 256)
    (hS : sizeBudget (2 * m) ≤ 1 / 256)
    (hN : 512 * Real.pi ^ 2 / (2 * m) ≤ 1 / 2) :
    (∀ j, radialDeficit m β u j + radialDeficit m β u (finRotate (2 * m) j) ≤ 1 / 2) ∧
    (∀ j, |Real.pi / (2 * m) +
      (normalizedAngle m u (successor (by omega) j) - normalizedAngle m u j) / 2| ≤ 1 / 2) := by
  have hE := model_energy_le (show 4 ≤ 2 * m by omega) h hη hJ
  have hp := model_polar_bounds (show 2 ≤ m by omega) h hE (by linarith)
  have hb0 (j : Fin (2 * m)) : 0 ≤ radialDeficit m β u j :=
    sub_nonneg.mpr (model_radius_le_one (by omega) h hz.1 j)
  have ht := (ExtremalScaleBound.model_matching_deficit_bound (show 2 ≤ m by omega)
    h (by linarith) hz hE).2.2
  simp_rw [model_matching_norm (by omega) h] at ht
  change radialMass m β u ≤ 256 * Real.pi ^ 2 at ht
  have hn : (0 : ℝ) < 2 * m := by positivity
  have hb (j : Fin (2 * m)) : radialDeficit m β u j ≤ 256 * Real.pi ^ 2 / (2 * m) := by
    apply (le_div_iff₀ hn).2
    have hh := Finset.single_le_sum (s := Finset.univ) (f := radialDeficit m β u)
      (fun k _ => hb0 k) (Finset.mem_univ j)
    have hh' := mul_le_mul_of_nonneg_left hh hn.le
    unfold radialMass at ht
    linarith only [ht, hh']
  have ha (j : ℕ) : |angle m u j| ≤ 1 / 8 := by
    have hs := Real.sq_sqrt (sizeBudget_nonneg (show 1 ≤ 2 * m by omega))
    have hr : Real.sqrt (sizeBudget (2 * m)) ≤ 1 / 16 := by
      nlinarith [Real.sqrt_nonneg (sizeBudget (2 * m))]
    nlinarith [hp.angle_size j, abs_nonneg (angle m u j)]
  constructor
  · intro j
    calc
      _ ≤ 256 * Real.pi ^ 2 / (2 * m) + 256 * Real.pi ^ 2 / (2 * m) :=
        add_le_add (hb j) (hb (finRotate (2 * m) j))
      _ = 512 * Real.pi ^ 2 / (2 * m) := by ring
      _ ≤ _ := hN
  · intro j
    have hd : |normalizedAngle m u (successor (by omega) j) - normalizedAngle m u j| ≤ 1 / 4 := by
      simp only [normalizedAngle, rawAngle, sub_sub_sub_cancel_right]
      exact (abs_sub _ _).trans (by linarith [ha j, ha (successor (by omega) j)])
    have hpi : Real.pi / (2 * m) ≤ (1 : ℝ) / 4 := by
      apply (div_le_iff₀ hn).2
      have hmR : (8 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith [Real.pi_lt_four]
    calc
      _ ≤ |Real.pi / (2 * m)| +
        |(normalizedAngle m u (successor (by omega) j) - normalizedAngle m u j) / 2| := abs_add_le _ _
      _ = Real.pi / (2 * m) +
        |normalizedAngle m u (successor (by omega) j) - normalizedAngle m u j| / 2 := by
          rw [abs_of_pos (by positivity : 0 < Real.pi / (2 * m)), abs_div,
            abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ _ := by linarith

end StructuralNote.ActualSignedPressure
