import StructuralNote.StrongPointwiseCoordinates
import StructuralNote.CommonFiberNonlocalFrames

/-! A sharp radial projection bound before matching saturation. -/

noncomputable section
open scoped BigOperators Topology

namespace StructuralNote.StrongPointwiseRadial

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization Filter GapRigidity
open SchurSpectrum SchurLift DiscreteEnergy FiniteFourierLift
open ExtremalPolarCenter NormalizedPolarRepresentation SignedPressureRemainder StrongObjectiveEstimate
open SinglePressureEstimate StrongBudgetConsequences StrongPointwiseCoordinates ActualCrossingGeometry
open SignedCrossingPressure CommonFiberNonlocalFrames CommonFiberNonlocalProjection

theorem direct_crossing_projection {a η b₀ b₁ : ℝ} {c₀ c₁ : ℂ}
    (hb : 0 ≤ b₀ + b₁)
    (hp : ‖radialSum a η b₀ b₁ + centerStep η c₀ c₁‖ ≤ 2)
    (hm : ‖radialSum a η b₀ b₁ - centerStep η c₀ c₁‖ ≤ 2) :
    |(centerStep η c₀ c₁).re| ≤ b₀ + b₁ + (a + η / 2) ^ 2 := by
  have hp' := (re_le_norm (radialSum a η b₀ b₁ + centerStep η c₀ c₁)).trans hp
  have hm' := (re_le_norm (radialSum a η b₀ b₁ - centerStep η c₀ c₁)).trans hm
  simp only [add_re, sub_re, radialSum_re] at hp' hm'
  have hcos := Real.one_sub_sq_div_two_le_cos (x := a + η / 2)
  have hmul := mul_le_mul_of_nonneg_left (Real.cos_le_one (a + η / 2)) hb
  apply abs_le.mpr
  constructor <;> nlinarith only [hp', hm', hcos, hmul]

theorem radial_actual_difference {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ) (j : Fin (2 * m)) :
    radial (meanFrame (by omega) (normalizedAngle m u) j)
      (difference (by omega) (actualCenter m β u) j) =
      (centerStep (normalizedAngle m u (successor (by omega) j) - normalizedAngle m u j)
        (rotatedCenter m β u j j) (rotatedCenter m β u j (successor (by omega) j))).re := by
  have hconj (x : ℝ) : (starRingEnd ℂ) (circle x) = circle (-x) := by
    apply Complex.ext <;> simp [circle, Complex.exp_re, Complex.exp_im]
  have he : (starRingEnd ℂ) (meanFrame (by omega) (normalizedAngle m u) j) =
      circle (-(ActualCrossingGeometry.midpoint (2 * m) j +
        (normalizedAngle m u j + normalizedAngle m u (successor (by omega) j)) / 2)) := by
    rw [meanFrame, frame_circle]
    change (starRingEnd ℂ) (circle _ * circle _) = _
    rw [circle_mul, hconj]
    rfl
  rw [radial, he]
  change (circle _ * (circle (normalizedAngle m u (successor (by omega) j)) *
    polarCenter m β u (successor (by omega) j) - circle (normalizedAngle m u j) * polarCenter m β u j)).re = _
  rw [rotate_actual_center]
  simp only [rotatedCenter, conj_frame_circle]

def radialErrorConstant : ℝ := 2 * budgetConstant + Real.pi * angleConstant + angleConstant ^ 2 / 4

theorem projection_error_scale {n η : ℝ} (hn : 1 ≤ n)
    (hη : |η| ≤ angleConstant / n ^ 2) :
    2 * budgetConstant / n ^ 3 + (Real.pi / n + η / 2) ^ 2 ≤
      Real.pi ^ 2 / n ^ 2 + radialErrorConstant / n ^ 3 := by
  have hn0 : 0 < n := by linarith
  have hη2 : η ^ 2 ≤ angleConstant ^ 2 / n ^ 4 := by
    have hh := pow_le_pow_left₀ (abs_nonneg η) hη 2
    simpa only [sq_abs, div_pow, ← pow_mul] using hh
  have hpow : n ^ 3 ≤ n ^ 4 := by
    nlinarith [mul_nonneg (pow_nonneg hn0.le 3) (sub_nonneg.mpr hn)]
  have hsq := hη2.trans (div_le_div_of_nonneg_left (sq_nonneg angleConstant) (pow_pos hn0 3) hpow)
  have he : (Real.pi / n) * η ≤ (Real.pi / n) * (angleConstant / n ^ 2) :=
    mul_le_mul_of_nonneg_left ((le_abs_self η).trans hη) (by positivity)
  have he' : (Real.pi / n) * (angleConstant / n ^ 2) = Real.pi * angleConstant / n ^ 3 := by ring
  rw [he'] at he
  unfold radialErrorConstant
  simp only [div_eq_mul_inv, ← inv_pow] at hsq he ⊢
  nlinarith only [hsq, he]

theorem model_radial_bound {m : ℕ} (hm : 0 < m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hz : DiameterAtMost 2 z)
    (hbounds : PointwiseBounds hm β u) (j : Fin (2 * m)) :
    |radial (meanFrame (by omega) (normalizedAngle m u) j)
      (difference (by omega) (actualCenter m β u) j)| ≤
        Real.pi ^ 2 / (2 * m : ℝ) ^ 2 + radialErrorConstant / (2 * m : ℝ) ^ 3 := by
  have hcross := actual_rotated_crossing hm h hz j
  have hb := hbounds.2.2.1
  have hangle := hbounds.2.2.2.1 j
  have hp := direct_crossing_projection (add_nonneg (hb j).1 (hb (successor (by omega) j)).1)
    hcross.1 hcross.2
  have hbpair : radialDeficit m β u j + radialDeficit m β u (successor (by omega) j) ≤
      2 * budgetConstant / (2 * m : ℝ) ^ 3 := by
    calc
      _ ≤ budgetConstant / (2 * m : ℝ) ^ 3 + budgetConstant / (2 * m : ℝ) ^ 3 :=
        add_le_add (hb j).2 (hb (successor (by omega) j)).2
      _ = _ := by ring
  rw [radial_actual_difference hm]
  have hn1 : (1 : ℝ) ≤ 2 * m := by
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  exact hp.trans ((add_le_add hbpair le_rfl).trans (projection_error_scale hn1 hangle))

end StructuralNote.StrongPointwiseRadial
