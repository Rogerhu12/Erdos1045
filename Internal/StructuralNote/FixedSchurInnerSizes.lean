import StructuralNote.FixedSchurChart
import StructuralNote.CommonFiberBounds
import StructuralNote.CommonFiberHessianGeometryChord
import StructuralNote.AngularDisplacementEnergy
import StructuralNote.FixedSchurDomainBounds
import StructuralNote.StrongPointwiseSteps

/-! No-log inner-scale bounds for the actual fixed-Schur center.

The input is the literal common domain together with a joint energy budget.  The
pointwise center step is obtained by splitting the fixed center into the
canonical lift and the free residual.  The resulting chord bound is then an
instance of the periodic quotient estimate.  The final eventual statement
uses the already constructed chart coordinate only to supply its norm bound;
it does not assert an actual-maximizer entry theorem.
-/

namespace StructuralNote.FixedSchurInnerSizes

open scoped BigOperators Topology

open Complex Filter
open Erdos1045 Erdos1045.EventualExact
open FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open CommonDomainClosure CommonDomainRadius CommonTangentialParameters
open CommonFiberBounds CommonFiberHessianGeometryChord
open AngularDisplacementEnergy FixedSchurData FixedSchurDomainBounds
open CommonFiberGeometry SignedPressureAngular StrongPointwiseSteps
open FixedSchurLinear FixedSchurChart GeometricRelativeRemainder

noncomputable section

theorem center_difference_le_of_joint_energy {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hdom : InDomain (by omega) θ v)
    (henergy : pairEnergy (by omega) (fun j => (θ j : ℂ)) +
        pairEnergy (by omega) v ≤ B ^ 2 / (2 * m : ℝ) ^ 2)
    (q : Fin (2 * m) → ℝ) (hq : ‖q‖ ≤ 5) (j : Fin (2 * m)) :
    ‖difference (by omega) (FixedSchurLinear.center q v) j‖ ≤
      (120 + 10 * B) / (2 * m : ℝ) ^ 2 := by
  have hθ0 := pairEnergy_nonneg (by omega) (fun k => (θ k : ℂ))
  have _hparameter : ParameterSpace (by omega) v := hdom.2.2.1
  have hve : pairEnergy (by omega) v ≤ B ^ 2 / (2 * m : ℝ) ^ 2 := by
    linarith
  have hve' : pairEnergy (by omega) v ≤ B ^ 2 / (↑(2 * m) : ℝ) ^ 2 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hve
  have hqpoint : ∀ k, |q k| ≤ 5 := by
    intro k
    have hk := norm_le_pi_norm q k
    have hk' : ‖q k‖ ≤ (5 : ℝ) := hk.trans hq
    simpa only [Real.norm_eq_abs] using hk'
  have hcan := canonical_increment_bound (show 3 ≤ 2 * m by omega) q hqpoint j
  have hv := difference_of_scaled_energy (show 0 < 2 * m by omega) v hB hve' j
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hcan hv
  have heq : difference (by omega) (FixedSchurLinear.center q v) j =
      difference (by omega) (canonicalLift q) j +
        difference (by omega) v j := by
    simp only [FixedSchurLinear.center, difference, Pi.add_apply]
    ring
  rw [heq]
  calc
    ‖difference (by omega) (canonicalLift q) j + difference (by omega) v j‖ ≤
        ‖difference (by omega) (canonicalLift q) j‖ +
          ‖difference (by omega) v j‖ := norm_add_le _ _
    _ ≤ 20 * Real.pi / (2 * m : ℝ) ^ 2 +
          10 * B / (2 * m : ℝ) ^ 2 := add_le_add hcan hv
    _ ≤ (120 + 10 * B) / (2 * m : ℝ) ^ 2 := by
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ (sq_nonneg (2 * m : ℝ))
      nlinarith [Real.pi_lt_four]

theorem center_chord_quotient_le_of_joint_energy {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hdom : InDomain (by omega) θ v)
    (henergy : pairEnergy (by omega) (fun j => (θ j : ℂ)) +
        pairEnergy (by omega) v ≤ B ^ 2 / (2 * m : ℝ) ^ 2)
    (q : Fin (2 * m) → ℝ) (hq : ‖q‖ ≤ 5)
    (p : Fin (2 * m) × Fin (2 * m)) :
    ‖quotient (FixedSchurLinear.center q v) (root (2 * m)) p‖ ≤
      (30 + 3 * B) / (2 * m : ℝ) := by
  have hstep (k : Fin (2 * m)) :
      ‖difference (by omega) (FixedSchurLinear.center q v) k‖ ≤
        (120 + 10 * B) / (2 * m : ℝ) ^ 2 :=
    center_difference_le_of_joint_energy hm θ v hB hdom henergy q hq k
  have hq' := quotient_of_step (show 0 < 2 * m by omega)
    (FixedSchurLinear.center q v)
    (by positivity : 0 ≤ (120 + 10 * B) / (2 * m : ℝ) ^ 2) hstep p.1 p.2
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hq'
  have hnR : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  calc
    ‖quotient (FixedSchurLinear.center q v) (root (2 * m)) p‖ ≤
        (2 * m : ℝ) / 4 * ((120 + 10 * B) / (2 * m : ℝ) ^ 2) := hq'
    _ = (30 + (5 / 2 : ℝ) * B) / (2 * m : ℝ) := by
      field_simp
      ring
    _ ≤ (30 + 3 * B) / (2 * m : ℝ) := by
      apply div_le_div_of_nonneg_right _ hnR.le
      linarith

theorem displacement_energy_le_of_joint_energy {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) {B : ℝ} (_hB : 0 ≤ B)
    (hdom : InDomain (by omega) θ v)
    (henergy : pairEnergy (by omega) (fun j => (θ j : ℂ)) +
        pairEnergy (by omega) v ≤ B ^ 2 / (2 * m : ℝ) ^ 2) :
    pairEnergy (by omega)
        (fun j => diameterVector θ j - root (2 * m) j) ≤
      6 * B ^ 2 / (2 * m : ℝ) ^ 2 := by
  have hv0 := pairEnergy_nonneg (by omega) v
  have hθ : pairEnergy (by omega) (fun j => (θ j : ℂ)) ≤
      B ^ 2 / (2 * m : ℝ) ^ 2 := by
    linarith
  have hd := displacement_energy (show 2 ≤ 2 * m by omega) θ hdom.2.1
  have hmul := mul_le_mul_of_nonneg_left hθ (by norm_num : (0 : ℝ) ≤ 6)
  calc
    pairEnergy (by omega)
        (fun j => diameterVector θ j - root (2 * m) j) ≤
        6 * pairEnergy (by omega) (fun j => (θ j : ℂ)) := hd
    _ ≤ 6 * (B ^ 2 / (2 * m : ℝ) ^ 2) := hmul
    _ = 6 * B ^ 2 / (2 * m : ℝ) ^ 2 := by ring

theorem eventually_chosen_inner_sizes (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ m : ℕ in atTop,
      ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
        (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
        InDomain (by omega) θ v →
        pairEnergy (by omega) (fun j => (θ j : ℂ)) +
            pairEnergy (by omega) v ≤ B ^ 2 / (2 * m : ℝ) ^ 2 →
        ‖coordinate (by omega) s θ v‖ ≤ 5 ∧
          (∀ p, ‖quotient (FixedSchurLinear.center (coordinate (by omega) s θ v) v)
              (root (2 * m)) p‖ ≤ (30 + 3 * B) / (2 * m : ℝ)) ∧
          (30 + 3 * B) / (2 * m : ℝ) ≤ 1 / 4 := by
  have hreal : Tendsto (fun m : ℕ => (2 * m : ℝ)) atTop atTop := by
    simpa only [Function.comp_def] using
      tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  have hlim : Tendsto (fun m : ℕ => (30 + 3 * B) / (2 * m : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hreal).const_mul (30 + 3 * B)
  filter_upwards [eventual_coordinate_properties,
    hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))] with m hprops hsmall
  intro hm s θ v hdom henergy
  have hp := hprops hm s θ v hdom
  have hq := hp.norm_le
  have hquot (p : Fin (2 * m) × Fin (2 * m)) :=
    center_chord_quotient_le_of_joint_energy hm θ v hB hdom henergy
      (coordinate (by omega) s θ v) hq p
  exact ⟨hq, hquot, hsmall.le⟩

end
end StructuralNote.FixedSchurInnerSizes
