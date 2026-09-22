import StructuralNote.FixedSchurNormalInnerEnergy
import StructuralNote.FixedSchurRationalWindowDomain

/-! The actual chosen center stays within O(n^-2) pair energy of the fixed
reference center on each fixed inner energy scale. -/

namespace StructuralNote.FixedSchurReferenceDisplacement

open Filter Complex Erdos1045.EventualExact FiniteBox SchurSpectrum SchurLiftBounds
open CommonClosureEnergy CommonDomainClosure FixedSchurData FixedSchurChart
open FixedSchurNormalExpansion FixedSchurNormalInnerEnergy FixedSchurInnerAngles
open FixedSchurLinear FixedSchurLiftStability FixedSchurRationalWindowEnergy
open FixedSchurRationalWindowDomain
open AngularObjectiveCurvature
open scoped BigOperators Topology
noncomputable section

def coordinateConstant (B : ℝ) : ℝ :=
  3 * normalEnergyConstant B ^ 2 + 3 * normalEnergyConstant 0 ^ 2 +
    12 * Real.pi ^ 2 * B ^ 2

def referenceConstant (B : ℝ) : ℝ := 40 * coordinateConstant B + 5 * B ^ 2

theorem coordinateConstant_nonneg (B : ℝ) : 0 ≤ coordinateConstant B := by
  unfold coordinateConstant
  positivity

theorem referenceConstant_nonneg (B : ℝ) : 0 ≤ referenceConstant B := by
  unfold referenceConstant
  have := coordinateConstant_nonneg B
  positivity

private theorem division_decay {a n : ℝ} (ha : 0 ≤ a) (hn : 1 ≤ n) :
    a / n ^ 4 ≤ a / n ^ 2 ∧ a / n ^ 3 ≤ a / n ^ 2 := by
  have hpos : 0 < n := by linarith
  constructor <;> apply div_le_div_of_nonneg_left ha (by positivity)
  · nlinarith [sq_nonneg (n ^ 2 - 1), sq_nonneg (n - 1)]
  · nlinarith [mul_nonneg (sq_nonneg n) (sub_nonneg.mpr hn)]

theorem eventual_coordinate_reference_meanSquare (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v →
      pairEnergy (by omega) (fun j => (θ j : ℂ)) + pairEnergy (by omega) v ≤
        B ^ 2 / (2 * m : ℝ) ^ 2 →
      meanSquare (coordinate (by omega) s θ v - coordinate (by omega) s 0 0) ≤
        coordinateConstant B / (2 * m : ℝ) ^ 2 := by
  filter_upwards [eventual_normal_error_meanSquare B hB,
    eventual_normal_error_meanSquare 0 (by norm_num)] with m hinner hzero
  intro hm s θ v hdom henergy
  have hn : (1 : ℝ) ≤ 2 * m := by exact_mod_cast (show 1 ≤ 2 * m by omega)
  have hn0 : (0 : ℝ) < 2 * m := by linarith
  have hzenergy : pairEnergy (by omega : 0 < 2 * m) (fun _ => ((0 : ℝ) : ℂ)) +
      pairEnergy (by omega : 0 < 2 * m) (0 : Fin (2 * m) → ℂ) ≤
      (0 : ℝ) ^ 2 / (2 * m : ℝ) ^ 2 := by
    simp [pairEnergy_eq_chord_sum]
  have he := hinner hm s θ v hdom henergy
  have he0 := hzero hm s 0 0 (zero_inDomain (by omega)) hzenergy
  let e := normalError (by omega : 0 < 2 * m) θ (coordinate (by omega) s θ v)
    (patternSign s)
  let e0 := normalError (by omega : 0 < 2 * m) 0 (coordinate (by omega) s 0 0)
    (patternSign s)
  let a : Fin (2 * m) → ℝ := fun j => -(2 * m : ℝ) / 2 * patternSign s j *
    angleDifference (by omega) θ j
  have ha : meanSquare a = (2 * m : ℝ) ^ 2 / 4 *
      meanSquare (angleDifference (by omega) θ) := by
    have hp (j : Fin (2 * m)) : a j ^ 2 =
        (2 * m : ℝ) ^ 2 / 4 * angleDifference (by omega) θ j ^ 2 := by
      rcases patternSign_is_sign s j with hj | hj <;> simp only [a, hj] <;> ring
    unfold meanSquare
    simp_rw [hp]
    rw [← Finset.mul_sum]
    ring
  have hq : coordinate (by omega) s θ v - coordinate (by omega) s 0 0 =
      fun j => e j - e0 j - a j := by
    funext j
    simp only [e, e0, a, normalError, angleDifference, Pi.zero_apply, sub_self,
      mul_zero, sub_zero, Pi.sub_apply, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hms := meanSquare_sub_sub_bound e e0 a
  rw [← hq, ha] at hms
  have hangle := angleDifference_meanSquare_le_of_joint_energy (by omega)
    θ v hB hdom henergy
  have hscaled : (2 * m : ℝ) ^ 2 / 4 *
      meanSquare (angleDifference (by omega) θ) ≤
      4 * Real.pi ^ 2 * B ^ 2 / (2 * m : ℝ) ^ 3 := by
    calc
      _ ≤ (2 * m : ℝ) ^ 2 / 4 *
          (16 * Real.pi ^ 2 * B ^ 2 / (2 * m : ℝ) ^ 5) := by
        gcongr
      _ = _ := by field_simp; ring
  have he' := (division_decay (sq_nonneg (normalEnergyConstant B)) hn).1
  have he0' := (division_decay (sq_nonneg (normalEnergyConstant 0)) hn).1
  have ha' := (division_decay (show 0 ≤ 4 * Real.pi ^ 2 * B ^ 2 by positivity) hn).2
  change meanSquare e ≤ _ at he
  change meanSquare e0 ≤ _ at he0
  calc
    _ ≤ 3 * meanSquare e + 3 * meanSquare e0 +
        3 * ((2 * m : ℝ) ^ 2 / 4 * meanSquare (angleDifference (by omega) θ)) := hms
    _ ≤ 3 * (normalEnergyConstant B ^ 2 / (2 * m : ℝ) ^ 2) +
        3 * (normalEnergyConstant 0 ^ 2 / (2 * m : ℝ) ^ 2) +
        3 * (4 * Real.pi ^ 2 * B ^ 2 / (2 * m : ℝ) ^ 2) := by
      gcongr
      · exact he.trans he'
      · exact he0.trans he0'
      · exact hscaled.trans ha'
    _ = _ := by unfold coordinateConstant; ring

theorem eventual_center_reference_energy (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v →
      pairEnergy (by omega) (fun j => (θ j : ℂ)) + pairEnergy (by omega) v ≤
        B ^ 2 / (2 * m : ℝ) ^ 2 →
      pairEnergy (by omega)
        (center (coordinate (by omega) s θ v) v - fixedReferenceCenter (by omega) s) ≤
        referenceConstant B / (2 * m : ℝ) ^ 2 := by
  filter_upwards [eventual_coordinate_reference_meanSquare B hB,
    eventual_coordinate_properties] with m hbound hprops
  intro hm s θ v hdom henergy
  have hq := (hprops hm s θ v hdom).antiperiodic
  have hq0 := (hprops hm s 0 0 (zero_inDomain (by omega))).antiperiodic
  have hanti : Antiperiodic (by omega)
      (coordinate (by omega) s θ v - coordinate (by omega) s 0 0) := by
    intro j
    simp only [Pi.sub_apply]
    rw [hq j, hq0 j]
    ring
  have hlift := canonicalLift_pairEnergy_le hm _ hanti
  have hms := hbound hm s θ v hdom henergy
  have heq : center (coordinate (by omega) s θ v) v - fixedReferenceCenter (by omega) s =
      fun j => SchurLift.canonicalLift
        (coordinate (by omega) s θ v - coordinate (by omega) s 0 0) j + v j := by
    rw [canonicalLift_sub]
    funext j
    simp only [center, fixedReferenceCenter, Pi.sub_apply, Pi.add_apply, Pi.zero_apply]
    ring
  rw [heq]
  have hyoung := pairEnergy_add_le_five_four (by omega : 0 < 2 * m)
    (SchurLift.canonicalLift (coordinate (by omega) s θ v - coordinate (by omega) s 0 0)) v
  have hv : pairEnergy (by omega) v ≤ B ^ 2 / (2 * m : ℝ) ^ 2 := by
    linarith [pairEnergy_nonneg (by omega : 0 < 2 * m) (fun j => (θ j : ℂ))]
  unfold referenceConstant
  simp only [add_div, mul_div_assoc]
  nlinarith only [hyoung, hlift, hms, hv]

end
end StructuralNote.FixedSchurReferenceDisplacement
