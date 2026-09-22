import StructuralNote.MatchingActivityRadialCenterError

/-! Physical-center and derotation energies at the actual normalized model,
obtained directly from the already proved pointwise estimates. -/

namespace StructuralNote.MatchingActivityRadialModelEnergy

open Erdos1045 Erdos1045.EventualExact Complex
open FiniteFourierLift FourierMultiplier SchurSpectrum LensClosure
open StrongPointwiseCoordinates StrongPointwiseSteps StrongBudgetConsequences
open ExtremalPolarCenter NormalizedPolarRepresentation
open MatchingActivityRadialStepEnergy
noncomputable section

def derotationConstant : ℝ := centerStepConstant / 1000 + centerConstant * angleConstant

theorem constants_nonneg : 0 ≤ physicalStepConstant ∧ 0 ≤ derotationConstant := by
  unfold physicalStepConstant derotationConstant centerStepConstant centerConstant angleConstant
  constructor <;> positivity

theorem model_center_sqrt_energy {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ)
    (hb : PointwiseBounds hm β u) :
    Real.sqrt (pairEnergy (by omega) (actualCenter m β u)) ≤ physicalStepConstant := by
  have hn0 : (0 : ℝ) < 2 * m := by positivity
  have he := sqrt_energy_of_step (by omega) (actualCenter m β u)
    (div_nonneg constants_nonneg.1 (sq_nonneg _)) hb.2.2.2.2.2.2
  simp only [Nat.cast_mul, Nat.cast_ofNat] at he
  exact he.trans_eq (by field_simp)

theorem model_derotation_step {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ)
    (hb : PointwiseBounds hm β u)
    (hθ : ∀ j, |normalizedAngle m u j| ≤ 1 / (1000 * (2 * m : ℝ))) (j : Fin (2 * m)) :
    ‖difference (by omega) (actualCenter m β u - polarCenter m β u) j‖ ≤
      derotationConstant / (2 * m : ℝ) ^ 3 := by
  have hc (k : Fin (2 * m)) : ‖polarCenter m β u k‖ ≤ centerConstant / (2 * m : ℝ) :=
    (norm_le_pi_norm _ k).trans hb.1
  have he := derotation_step (by omega) (normalizedAngle m u) (polarCenter m β u)
    hc hθ hb.2.2.2.2.2.1 hb.2.2.2.1 j
  have hid : (actualCenter m β u - polarCenter m β u) =
      fun k => (unit (normalizedAngle m u k) - 1) * polarCenter m β u k := by
    funext k
    change GapRigidity.circle _ * _ - _ = (unit _ - 1) * _
    change unit _ * _ - _ = (unit _ - 1) * _
    ring
  rw [hid]
  exact he.trans_eq (by unfold derotationConstant; ring)

theorem model_derotation_sqrt_energy {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ)
    (hb : PointwiseBounds hm β u)
    (hθ : ∀ j, |normalizedAngle m u j| ≤ 1 / (1000 * (2 * m : ℝ))) :
    Real.sqrt (pairEnergy (by omega) (actualCenter m β u - polarCenter m β u)) ≤
      derotationConstant / (2 * m : ℝ) := by
  have hn0 : (0 : ℝ) < 2 * m := by positivity
  have he := sqrt_energy_of_step (by omega) (actualCenter m β u - polarCenter m β u)
    (div_nonneg constants_nonneg.2 (by positivity)) (model_derotation_step hm β u hb hθ)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at he
  exact he.trans_eq (by field_simp)

end
end StructuralNote.MatchingActivityRadialModelEnergy
