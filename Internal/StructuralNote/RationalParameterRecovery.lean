import StructuralNote.RationalChartInverse

/-! Recovery of the n-1 base-edge rational parameters from actual half-period
angles and selected crossing unit vectors, including the small-window bound. -/

namespace StructuralNote.RationalParameterRecovery

open Erdos1045.EventualExact LensClosure RationalChartInverse
noncomputable section

def parameters {m : ℕ} (a : Fin m → ℝ) (W : Fin m → ℂ) : RationalConfiguration.Variables m → ℝ
  | .inl k => Real.tan (a ⟨k.val + 1, by omega⟩ / 2)
  | .inr j => parameter (W j)

theorem angleParameter_parameters {m : ℕ} (hm : 0 < m) (a : Fin m → ℝ) (W : Fin m → ℂ)
    (ha0 : a ⟨0, hm⟩ = 0) (j : Fin m) :
    RationalConfiguration.angleParameter (parameters a W) j = Real.tan (a j / 2) := by
  unfold RationalConfiguration.angleParameter
  split
  · have hj : j = ⟨0, hm⟩ := Fin.ext (by assumption)
    simp [hj, ha0]
  · simp only [parameters]
    congr 2
    congr 1
    apply Fin.ext
    change j.val - 1 + 1 = j.val
    omega

theorem angle_parameters {m : ℕ} (hm : 0 < m) (a : Fin m → ℝ) (W : Fin m → ℂ)
    (ha0 : a ⟨0, hm⟩ = 0) (ha : ∀ j, |a j| < Real.pi) (j : ℕ) :
    RationalAngleBranch.angle hm (parameters a W) j = a ⟨j % m, Nat.mod_lt _ hm⟩ := by
  rw [RationalAngleBranch.angle, angleParameter_parameters hm a W ha0]
  exact RationalAngleBranch.angle_inverse (ha _)

theorem diameter_parameters {m : ℕ} (hm : 0 < m) (a : Fin m → ℝ) (W : Fin m → ℂ)
    (ha0 : a ⟨0, hm⟩ = 0) (ha : ∀ j, |a j| < Real.pi) (j : ℕ) :
    RationalConfiguration.diameter hm (parameters a W) j =
      unit (Real.pi / m * j + a ⟨j % m, Nat.mod_lt _ hm⟩) := by
  rw [RationalAngleBranch.diameter_eq_unit, angle_parameters hm a W ha0 ha]

theorem crossingUnit_parameters {m : ℕ} (a : Fin m → ℝ) (W : Fin m → ℂ)
    (hW : ∀ j, ‖W j‖ = 1) (hR : ∀ j, 0 < 1 + (W j).re) (j : Fin m) :
    RationalConfiguration.crossingUnit (parameters a W) j = unit (midpoint m j) * W j := by
  change unit (midpoint m j) * RationalChart.rotation (parameter (W j)) = _
  rw [rotation_parameter (hW j) (hR j)]

theorem small_parameters {m : ℕ} (hm : 0 < m) (a : Fin m → ℝ) (W : Fin m → ℂ)
    (ha : ∀ j, |a j| < 1 / (2 * (m : ℝ)))
    (hW : ∀ j, ‖W j - 1‖ < 1 / (2 * (m : ℝ))) :
    RationalAngleBranch.SmallWindow (parameters a W) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hε : 1 / (2 * (m : ℝ)) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  intro i
  cases i with
  | inl k =>
    let j : Fin m := ⟨k.val + 1, by omega⟩
    have haj : |a j| < Real.pi := (ha j).trans (by linarith [Real.pi_gt_three])
    change |Real.tan (a j / 2)| < 1 / (2 * (m : ℝ))
    rw [← unit_parameter haj]
    apply parameter_abs_lt_of_close hε
    have hb := norm_unit_sub_le (a j) 0
    simp only [unit, Complex.ofReal_zero, zero_mul, Complex.exp_zero, sub_zero] at hb
    exact hb.trans_lt (ha j)
  | inr j => exact parameter_abs_lt_of_close hε (hW j)

end
end StructuralNote.RationalParameterRecovery
