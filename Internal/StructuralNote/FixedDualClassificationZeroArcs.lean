import StructuralNote.FixedDualClassificationLobeGeometry
import Mathlib.Algebra.Order.ToIntervalMod

/-! The six excluded arcs are the radius 1/8 neighborhoods of the zeros of
the third harmonic. Integer centers avoid choosing a cut on the circle. -/

namespace StructuralNote.FixedDualClassificationZeroArcs

open Real Set
noncomputable section

def zeroCenter (α : ℝ) (k : ℤ) : ℝ := α + Real.pi / 6 + k * Real.pi / 3

theorem zeroCenter_add_six (α : ℝ) (k : ℤ) :
    zeroCenter α (k + 6) = zeroCenter α k + 2 * Real.pi := by
  unfold zeroCenter
  push_cast
  ring

theorem abs_sine_eq_sine_abs {u : ℝ} (hu : |u| ≤ Real.pi / 2) :
    |sin u| = sin |u| :=
  abs_sin_eq_sin_abs_of_abs_le_pi (by linarith [pi_pos])

theorem cosine_zero_distance (φ : ℝ) (k : ℤ) :
    |cos φ| = |sin (φ - (Real.pi / 2 + k * Real.pi))| := by
  have h : φ = (φ - (Real.pi / 2 + k * Real.pi) + Real.pi / 2) + k * Real.pi := by ring
  conv_lhs => rw [h, cos_add_int_mul_pi, cos_add_pi_div_two]
  simp only [abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]

theorem cosine_away_of_zero_distance {φ : ℝ}
    (haway : ∀ k : ℤ, (3 : ℝ) / 8 ≤ |φ - (Real.pi / 2 + k * Real.pi)|) :
    sin (3 / 8 : ℝ) ≤ |cos φ| := by
  let u := toIcoMod pi_pos (-(Real.pi / 2)) (φ - Real.pi / 2)
  let k := toIcoDiv pi_pos (-(Real.pi / 2)) (φ - Real.pi / 2)
  have hu := toIcoMod_mem_Ico pi_pos (-(Real.pi / 2)) (φ - Real.pi / 2)
  have he := toIcoMod_add_toIcoDiv_zsmul pi_pos (-(Real.pi / 2)) (φ - Real.pi / 2)
  change u ∈ Ico (-(Real.pi / 2)) (-(Real.pi / 2) + Real.pi) at hu
  change u + k • Real.pi = φ - Real.pi / 2 at he
  rw [zsmul_eq_mul] at he
  have heq : φ - (Real.pi / 2 + k * Real.pi) = u := by linarith
  have hub : |u| ≤ Real.pi / 2 := abs_le.mpr ⟨hu.1, by linarith [hu.2]⟩
  have hlo := haway k
  rw [heq] at hlo
  rw [cosine_zero_distance φ k, heq, abs_sine_eq_sine_abs hub]
  exact sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) hub hlo

theorem cosine_away_of_outside_arcs {α θ : ℝ}
    (haway : ∀ k : ℤ, (1 : ℝ) / 8 ≤ |θ - zeroCenter α k|) :
    sin (3 / 8 : ℝ) ≤ |cos (3 * (θ - α))| := by
  apply cosine_away_of_zero_distance
  intro k
  have he : 3 * (θ - α) - (Real.pi / 2 + k * Real.pi) =
      3 * (θ - zeroCenter α k) := by unfold zeroCenter; ring
  rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  linarith [haway k]

end
end StructuralNote.FixedDualClassificationZeroArcs
