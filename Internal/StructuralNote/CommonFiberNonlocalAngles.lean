import StructuralNote.CommonFiberNonlocalFrames

/-! Lifted angles along a cyclic interval, with exact direction identities.
Periodizing the vectors retains the full-turn and half-turn signs automatically. -/

namespace StructuralNote.CommonFiberNonlocalAngles

open Erdos1045 Erdos1045.EventualExact LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open CommonClosureEnergy CommonFiberGeometry CommonFiberNonlocalFrames
noncomputable section

def thetaNat {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) (j : ℕ) : ℝ := θ ⟨j % n, Nat.mod_lt _ hn⟩

def angleLift {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) (j : ℕ) : ℝ :=
  2 * Real.pi * j / n + thetaNat hn θ j

theorem diameter_periodize {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) (j : ℕ) :
    periodize hn (diameterVector θ) j = unit (angleLift hn θ j) := by
  change character n 1 (j % n) * unit (thetaNat hn θ j) = _
  rw [character_mod hn, angleLift, unit_add, character_eq_exp]
  simp only [Nat.cast_one, mul_one, unit]

theorem meanFrame_periodize {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) (j : ℕ) :
    periodize hn (meanFrame hn θ) j = unit ((angleLift hn θ j + angleLift hn θ (j + 1)) / 2) := by
  change (LocalPhase.phase n 1 * character n 1 (j % n)) *
    unit (angleAverage hn θ ⟨j % n, Nat.mod_lt _ hn⟩) = _
  rw [character_mod hn, midpointCharacter_eq_exp]
  have hav : angleAverage hn θ ⟨j % n, Nat.mod_lt _ hn⟩ = (thetaNat hn θ j + thetaNat hn θ (j + 1)) / 2 := by
    simp only [angleAverage, thetaNat, successor, Nat.mod_add_mod]
  rw [hav]
  simp only [Nat.cast_one, one_mul]
  change unit ((2 * j + 1) * Real.pi / n) * unit ((thetaNat hn θ j + thetaNat hn θ (j + 1)) / 2) = _
  rw [← unit_add]
  congr 1
  unfold angleLift
  push_cast
  ring

theorem half_angle_error {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) {S : ℝ}
    (hθ : ∀ i, |θ i| ≤ S) (j k : ℕ) :
    |(angleLift hn θ (j + k) - angleLift hn θ j) / 2 - Real.pi * k / n| ≤ S := by
  have he : (angleLift hn θ (j + k) - angleLift hn θ j) / 2 - Real.pi * k / n =
      (thetaNat hn θ (j + k) - thetaNat hn θ j) / 2 := by unfold angleLift; push_cast; ring
  rw [he, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hb := abs_sub_le (thetaNat hn θ (j + k)) 0 (thetaNat hn θ j)
  simp only [sub_zero, zero_sub, abs_neg] at hb
  have h₁ : |thetaNat hn θ (j + k)| ≤ S := hθ _
  have h₂ : |thetaNat hn θ j| ≤ S := hθ _
  linarith

theorem meanFrame_distance {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) {S : ℝ}
    (hθ : ∀ i, |θ i| ≤ S) (j k r : ℕ) (hr : r < k) :
    ‖unit ((angleLift hn θ j + angleLift hn θ (j + k)) / 2) -
      periodize hn (meanFrame hn θ) (j + r)‖ ≤ Real.pi * k / n + 2 * S := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hrR : (r : ℝ) + 1 ≤ k := by exact_mod_cast (show r + 1 ≤ k by omega)
  have he : (angleLift hn θ j + angleLift hn θ (j + k)) / 2 -
      (angleLift hn θ (j + r) + angleLift hn θ (j + r + 1)) / 2 =
      Real.pi / n * ((k : ℝ) - (2 * r + 1)) +
        (thetaNat hn θ j + thetaNat hn θ (j + k) - thetaNat hn θ (j + r) - thetaNat hn θ (j + r + 1)) / 2 := by
    unfold angleLift
    push_cast
    ring
  have hbase : |Real.pi / n * ((k : ℝ) - (2 * r + 1))| ≤ Real.pi * k / n := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < Real.pi / n)]
    have hab : |(k : ℝ) - (2 * r + 1)| ≤ k := by
      exact abs_le.mpr ⟨by linarith, by linarith [show (0 : ℝ) ≤ r by positivity]⟩
    have hh := mul_le_mul_of_nonneg_left hab (by positivity : 0 ≤ Real.pi / n)
    exact hh.trans_eq (by ring)
  have ht : |(thetaNat hn θ j + thetaNat hn θ (j + k) -
      thetaNat hn θ (j + r) - thetaNat hn θ (j + r + 1)) / 2| ≤ 2 * S := by
    have hh (a : ℕ) : -S ≤ thetaNat hn θ a ∧ thetaNat hn θ a ≤ S := abs_le.mp (hθ _)
    exact abs_le.mpr ⟨by linarith [(hh j).1, (hh (j + k)).1, (hh (j + r)).2, (hh (j + r + 1)).2],
      by linarith [(hh j).2, (hh (j + k)).2, (hh (j + r)).1, (hh (j + r + 1)).1]⟩
  rw [meanFrame_periodize]
  apply (norm_unit_sub_le _ _).trans
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hbase ht)

end
end StructuralNote.CommonFiberNonlocalAngles
