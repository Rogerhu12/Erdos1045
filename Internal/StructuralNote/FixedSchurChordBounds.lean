import StructuralNote.FixedSchurData

/-! Chord-coordinate errors caused by a midpoint displacement and a local angle gap. -/

namespace StructuralNote.FixedSchurChordBounds

open Real
open CommonClosureEnergy
open FixedSchurData
open CommonFiberNormalProjection
noncomputable section

theorem scalar_cosine_bound (a d b : ℝ) :
    |2 * Real.cos (a + d / 2) * Real.cos b - 2 * Real.cos a| ≤
      |Real.sin a| * |d| + d ^ 2 / 4 + b ^ 2 := by
  have he : 2 * Real.cos (a + d / 2) * Real.cos b - 2 * Real.cos a =
      2 * Real.cos (a + d / 2) * (Real.cos b - 1) +
        2 * (Real.cos (a + d / 2) - Real.cos a) := by ring
  have he₂ : Real.cos (a + d / 2) - Real.cos a =
      Real.cos a * (Real.cos (d / 2) - 1) - Real.sin a * Real.sin (d / 2) := by
    rw [Real.cos_add]
    ring
  have hfirst :
      |2 * Real.cos (a + d / 2) * (Real.cos b - 1)| ≤ b ^ 2 := by
    calc
      |2 * Real.cos (a + d / 2) * (Real.cos b - 1)| =
          2 * (|Real.cos (a + d / 2)| * |Real.cos b - 1|) := by
            rw [abs_mul, abs_mul]
            norm_num
            ring
      _ ≤ 2 * (1 * (b ^ 2 / 2)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul (Real.abs_cos_le_one (a + d / 2)) (cos_zero_error b)
            (abs_nonneg _) (by norm_num)) (by norm_num)
      _ = b ^ 2 := by ring
  have hcos : |Real.cos a * (Real.cos (d / 2) - 1)| ≤ (d / 2) ^ 2 / 2 := by
    rw [abs_mul]
    simpa only [one_mul] using
      (mul_le_mul (Real.abs_cos_le_one a) (cos_zero_error (d / 2))
        (abs_nonneg _) (by norm_num))
  have hsin : |Real.sin a * Real.sin (d / 2)| ≤ |Real.sin a| * (|d| / 2) := by
    rw [abs_mul]
    calc
      |Real.sin a| * |Real.sin (d / 2)| ≤ |Real.sin a| * |d / 2| :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_abs (x := d / 2)) (abs_nonneg _)
      _ = |Real.sin a| * (|d| / 2) := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hsecond :
      |2 * (Real.cos (a + d / 2) - Real.cos a)| ≤
        |Real.sin a| * |d| + d ^ 2 / 4 := by
    have hbase :
        |Real.cos a * (Real.cos (d / 2) - 1) - Real.sin a * Real.sin (d / 2)| ≤
          |Real.cos a * (Real.cos (d / 2) - 1)| +
            |Real.sin a * Real.sin (d / 2)| := by
      calc
        |Real.cos a * (Real.cos (d / 2) - 1) - Real.sin a * Real.sin (d / 2)| =
            |Real.cos a * (Real.cos (d / 2) - 1) +
              (-Real.sin a * Real.sin (d / 2))| := by ring
        _ ≤ |Real.cos a * (Real.cos (d / 2) - 1)| +
            |-Real.sin a * Real.sin (d / 2)| := abs_add_le _ _
        _ = |Real.cos a * (Real.cos (d / 2) - 1)| +
            |Real.sin a * Real.sin (d / 2)| := by
              rw [show -Real.sin a * Real.sin (d / 2) =
                -(Real.sin a * Real.sin (d / 2)) by ring, abs_neg]
    have hsum :
        |Real.cos a * (Real.cos (d / 2) - 1)| +
            |Real.sin a * Real.sin (d / 2)| ≤
          (d / 2) ^ 2 / 2 + |Real.sin a| * (|d| / 2) := by
      exact add_le_add hcos hsin
    calc
      |2 * (Real.cos (a + d / 2) - Real.cos a)| =
          2 * |Real.cos a * (Real.cos (d / 2) - 1) -
            Real.sin a * Real.sin (d / 2)| := by
              rw [he₂, abs_mul]
              norm_num
      _ ≤ 2 * (|Real.cos a * (Real.cos (d / 2) - 1)| +
          |Real.sin a * Real.sin (d / 2)|) :=
        mul_le_mul_of_nonneg_left hbase (by norm_num)
      _ ≤ 2 * ((d / 2) ^ 2 / 2 + |Real.sin a| * (|d| / 2)) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = |Real.sin a| * |d| + d ^ 2 / 4 := by ring
  rw [he]
  calc
    |2 * Real.cos (a + d / 2) * (Real.cos b - 1) +
        2 * (Real.cos (a + d / 2) - Real.cos a)| ≤
        |2 * Real.cos (a + d / 2) * (Real.cos b - 1)| +
          |2 * (Real.cos (a + d / 2) - Real.cos a)| := abs_add_le _ _
    _ ≤ b ^ 2 + (|Real.sin a| * |d| + d ^ 2 / 4) :=
      add_le_add hfirst hsecond
    _ = |Real.sin a| * |d| + d ^ 2 / 4 + b ^ 2 := by ring

theorem actual_X_error {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (j : Fin m) :
    |FixedSchurData.X (by omega) θ (CommonClosureEnergy.halfIndex j) -
        2 * Real.cos (Real.pi / (2 * m : ℝ))| ≤
      |Real.sin (Real.pi / (2 * m : ℝ))| *
          |angleDifference (by omega) θ (CommonClosureEnergy.halfIndex j)| +
        angleDifference (by omega) θ (CommonClosureEnergy.halfIndex j) ^ 2 / 4 +
        angleAverage (by omega) θ (CommonClosureEnergy.halfIndex j) ^ 2 := by
  rw [FixedSchurData.X_halfIndex hm θ j]
  apply scalar_cosine_bound (Real.pi / (2 * m : ℝ))
    (angleDifference (by omega) θ (CommonClosureEnergy.halfIndex j))
    (angleAverage (by omega) θ (CommonClosureEnergy.halfIndex j))

end
end StructuralNote.FixedSchurChordBounds
