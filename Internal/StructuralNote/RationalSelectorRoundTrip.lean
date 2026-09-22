import StructuralNote.CommonRationalSelectorComplete

/-! The explicit inverse chart is a genuine left inverse on the rational
small window, so the two selector descriptions preserve every parameter. -/

namespace StructuralNote.RationalSelectorRoundTrip

open Erdos1045.EventualExact LensClosure CommonFiberGeometry CommonRationalChart
open RationalCommonConfiguration
open scoped BigOperators
noncomputable section

theorem angle_zero {m : ℕ} (hm : 0 < m) (X : RationalConfiguration.Variables m → ℝ) :
    RationalAngleBranch.angle hm X 0 = 0 := by
  simp [RationalAngleBranch.angle, RationalConfiguration.angleParameter]

theorem initialAngle_theta {m : ℕ} (hm : 0 < m) (X : RationalConfiguration.Variables m → ℝ) :
    initialAngle hm (theta hm X) = -angleMean hm X := by
  simp only [initialAngle, theta, angle_zero, zero_sub]

theorem relativeAngle_theta {m : ℕ} (hm : 0 < m) (X : RationalConfiguration.Variables m → ℝ) (j : Fin m) :
    relativeAngle hm (theta hm X) j = RationalAngleBranch.angle hm X j := by
  rw [relativeAngle, initialAngle_theta]
  change RationalAngleBranch.angle hm X j - angleMean hm X - -angleMean hm X = _
  ring

theorem relativeAverage_theta {m : ℕ} (hm : 0 < m) (X : RationalConfiguration.Variables m → ℝ) (j : Fin m) :
    relativeAverage hm (theta hm X) j =
      (RationalAngleBranch.angle hm X j + RationalAngleBranch.angle hm X (j.val + 1)) / 2 := by
  rw [relativeAverage, initialAngle_theta]
  unfold CommonClosureEnergy.angleAverage
  simp only [theta]
  rw [successor_half_val hm j]
  simp only [CommonClosureEnergy.halfIndex]
  ring

theorem lensUnit_tangential {m : ℕ} (hm : 2 ≤ m) (σ : Fin m → ℝ)
    (X : RationalConfiguration.Variables m → ℝ) (hX : RationalAngleBranch.SmallWindow X)
    (j : Fin m) (hs : σ j ^ 2 = 1) :
    lensUnit (σ j) (RationalAngleBranch.tangential (by omega) σ X j) =
      unit (RationalAngleBranch.crossingOffset (by omega) X j) := by
  have hh := RationalAngleBranch.positive_height hs
    (RationalAngleBranch.crossingOffset_cos_pos hm X hX j).le
  apply Complex.ext
  · change Lens.height (σ j * (2 * Real.sin (RationalAngleBranch.crossingOffset (by omega) X j))) / 2 = _
    rw [hh, unit_re]
    ring
  · change σ j * (σ j * (2 * Real.sin (RationalAngleBranch.crossingOffset (by omega) X j))) / 2 = _
    rw [unit_im]
    calc
      _ = σ j ^ 2 * Real.sin (RationalAngleBranch.crossingOffset (by omega) X j) := by ring
      _ = _ := by rw [hs, one_mul]

theorem crossingRelative_recovered {m : ℕ} (hm : 2 ≤ m) (σ : Fin m → ℝ)
    (X : RationalConfiguration.Variables m → ℝ) (hX : RationalAngleBranch.SmallWindow X)
    (j : Fin m) (hs : σ j ^ 2 = 1) :
    crossingRelative (by omega) (theta (by omega) X) (recoveredVector (by omega) σ X) σ
      (recoveredCorrection (by omega) σ X) j = RationalChart.rotation (RationalConfiguration.crossingParameter X j) := by
  rw [crossingRelative, recovered_height hm σ X, relativeAverage_theta,
    lensUnit_tangential hm σ X hX j hs, ← unit_add, RationalAngleBranch.rotation_eq_unit_arctan]
  congr 1
  unfold RationalAngleBranch.crossingOffset
  ring

theorem parameters_recovered {m : ℕ} (hm : 2 ≤ m) (σ : Fin m → ℝ)
    (X : RationalConfiguration.Variables m → ℝ) (hX : RationalAngleBranch.SmallWindow X)
    (hs : ∀ j, σ j ^ 2 = 1) :
    parameters (by omega) (theta (by omega) X) (recoveredVector (by omega) σ X) σ
      (recoveredCorrection (by omega) σ X) = X := by
  funext i
  cases i with
  | inl k =>
    change Real.tan (relativeAngle (by omega) (theta (by omega) X) ⟨k.val + 1, by omega⟩ / 2) = X (.inl k)
    rw [relativeAngle_theta]
    unfold RationalAngleBranch.angle
    simp only [Nat.mod_eq_of_lt (show k.val + 1 < m by omega)]
    have he : 2 * Real.arctan (RationalConfiguration.angleParameter X ⟨k.val + 1, by omega⟩) / 2 =
        Real.arctan (RationalConfiguration.angleParameter X ⟨k.val + 1, by omega⟩) := by ring
    rw [he, Real.tan_arctan]
    simp only [RationalConfiguration.angleParameter, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, dite_false]
    congr 1
  | inr j =>
    change RationalChartInverse.parameter (crossingRelative (by omega) (theta (by omega) X)
      (recoveredVector (by omega) σ X) σ (recoveredCorrection (by omega) σ X) j) = X (.inr j)
    rw [crossingRelative_recovered hm σ X hX j (hs j), RationalChartInverse.parameter_rotation]
    rfl

end
end StructuralNote.RationalSelectorRoundTrip
