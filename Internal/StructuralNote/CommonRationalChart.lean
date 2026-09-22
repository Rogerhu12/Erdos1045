import StructuralNote.RationalParameterRecovery
import StructuralNote.CommonRationalWindowBounds
import StructuralNote.RationalCommonConfiguration

/-! An explicit inverse chart on common-fiber parameters. The positive square
root in the lens formula determines the selected crossing unit vector. -/

namespace StructuralNote.CommonRationalChart

open Erdos1045.EventualExact LensClosure FiniteFourierLift SchurSpectrum
open CommonClosureEnergy CommonTangentialParameters CommonFiberGeometry
open scoped BigOperators
noncomputable section

def initialAngle {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) : ℝ := θ ⟨0, by omega⟩

def relativeAngle {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (j : Fin m) : ℝ :=
  θ (CommonClosureEnergy.halfIndex j) - initialAngle hm θ

def relativeAverage {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (j : Fin m) : ℝ :=
  angleAverage (by omega) θ (CommonClosureEnergy.halfIndex j) - initialAngle hm θ

def lensUnit (s t : ℝ) : ℂ := ⟨Lens.height t / 2, s * t / 2⟩

def crossingRelative {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ) (j : Fin m) : ℂ :=
  unit (relativeAverage hm θ j) * lensUnit (σ j) (heightParameter (coordinates hm v) ξ j)

def parameters {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ) : RationalConfiguration.Variables m → ℝ :=
  RationalParameterRecovery.parameters (relativeAngle hm θ) (crossingRelative hm θ v σ ξ)

theorem lensUnit_norm {s t : ℝ} (hs : s ^ 2 = 1) (ht : t ^ 2 ≤ 4) : ‖lensUnit s t‖ = 1 := by
  have he := Lens.height_sq ht
  have hn : ‖lensUnit s t‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    change (Lens.height t / 2) * (Lens.height t / 2) + (s * t / 2) * (s * t / 2) = 1
    nlinarith [sq_nonneg (Lens.height t)]
  nlinarith [norm_nonneg (lensUnit s t)]

theorem lensUnit_close {s t : ℝ} (hs : s ^ 2 = 1) (ht : |t| ≤ 1) :
    ‖lensUnit s t - 1‖ ≤ |t| := by
  have hs' : |s| = 1 := by nlinarith [sq_abs s, abs_nonneg s]
  have ht' : t ^ 2 ≤ 1 := by nlinarith [sq_abs t, abs_nonneg t]
  have he : lensUnit s t - 1 = ((Lens.height t - 2) / 2 : ℝ) + ((s * t / 2 : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [lensUnit]
      ring
    · simp [lensUnit]
  rw [he]
  calc
    _ ≤ ‖(((Lens.height t - 2) / 2 : ℝ) : ℂ)‖ + ‖((s * t / 2 : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |Lens.height t - 2| / 2 + |t| / 2 := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
        abs_div, abs_mul, hs', one_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ t ^ 2 / 4 + |t| / 2 := by
      have hh := BoxLensLift.height_defect (show t ^ 2 ≤ 4 by linarith)
      linarith
    _ ≤ |t| := by nlinarith [sq_abs t, abs_nonneg t]

theorem crossingRelative_norm {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ) (j : Fin m)
    (hs : σ j ^ 2 = 1) (ht : (heightParameter (coordinates hm v) ξ j) ^ 2 ≤ 4) :
    ‖crossingRelative hm θ v σ ξ j‖ = 1 := by
  rw [crossingRelative, norm_mul, norm_unit, one_mul, lensUnit_norm hs ht]

theorem crossingRelative_close {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ) (j : Fin m)
    (hs : σ j ^ 2 = 1) (ht : |heightParameter (coordinates hm v) ξ j| ≤ 1) :
    ‖crossingRelative hm θ v σ ξ j - 1‖ ≤
      |relativeAverage hm θ j| + |heightParameter (coordinates hm v) ξ j| := by
  have he : crossingRelative hm θ v σ ξ j - 1 =
      (unit (relativeAverage hm θ j) - 1) + unit (relativeAverage hm θ j) *
        (lensUnit (σ j) (heightParameter (coordinates hm v) ξ j) - 1) := by
    unfold crossingRelative
    ring
  have hu := norm_unit_sub_le (relativeAverage hm θ j) 0
  simp only [unit, Complex.ofReal_zero, zero_mul, Complex.exp_zero, sub_zero] at hu
  rw [he]
  calc
    _ ≤ ‖unit (relativeAverage hm θ j) - 1‖ + ‖unit (relativeAverage hm θ j) *
        (lensUnit (σ j) (heightParameter (coordinates hm v) ξ j) - 1)‖ := norm_add_le _ _
    _ = ‖unit (relativeAverage hm θ j) - 1‖ + ‖lensUnit (σ j) (heightParameter (coordinates hm v) ξ j) - 1‖ := by
      rw [norm_mul, norm_unit, one_mul]
    _ ≤ _ := add_le_add hu (lensUnit_close hs ht)

theorem relativeAngle_zero {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) :
    relativeAngle hm θ ⟨0, hm⟩ = 0 := by simp [relativeAngle, initialAngle, CommonClosureEnergy.halfIndex]

theorem half_repeat {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (hθ : HalfPeriodic hm (fun j => (θ j : ℂ))) :
    (fun j => (θ j : ℂ)) = BoxLensLift.repeatHalf hm (fun j => (θ (CommonClosureEnergy.halfIndex j) : ℂ)) := by
  apply eq_of_half_restriction hm hθ (BoxLensLift.repeatHalf_halfTurn hm _)
  intro j
  simp only [BoxLensLift.repeatHalf, BoxLensLift.halfIndex, Nat.mod_eq_of_lt j.isLt]
  rfl

theorem half_value {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (hθ : HalfPeriodic hm (fun j => (θ j : ℂ))) (j : Fin (2 * m)) :
    θ (CommonClosureEnergy.halfIndex ⟨j.val % m, Nat.mod_lt _ hm⟩) = θ j := by
  exact Complex.ofReal_injective (congrFun (half_repeat hm θ hθ) j).symm

theorem angle_parameters {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ)
    (hθ : HalfPeriodic hm (fun j => (θ j : ℂ)))
    (ha : ∀ j, |relativeAngle hm θ j| < Real.pi) (j : Fin (2 * m)) :
    RationalAngleBranch.angle hm (parameters hm θ v σ ξ) j = θ j - initialAngle hm θ := by
  rw [parameters, RationalParameterRecovery.angle_parameters hm _ _ (relativeAngle_zero hm θ) ha]
  rw [relativeAngle, half_value hm θ hθ]

theorem small_parameters {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ)
    (hs : ∀ j, σ j ^ 2 = 1) (hθ : ∀ j, |θ j| < 1 / (8 * (2 * m : ℝ)))
    (ht : ∀ j, |heightParameter (coordinates hm v) ξ j| ≤ 1 / (4 * (2 * m : ℝ))) :
    RationalAngleBranch.SmallWindow (parameters hm θ v σ ξ) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hd : (0 : ℝ) < 2 * m := by positivity
  have hd₁ : 1 / (4 * (2 * m : ℝ)) = 2 * (1 / (8 * (2 * m : ℝ))) := by ring
  have hd₂ : 1 / (2 * m : ℝ) = 4 * (1 / (4 * (2 * m : ℝ))) := by ring
  have ha (j : Fin m) : |relativeAngle hm θ j| < 1 / (4 * (2 * m : ℝ)) := by
    have hh := abs_sub_le (θ (CommonClosureEnergy.halfIndex j)) 0 (initialAngle hm θ)
    simp only [sub_zero, zero_sub, abs_neg] at hh
    have hb := hθ ⟨0, by omega⟩
    change |initialAngle hm θ| < _ at hb
    unfold relativeAngle
    linarith [hθ (CommonClosureEnergy.halfIndex j)]
  have hβ (j : Fin m) : |relativeAverage hm θ j| < 1 / (4 * (2 * m : ℝ)) := by
    have hh := abs_sub_le (angleAverage (by omega) θ (CommonClosureEnergy.halfIndex j)) 0 (initialAngle hm θ)
    simp only [sub_zero, zero_sub, abs_neg] at hh
    have hb := hθ ⟨0, by omega⟩
    change |initialAngle hm θ| < _ at hb
    have hav : |angleAverage (by omega) θ (CommonClosureEnergy.halfIndex j)| < 1 / (8 * (2 * m : ℝ)) := by
      unfold angleAverage
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hu := abs_add_le (θ (CommonClosureEnergy.halfIndex j)) (θ (successor (by omega) (CommonClosureEnergy.halfIndex j)))
      linarith [hθ (CommonClosureEnergy.halfIndex j), hθ (successor (by omega) (CommonClosureEnergy.halfIndex j))]
    unfold relativeAverage
    linarith
  apply RationalParameterRecovery.small_parameters hm
  · intro j
    exact (ha j).trans (by linarith [show (0 : ℝ) < 1 / (4 * (2 * m : ℝ)) by positivity])
  · intro j
    have ht1 : |heightParameter (coordinates hm v) ξ j| ≤ 1 := (ht j).trans
      ((div_le_one (by positivity)).2 (by linarith))
    have hb := crossingRelative_close hm θ v σ ξ j (hs j) ht1
    linarith [hβ j, ht j, show (0 : ℝ) < 1 / (2 * m : ℝ) by positivity]

end
end StructuralNote.CommonRationalChart
