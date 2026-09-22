import StructuralNote.FixedSchurChartRotated
import StructuralNote.CommonFiberNormalProjection

/-! Exact normal-coordinate expansion and the scalar angular Taylor remainder.

The expansion uses the positive rotated branch already proved for the actual
fixed-Schur coordinate.  The scalar estimate retains both the quadratic angle
term and the mixed secant term.
-/

namespace StructuralNote.FixedSchurNormalExpansion

open scoped BigOperators Topology

open Complex Filter
open Erdos1045 Erdos1045.EventualExact
open FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open CommonClosureEnergy CommonDomainClosure CommonDomainRadius
open CommonTangentialParameters
open EdgeCoordinates FixedSchurData FixedSchurChart FixedSchurLinear
open FixedSchurChartRotated FixedSchurRotatedAlgebra
open CommonFiberNormalProjection

noncomputable section

def angularErrorCoefficient {n : ℕ} (hn : 0 < n)
    (θ : Fin n → ℝ) (j : Fin n) : ℝ :=
  (((2 - chordLength hn θ j) / Real.cos (angleAverage hn θ j)) -
      (2 - 2 * Real.cos (Real.pi / (n : ℝ))) -
      Real.sin (Real.pi / (n : ℝ)) * angleDifference hn θ j) / epsilon n

def normalError {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ)
    (q σ : Fin n → ℝ) (j : Fin n) : ℝ :=
  q j - FiniteBox.amplitude n * σ j -
    (n : ℝ) / 2 * σ j * angleDifference hn θ j

def rotatedP {n : ℕ} (hn : 0 < n) (v : Fin n → ℂ)
    (q : Fin n → ℝ) (j : Fin n) : ℝ :=
  (J q + tangent hn v) j

def rotatedS {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ)
    (v : Fin n → ℂ) (q : Fin n → ℝ) (j : Fin n) : ℝ :=
  tangential (angleAverage hn θ j) (q j) (rotatedP hn v q j)

def rotatedH {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ)
    (v : Fin n → ℂ) (q : Fin n → ℝ) (j : Fin n) : ℝ :=
  Real.sqrt (4 - (epsilon n * rotatedS hn θ v q j) ^ 2)

theorem scalar_angular_error_bound (a η b : ℝ)
    (hη : |η / 2| ≤ 1) (hb : |b| ≤ 1) :
    |((2 - 2 * Real.cos (a + η / 2)) / Real.cos b) -
        (2 - 2 * Real.cos a) - Real.sin a * η| ≤
      η ^ 2 / 2 + (a + η / 2) ^ 2 * b ^ 2 := by
  have hb2 : b ^ 2 ≤ 1 := by
    have hble := (abs_le.mp hb)
    nlinarith [sq_abs b]
  have hcos_lower : (1 / 2 : ℝ) ≤ Real.cos b := by
    have hcos := Real.one_sub_sq_div_two_le_cos (x := b)
    nlinarith
  have hcos_pos : 0 < Real.cos b := lt_of_lt_of_le (by norm_num) hcos_lower
  have hsec_nonneg : 0 ≤ 1 / Real.cos b - 1 := by
    have hcos_le : Real.cos b ≤ 1 := Real.cos_le_one b
    have hnum : 0 ≤ 1 - Real.cos b := by linarith
    have hid : 1 / Real.cos b - 1 =
        (1 - Real.cos b) / Real.cos b := by
      field_simp
    rw [hid]
    exact div_nonneg hnum hcos_pos.le
  have hsec_le : 1 / Real.cos b - 1 ≤ b ^ 2 := by
    have hcos_err := cos_zero_error b
    have hnonneg : 0 ≤ 1 - Real.cos b := by linarith [Real.cos_le_one b]
    have hone : 1 - Real.cos b ≤ b ^ 2 / 2 := by
      have hcos_err' : |1 - Real.cos b| ≤ b ^ 2 / 2 := by
        simpa only [abs_sub_comm] using hcos_err
      simpa only [abs_of_nonneg hnonneg] using hcos_err'
    rw [show 1 / Real.cos b - 1 =
      (1 - Real.cos b) / Real.cos b by field_simp]
    apply (div_le_iff₀ hcos_pos).2
    have hmul : b ^ 2 / 2 ≤ b ^ 2 * Real.cos b := by
      nlinarith [sq_nonneg b, hcos_lower]
    nlinarith
  have hlin := cos_linear_error a (η / 2) hη
  have hlin' :
      |(2 - 2 * Real.cos (a + η / 2)) - (2 - 2 * Real.cos a) -
          Real.sin a * η| ≤ η ^ 2 / 2 := by
    have he :
        (2 - 2 * Real.cos (a + η / 2)) - (2 - 2 * Real.cos a) -
            Real.sin a * η =
          -2 * (Real.cos (a + η / 2) - Real.cos a +
            Real.sin a * (η / 2)) := by ring
    rw [he, abs_mul]
    norm_num
    nlinarith [hlin]
  have hwidth_nonneg : 0 ≤ 2 - 2 * Real.cos (a + η / 2) := by
    nlinarith [Real.cos_le_one (a + η / 2)]
  have hwidth : 2 - 2 * Real.cos (a + η / 2) ≤ (a + η / 2) ^ 2 := by
    have hcos := Real.one_sub_sq_div_two_le_cos (x := a + η / 2)
    nlinarith
  have hmix :
      (2 - 2 * Real.cos (a + η / 2)) * (1 / Real.cos b - 1) ≤
        (a + η / 2) ^ 2 * b ^ 2 := by
    exact mul_le_mul hwidth hsec_le hsec_nonneg (sq_nonneg _)
  have hmix_abs :
      |(2 - 2 * Real.cos (a + η / 2)) * (1 / Real.cos b - 1)| ≤
        (a + η / 2) ^ 2 * b ^ 2 := by
    rw [abs_of_nonneg (mul_nonneg hwidth_nonneg hsec_nonneg)]
    exact hmix
  have hdecomp :
      (2 - 2 * Real.cos (a + η / 2)) / Real.cos b -
          (2 - 2 * Real.cos a) - Real.sin a * η =
        ((2 - 2 * Real.cos (a + η / 2)) -
            (2 - 2 * Real.cos a) - Real.sin a * η) +
          (2 - 2 * Real.cos (a + η / 2)) *
            (1 / Real.cos b - 1) := by
    field_simp [ne_of_gt hcos_pos]
    ring
  rw [hdecomp]
  exact (abs_add_le _ _).trans (add_le_add hlin' hmix_abs)

theorem normal_error_algebra {n : ℝ} {q σ ε A a L b η p S H : ℝ}
    (hε : ε ≠ 0) (hcos : Real.cos b ≠ 0) (hden : 2 + H ≠ 0)
    (hamp : ε * A = 2 - 2 * Real.cos a)
    (hlin : ε * (n / 2) = Real.sin a)
    (hq : q = σ / ε * ((2 - L) / Real.cos b) - p * Real.tan b -
      σ * ε * S ^ 2 / (Real.cos b * (2 + H))) :
    q - A * σ - n / 2 * σ * η =
      σ * (((2 - L) / Real.cos b - (2 - 2 * Real.cos a) -
        Real.sin a * η) / ε) - p * Real.tan b -
        σ * ε * S ^ 2 / (Real.cos b * (2 + H)) := by
  rw [hq]
  rw [← hamp, ← hlin]
  field_simp [hε, hcos, hden]
  ring

theorem normalError_from_rotated_formula {n : ℕ} (hn : 0 < n) (hn2 : 2 ≤ n)
    (θ q σ : Fin n → ℝ) (j : Fin n) {p S H : ℝ}
    (_hcos : 0 < Real.cos (angleAverage hn θ j))
    (hcoord : q j = σ j / epsilon n *
        ((2 - chordLength hn θ j) / Real.cos (angleAverage hn θ j)) -
      p * Real.tan (angleAverage hn θ j) -
      σ j * epsilon n * S ^ 2 /
        (Real.cos (angleAverage hn θ j) * (2 + H)))
    (hden : 2 + H ≠ 0) :
    normalError hn θ q σ j =
      σ j * angularErrorCoefficient hn θ j -
        p * Real.tan (angleAverage hn θ j) -
        σ j * epsilon n * S ^ 2 /
          (Real.cos (angleAverage hn θ j) * (2 + H)) := by
  have hε : 0 < epsilon n := epsilon_pos hn2
  have hεne : epsilon n ≠ 0 := hε.ne'
  have hcosne : Real.cos (angleAverage hn θ j) ≠ 0 := _hcos.ne'
  have hamp := epsilon_amplitude hn2
  have hlin : epsilon n * ((n : ℝ) / 2) = Real.sin (Real.pi / (n : ℝ)) := by
    unfold epsilon
    field_simp
  unfold normalError angularErrorCoefficient
  exact normal_error_algebra
    (n := (n : ℝ)) (q := q j) (σ := σ j) (ε := epsilon n)
    (A := FiniteBox.amplitude n) (a := Real.pi / (n : ℝ))
    (L := chordLength hn θ j) (b := angleAverage hn θ j)
    (η := angleDifference hn θ j) (p := p) (S := S) (H := H)
    hεne hcosne hden hamp hlin hcoord

theorem eventual_normalError_rotated_expansion : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → ∀ j : Fin (2 * m),
      normalError (by omega) θ (coordinate (by omega) s θ v)
          (FiniteBox.patternSign s) j =
        FiniteBox.patternSign s j * angularErrorCoefficient (by omega) θ j -
          rotatedP (by omega) v (coordinate (by omega) s θ v) j *
            Real.tan (angleAverage (by omega) θ j) -
          FiniteBox.patternSign s j * epsilon (2 * m) *
            (rotatedS (by omega) θ v (coordinate (by omega) s θ v) j) ^ 2 /
            (Real.cos (angleAverage (by omega) θ j) *
              (2 + rotatedH (by omega) θ v (coordinate (by omega) s θ v) j)) := by
  filter_upwards [FixedSchurChartRotated.eventual_coordinate_rotated] with m hrot
  intro hm s θ v hdom j
  have hr := hrot hm s θ v hdom j
  have hcoord := hr.2.2.2.2.2
  have hcoord' : coordinate (by omega) s θ v j =
      FiniteBox.patternSign s j / epsilon (2 * m) *
          ((2 - chordLength (by omega) θ j) /
            Real.cos (angleAverage (by omega) θ j)) -
        rotatedP (by omega) v (coordinate (by omega) s θ v) j *
          Real.tan (angleAverage (by omega) θ j) -
        FiniteBox.patternSign s j * epsilon (2 * m) *
          (rotatedS (by omega) θ v (coordinate (by omega) s θ v) j) ^ 2 /
          (Real.cos (angleAverage (by omega) θ j) *
            (2 + rotatedH (by omega) θ v (coordinate (by omega) s θ v) j)) := by
    simpa only [rotatedP, rotatedS, rotatedH] using hcoord
  have hden : 2 + rotatedH (by omega) θ v (coordinate (by omega) s θ v) j ≠ 0 := by
    have hh : 0 ≤ rotatedH (by omega) θ v (coordinate (by omega) s θ v) j :=
      Real.sqrt_nonneg _
    nlinarith
  simpa only [rotatedP, rotatedS, rotatedH] using
    (normalError_from_rotated_formula (by omega) (by omega) θ
      (coordinate (by omega) s θ v) (FiniteBox.patternSign s) j hr.1 hcoord' hden)

end
end StructuralNote.FixedSchurNormalExpansion
