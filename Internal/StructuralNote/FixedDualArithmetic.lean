import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
Appendix A: exact table data and the rational implication from primitive enclosures
to the two numerical budgets. This file does NOT prove the twenty signs of the
actual transcendental functions, the ten actual primitive enclosures, the zero
count, or the absolute-value integral identity. Those are separate analytic tasks.
-/

namespace StructuralNote.FixedDualArithmetic

open scoped BigOperators

/-- The signed parameter is `sign * magnitude`; `rising` records the expected
left-negative/right-positive sign pattern, not a proved transcendental assertion. -/
structure Row where
  magnitude : ℚ
  sign : ℤ
  leftHundredths : ℕ
  primitiveThousandths : ℤ
  rising : Bool
  deriving DecidableEq

def rows : Fin 10 → Row := ![
  ⟨1 / 2, 1, 6, 1336, true⟩,
  ⟨1 / 2, 1, 79, 1861, false⟩,
  ⟨1 / 2, -1, 9, 1659, true⟩,
  ⟨1 / 2, -1, 45, 1745, false⟩,
  ⟨1 / 2, -1, 137, 1310, true⟩,
  ⟨1, 1, 6, 1172, true⟩,
  ⟨1, 1, 87, 1996, false⟩,
  ⟨1, -1, 12, 1818, true⟩,
  ⟨1, -1, 25, 1824, false⟩,
  ⟨1, -1, 126, 1194, true⟩]

def left (r : Row) : ℚ := r.leftHundredths / 100
def right (r : Row) : ℚ := (r.leftHundredths + 1) / 100
def midpoint (r : Row) : ℚ := (2 * r.leftHundredths + 1) / 200
def primitiveLower (r : Row) : ℚ := r.primitiveThousandths / 1000
def primitiveUpper (r : Row) : ℚ := (r.primitiveThousandths + 1) / 1000
def signedParameter (r : Row) : ℚ := r.sign * r.magnitude

theorem row_domains (i : Fin 10) :
    3 / 50 ≤ left (rows i) ∧ right (rows i) ≤ 69 / 50 ∧
      |signedParameter (rows i)| ≤ 1 := by
  fin_cases i <;> norm_num [rows, left, right, signedParameter]

theorem row_denominators_positive :
    (0 : ℚ) < 100 ∧ 0 < 200 ∧ 0 < 1000 ∧ 0 < 40000 ∧ 0 < 56000 := by norm_num

theorem row_midpoint_width (r : Row) :
    midpoint r - left r = 1 / 200 ∧ right r - midpoint r = 1 / 200 ∧
      primitiveUpper r - primitiveLower r = 1 / 1000 := by
  simp only [midpoint, left, right, primitiveUpper, primitiveLower]
  constructor
  · ring
  constructor <;> ring

theorem row_argument_bound (i : Fin 10) :
    0 < left (rows i) ∧ 3 * right (rows i) ≤ 207 / 50 := by
  obtain ⟨hl, hr, _⟩ := row_domains i
  constructor <;> linarith

/-- The positive rational lower bound used for every sine denominator. -/
def sineFloor : ℚ := 3 / 50 - (3 / 50) ^ 3 / 6

theorem derivative_denominator_positive : 0 < sineFloor := by norm_num [sineFloor]

theorem rational_derivative_bound : (17 : ℚ) / 2 + 1 / sineFloor < 26 := by
  norm_num [sineFloor]

def rootError : ℚ := 13 / 40000

theorem stationary_error_arithmetic : (26 : ℚ) / 2 * (1 / 200) ^ 2 = rootError := by
  norm_num [rootError]

theorem five_root_error : 5 * rootError = (13 : ℚ) / 8000 := by norm_num [rootError]

/-- Signs of the five stationary primitive values in (A.5). -/
def rootCoefficient : Fin 5 → ℚ := ![-1, 1, -1, 1, -1]

def budgetHalf : ℚ := 11 / 7 +
  (primitiveUpper (rows ⟨1, by omega⟩) - primitiveLower (rows ⟨0, by omega⟩) +
    primitiveUpper (rows ⟨3, by omega⟩) - primitiveLower (rows ⟨2, by omega⟩) -
      primitiveLower (rows ⟨4, by omega⟩)) +
  5 * rootError

def budgetOne : ℚ := 11 / 7 +
  (primitiveUpper (rows ⟨6, by omega⟩) - primitiveLower (rows ⟨5, by omega⟩) +
    primitiveUpper (rows ⟨8, by omega⟩) - primitiveLower (rows ⟨7, by omega⟩) -
      primitiveLower (rows ⟨9, by omega⟩)) +
  5 * rootError

theorem budgetHalf_exact : budgetHalf = 49059 / 56000 := by
  norm_num [budgetHalf, primitiveUpper, primitiveLower, rows, rootError]

theorem budgetOne_exact : budgetOne = 67819 / 56000 := by
  norm_num [budgetOne, primitiveUpper, primitiveLower, rows, rootError]

theorem budgetHalf_strict : budgetHalf < 9 / 10 := by rw [budgetHalf_exact]; norm_num
theorem budgetOne_strict : budgetOne < 97 / 80 := by rw [budgetOne_exact]; norm_num

theorem strict_budget_margins :
    9 / 10 - budgetHalf = 1341 / 56000 ∧ 97 / 80 - budgetOne = 81 / 56000 := by
  rw [budgetHalf_exact, budgetOne_exact]
  norm_num

theorem pi_half_upper : Real.pi / 2 < 11 / 7 := by linarith [Real.pi_lt_d4]

/-- A second derivative bound of 26 and a midpoint distance at most 1/200
lead to this arithmetic radius. The analytic Taylor theorem is not assumed here. -/
theorem stationary_error_from_quadratic {e d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 1 / 200)
    (he : |e| ≤ 26 / 2 * d ^ 2) : |e| ≤ 13 / 40000 := by
  nlinarith

theorem root_enclosure_of_midpoint {k : ℤ} {qmid qroot : ℝ}
    (hmid : (k : ℝ) / 1000 < qmid ∧ qmid < ((k : ℝ) + 1) / 1000)
    (herr : |qroot - qmid| ≤ 13 / 40000) :
    (k : ℝ) / 1000 - 13 / 40000 < qroot ∧
      qroot < ((k : ℝ) + 1) / 1000 + 13 / 40000 := by
  obtain ⟨he1, he2⟩ := abs_le.mp herr
  constructor <;> linarith [hmid.1, hmid.2]

/-- Pure arithmetic interface to (A.5), for any five primitive values.
`hidentity` and `hprimitive` are explicitly supplied; neither asserts that
the actual analytic functions have already been enclosed. -/
theorem five_value_budget {J : ℝ} (q : Fin 5 → ℝ) (k : Fin 5 → ℤ)
    (hidentity : J = Real.pi / 2 + q 1 - q 0 + q 3 - q 2 - q 4)
    (hprimitive : ∀ i, (k i : ℝ) / 1000 - 13 / 40000 < q i ∧
      q i < ((k i : ℝ) + 1) / 1000 + 13 / 40000) :
    J < 11 / 7 + (((k 1 : ℝ) + 1) - k 0 + ((k 3 : ℝ) + 1) - k 2 - k 4) / 1000 +
      13 / 8000 := by
  have h0 := (hprimitive 0).1
  have h1 := (hprimitive 1).2
  have h2 := (hprimitive 2).1
  have h3 := (hprimitive 3).2
  have h4 := (hprimitive 4).1
  rw [hidentity]
  linarith [pi_half_upper]

theorem half_budget_from_primitive_enclosures {J : ℝ} (q : Fin 5 → ℝ)
    (hidentity : J = Real.pi / 2 + q 1 - q 0 + q 3 - q 2 - q 4)
    (hprimitive : ∀ i : Fin 5,
      ((rows ⟨i, by omega⟩).primitiveThousandths : ℝ) / 1000 - 13 / 40000 < q i ∧
        q i < (((rows ⟨i, by omega⟩).primitiveThousandths : ℝ) + 1) / 1000 + 13 / 40000) :
    J < 49059 / 56000 ∧ J < 9 / 10 := by
  have h := five_value_budget q (fun i => (rows ⟨i, by omega⟩).primitiveThousandths)
    hidentity hprimitive
  norm_num [rows] at h
  constructor
  · exact h
  · linarith

theorem one_budget_from_primitive_enclosures {J : ℝ} (q : Fin 5 → ℝ)
    (hidentity : J = Real.pi / 2 + q 1 - q 0 + q 3 - q 2 - q 4)
    (hprimitive : ∀ i : Fin 5,
      ((rows ⟨i + 5, by omega⟩).primitiveThousandths : ℝ) / 1000 - 13 / 40000 < q i ∧
        q i < (((rows ⟨i + 5, by omega⟩).primitiveThousandths : ℝ) + 1) / 1000 + 13 / 40000) :
    J < 67819 / 56000 ∧ J < 97 / 80 := by
  have h := five_value_budget q (fun i => (rows ⟨i + 5, by omega⟩).primitiveThousandths)
    hidentity hprimitive
  norm_num [rows] at h
  constructor
  · exact h
  · linarith

/-- The numerical part of the two-plane sign test in §8.2. -/
theorem first_plane_margin {r J g c : ℝ} (hr : 24 / 25 ≤ r)
    (hJ : J < 9 / 10) (hc : 1 ≤ c) (hg : r * c - J ≤ g) : 3 / 50 < g := by
  have hrc : r ≤ r * c := by nlinarith
  linarith

theorem second_plane_margin {r J g c : ℝ} (hr : 24 / 25 ≤ r)
    (hJ : J < 97 / 80) (hc : 129 / 100 ≤ c) (hg : r * c - J ≤ g) :
    259 / 10000 < g ∧ 1 / 50 < g := by
  have hrc : (24 : ℝ) / 25 * (129 / 100) ≤ r * c :=
    mul_le_mul hr hc (by norm_num) (by linarith)
  constructor <;> linarith

theorem second_plane_polynomial_margin :
    (1 : ℚ) + 3 / 8 - (3 / 8) ^ 2 / 2 - (3 / 8) ^ 3 / 6 = 1327 / 1024 ∧
      (129 : ℚ) / 100 < 1327 / 1024 := by norm_num

end StructuralNote.FixedDualArithmetic
