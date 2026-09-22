import Mathlib

/-! The positive scalar square-root branch used by a fixed Schur coordinate. -/

namespace StructuralNote.FixedSchurScalarRoot

open Real Set
noncomputable section

def rootValue (σ ε X Y p : ℝ) : ℝ :=
  σ / ε * (Real.sqrt (4 - (Y + σ * ε * p) ^ 2) - X)

private theorem sign_sq {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : σ ^ 2 = 1 := by
  rcases hσ with rfl | rfl <;> norm_num

private theorem radicand_pos {z : ℝ} (hz : |z| < 2) : 0 < 4 - z ^ 2 := by
  have hz' := abs_lt.mp hz
  nlinarith

private theorem root_cancel {σ ε : ℝ} (hσ : σ = 1 ∨ σ = -1) (hε : 0 < ε) :
    σ * ε * (σ / ε) = 1 := by
  have hσsq := sign_sq hσ
  field_simp [ne_of_gt hε]
  nlinarith

theorem rootValue_spec {σ ε X Y p : ℝ} (hσ : σ = 1 ∨ σ = -1) (hε : 0 < ε)
    (hz : |Y + σ * ε * p| < 2) :
    0 < X + σ * ε * rootValue σ ε X Y p ∧
      (X + σ * ε * rootValue σ ε X Y p) ^ 2 +
          (Y + σ * ε * p) ^ 2 = 4 := by
  have hrad : 0 < 4 - (Y + σ * ε * p) ^ 2 := radicand_pos hz
  have hsqrt : 0 < Real.sqrt (4 - (Y + σ * ε * p) ^ 2) :=
    Real.sqrt_pos.mpr hrad
  have hcancel := root_cancel hσ hε
  have hroot : X + σ * ε * rootValue σ ε X Y p =
      Real.sqrt (4 - (Y + σ * ε * p) ^ 2) := by
    calc
      X + σ * ε * rootValue σ ε X Y p =
          X + (σ * ε * (σ / ε)) *
            (Real.sqrt (4 - (Y + σ * ε * p) ^ 2) - X) := by
              unfold rootValue
              ring
      _ = Real.sqrt (4 - (Y + σ * ε * p) ^ 2) := by
        rw [hcancel]
        ring
  constructor
  · rw [hroot]
    exact hsqrt
  · rw [hroot]
    have hsquare := Real.sq_sqrt hrad.le
    nlinarith only [hsquare]

theorem rootValue_unique {σ ε X Y p q : ℝ} (hσ : σ = 1 ∨ σ = -1) (hε : 0 < ε)
    (hz : |Y + σ * ε * p| < 2)
    (hq : 0 < X + σ * ε * q)
    (hcirc : (X + σ * ε * q) ^ 2 + (Y + σ * ε * p) ^ 2 = 4) :
    q = rootValue σ ε X Y p := by
  have hrad : 0 < 4 - (Y + σ * ε * p) ^ 2 := radicand_pos hz
  have hsqrt : 0 ≤ Real.sqrt (4 - (Y + σ * ε * p) ^ 2) :=
    Real.sqrt_nonneg _
  have hsquare := Real.sq_sqrt hrad.le
  have hroot : X + σ * ε * q =
      Real.sqrt (4 - (Y + σ * ε * p) ^ 2) := by
    nlinarith only [hcirc, hsquare, hsqrt, hq]
  have hlinear : σ * ε * q =
      Real.sqrt (4 - (Y + σ * ε * p) ^ 2) - X := by
    linarith only [hroot]
  have hcancel := root_cancel hσ hε
  unfold rootValue
  calc
    q = (σ * ε * (σ / ε)) * q := by rw [hcancel]; ring
    _ = (σ / ε) * (σ * ε * q) := by ring
    _ = (σ / ε) * (Real.sqrt (4 - (Y + σ * ε * p) ^ 2) - X) := by
      rw [hlinear]

private theorem sq_le_sq_of_abs_le {z r : ℝ} (hr : 0 ≤ r) (hz : |z| ≤ r) :
    z ^ 2 ≤ r ^ 2 := by
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg z) hr).mpr hz

private theorem sqrt_difference_bound {z z' r : ℝ} (hr0 : 0 ≤ r) (hr2 : r < 2)
    (hz : |z| ≤ r) (hz' : |z'| ≤ r) :
    |Real.sqrt (4 - z ^ 2) - Real.sqrt (4 - z' ^ 2)| ≤
      r / Real.sqrt (4 - r ^ 2) * |z - z'| := by
  have hrrad : 0 < 4 - r ^ 2 := by
    nlinarith [sq_nonneg r]
  have hzsq : z ^ 2 ≤ r ^ 2 := sq_le_sq_of_abs_le hr0 hz
  have hz'sq : z' ^ 2 ≤ r ^ 2 := sq_le_sq_of_abs_le hr0 hz'
  have hrad : 0 ≤ 4 - z ^ 2 := by linarith
  have hrad' : 0 ≤ 4 - z' ^ 2 := by linarith
  have hsD : 0 < Real.sqrt (4 - r ^ 2) := Real.sqrt_pos.mpr hrrad
  have hs : 0 ≤ Real.sqrt (4 - z ^ 2) := Real.sqrt_nonneg _
  have hs' : 0 ≤ Real.sqrt (4 - z' ^ 2) := Real.sqrt_nonneg _
  have hD : Real.sqrt (4 - r ^ 2) ≤ Real.sqrt (4 - z ^ 2) := by
    have hDsq := Real.sq_sqrt hrrad.le
    have hssq := Real.sq_sqrt hrad
    nlinarith
  have hD' : Real.sqrt (4 - r ^ 2) ≤ Real.sqrt (4 - z' ^ 2) := by
    have hDsq := Real.sq_sqrt hrrad.le
    have hs'sq := Real.sq_sqrt hrad'
    nlinarith
  have hden : 0 < Real.sqrt (4 - z ^ 2) + Real.sqrt (4 - z' ^ 2) := by
    nlinarith
  have hdenlower : 2 * Real.sqrt (4 - r ^ 2) ≤
      Real.sqrt (4 - z ^ 2) + Real.sqrt (4 - z' ^ 2) := by
    linarith
  have hid :
      (Real.sqrt (4 - z ^ 2) - Real.sqrt (4 - z' ^ 2)) *
          (Real.sqrt (4 - z ^ 2) + Real.sqrt (4 - z' ^ 2)) = z' ^ 2 - z ^ 2 := by
    calc
      (Real.sqrt (4 - z ^ 2) - Real.sqrt (4 - z' ^ 2)) *
          (Real.sqrt (4 - z ^ 2) + Real.sqrt (4 - z' ^ 2)) =
          Real.sqrt (4 - z ^ 2) ^ 2 - Real.sqrt (4 - z' ^ 2) ^ 2 := by ring
      _ = (4 - z ^ 2) - (4 - z' ^ 2) := by
        rw [Real.sq_sqrt hrad, Real.sq_sqrt hrad']
      _ = z' ^ 2 - z ^ 2 := by ring
  have hquot :
      |Real.sqrt (4 - z ^ 2) - Real.sqrt (4 - z' ^ 2)| ≤
        |z' ^ 2 - z ^ 2| /
          (Real.sqrt (4 - z ^ 2) + Real.sqrt (4 - z' ^ 2)) := by
    apply (le_div_iff₀ hden).2
    calc
      |Real.sqrt (4 - z ^ 2) - Real.sqrt (4 - z' ^ 2)| *
          (Real.sqrt (4 - z ^ 2) + Real.sqrt (4 - z' ^ 2)) =
          |(Real.sqrt (4 - z ^ 2) - Real.sqrt (4 - z' ^ 2)) *
            (Real.sqrt (4 - z ^ 2) + Real.sqrt (4 - z' ^ 2))| := by
              rw [abs_mul, abs_of_pos hden]
      _ = |z' ^ 2 - z ^ 2| := by
        rw [hid]
      _ ≤ |z' ^ 2 - z ^ 2| := le_rfl
  have hsum : |z' + z| ≤ 2 * r := by
    calc
      |z' + z| ≤ |z'| + |z| := abs_add_le _ _
      _ ≤ r + r := add_le_add hz' hz
      _ = 2 * r := by ring
  have hnum : |z' ^ 2 - z ^ 2| ≤ 2 * r * |z' - z| := by
    rw [show z' ^ 2 - z ^ 2 = (z' - z) * (z' + z) by ring, abs_mul]
    calc
      |z' - z| * |z' + z| ≤ |z' - z| * (2 * r) :=
        mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
      _ = 2 * r * |z' - z| := by ring
  have hquot' :
      |Real.sqrt (4 - z ^ 2) - Real.sqrt (4 - z' ^ 2)| ≤
        (2 * r * |z' - z|) /
          (Real.sqrt (4 - z ^ 2) + Real.sqrt (4 - z' ^ 2)) :=
    hquot.trans (div_le_div_of_nonneg_right hnum hden.le)
  have hquot'' :
      |Real.sqrt (4 - z ^ 2) - Real.sqrt (4 - z' ^ 2)| ≤
        (2 * r * |z' - z|) / (2 * Real.sqrt (4 - r ^ 2)) := by
    exact hquot'.trans (div_le_div_of_nonneg_left
      (by positivity : 0 ≤ 2 * r * |z' - z|)
      (by positivity : 0 < 2 * Real.sqrt (4 - r ^ 2)) hdenlower)
  calc
    |Real.sqrt (4 - z ^ 2) - Real.sqrt (4 - z' ^ 2)| ≤
        (2 * r * |z' - z|) / (2 * Real.sqrt (4 - r ^ 2)) := hquot''
    _ = r / Real.sqrt (4 - r ^ 2) * |z - z'| := by
      rw [abs_sub_comm z' z]
      field_simp [ne_of_gt hsD]

theorem rootValue_lipschitz {σ ε X Y p p' r : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hε : 0 < ε) (hr0 : 0 ≤ r) (hr2 : r < 2)
    (hp : |Y + σ * ε * p| ≤ r) (hp' : |Y + σ * ε * p'| ≤ r) :
    |rootValue σ ε X Y p - rootValue σ ε X Y p'| ≤
      r / Real.sqrt (4 - r ^ 2) * |p - p'| := by
  have hsigma : |σ| = 1 := by
    rcases hσ with rfl | rfl <;> norm_num
  have hsd := sqrt_difference_bound hr0 hr2 hp hp'
  have hcoef : |σ / ε| = 1 / ε := by
    rw [abs_div, hsigma, abs_of_pos hε]
  have hpdiff : |Y + σ * ε * p - (Y + σ * ε * p')| = ε * |p - p'| := by
    calc
      |Y + σ * ε * p - (Y + σ * ε * p')| =
          |σ| * |ε| * |p - p'| := by
            rw [show Y + σ * ε * p - (Y + σ * ε * p') =
              σ * ε * (p - p') by ring, abs_mul, abs_mul]
      _ = ε * |p - p'| := by rw [hsigma, abs_of_pos hε]; ring
  calc
    |rootValue σ ε X Y p - rootValue σ ε X Y p'| =
        |σ / ε| *
          |Real.sqrt (4 - (Y + σ * ε * p) ^ 2) -
            Real.sqrt (4 - (Y + σ * ε * p') ^ 2)| := by
          unfold rootValue
          rw [show σ / ε *
              (Real.sqrt (4 - (Y + σ * ε * p) ^ 2) - X) -
                σ / ε * (Real.sqrt (4 - (Y + σ * ε * p') ^ 2) - X) =
              (σ / ε) *
                (Real.sqrt (4 - (Y + σ * ε * p) ^ 2) -
                  Real.sqrt (4 - (Y + σ * ε * p') ^ 2)) by ring,
            abs_mul]
    _ = (1 / ε) *
          |Real.sqrt (4 - (Y + σ * ε * p) ^ 2) -
            Real.sqrt (4 - (Y + σ * ε * p') ^ 2)| := by rw [hcoef]
    _ ≤ (1 / ε) *
          (r / Real.sqrt (4 - r ^ 2) *
            |Y + σ * ε * p - (Y + σ * ε * p')|) := by
          gcongr
    _ = r / Real.sqrt (4 - r ^ 2) * |p - p'| := by
          rw [hpdiff]
          field_simp [ne_of_gt hε]

theorem rootValue_lipschitz_of_le_one {σ ε X Y p p' r : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hε : 0 < ε) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hp : |Y + σ * ε * p| ≤ r) (hp' : |Y + σ * ε * p'| ≤ r) :
    |rootValue σ ε X Y p - rootValue σ ε X Y p'| ≤ r * |p - p'| := by
  have hgen := rootValue_lipschitz (X := X) hσ hε hr0
    (lt_of_le_of_lt hr1 (by norm_num)) hp hp'
  have hsq : r ^ 2 ≤ 1 := by nlinarith [sq_nonneg r]
  have hrad : 0 ≤ 4 - r ^ 2 := by linarith
  have hsqrt : 1 ≤ Real.sqrt (4 - r ^ 2) := by
    have hsquare := Real.sq_sqrt hrad
    have hsnonneg := Real.sqrt_nonneg (4 - r ^ 2)
    nlinarith
  have hsqrtpos : 0 < Real.sqrt (4 - r ^ 2) := lt_of_lt_of_le (by norm_num) hsqrt
  calc
    |rootValue σ ε X Y p - rootValue σ ε X Y p'| ≤
        r / Real.sqrt (4 - r ^ 2) * |p - p'| := hgen
    _ = (r * |p - p'|) / Real.sqrt (4 - r ^ 2) := by ring
    _ ≤ r * |p - p'| := by
      apply (div_le_iff₀ hsqrtpos).2
      nlinarith [mul_nonneg hr0 (abs_nonneg (p - p'))]

theorem rootValue_source_bound {σ ε X X₀ Y A p : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hε : 0 < ε) (hA : ε * A = 2 - X₀)
    (hz : |Y + σ * ε * p| ≤ 1) :
    |rootValue σ ε X Y p - A * σ| ≤
      (|X - X₀| + (Y + σ * ε * p) ^ 2 / 2) / ε := by
  have hsigma : |σ| = 1 := by
    rcases hσ with rfl | rfl <;> norm_num
  have hzsq : (Y + σ * ε * p) ^ 2 ≤ 1 := by
    simpa using (sq_le_sq_of_abs_le (z := Y + σ * ε * p) (r := 1) (by norm_num) hz)
  have hrad : 0 ≤ 4 - (Y + σ * ε * p) ^ 2 := by linarith
  have hsqrt : 0 ≤ Real.sqrt (4 - (Y + σ * ε * p) ^ 2) :=
    Real.sqrt_nonneg _
  have hsquare := Real.sq_sqrt hrad
  have hsqrt_le : Real.sqrt (4 - (Y + σ * ε * p) ^ 2) ≤ 2 := by
    nlinarith
  have hden : 0 < 2 + Real.sqrt (4 - (Y + σ * ε * p) ^ 2) := by
    nlinarith
  have hroot_error :
      2 - Real.sqrt (4 - (Y + σ * ε * p) ^ 2) ≤
        (Y + σ * ε * p) ^ 2 / 2 := by
    have hid :
        (2 - Real.sqrt (4 - (Y + σ * ε * p) ^ 2)) *
            (2 + Real.sqrt (4 - (Y + σ * ε * p) ^ 2)) =
          (Y + σ * ε * p) ^ 2 := by
      nlinarith
    have hfrac : 2 - Real.sqrt (4 - (Y + σ * ε * p) ^ 2) =
        (Y + σ * ε * p) ^ 2 /
          (2 + Real.sqrt (4 - (Y + σ * ε * p) ^ 2)) := by
      apply (eq_div_iff (ne_of_gt hden)).2
      exact hid
    rw [hfrac]
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num : (0 : ℝ) < 2)
    nlinarith
  have hlin : rootValue σ ε X Y p - A * σ =
      (σ / ε) *
        (Real.sqrt (4 - (Y + σ * ε * p) ^ 2) - 2 + (X₀ - X)) := by
    unfold rootValue
    rw [show A * σ = (σ / ε) * (ε * A) by
      field_simp [ne_of_gt hε]]
    rw [hA]
    ring
  have hinner :
      |Real.sqrt (4 - (Y + σ * ε * p) ^ 2) - 2 + (X₀ - X)| ≤
        |X - X₀| + (Y + σ * ε * p) ^ 2 / 2 := by
    calc
      |Real.sqrt (4 - (Y + σ * ε * p) ^ 2) - 2 + (X₀ - X)| ≤
          |Real.sqrt (4 - (Y + σ * ε * p) ^ 2) - 2| + |X₀ - X| :=
            abs_add_le _ _
      _ = (2 - Real.sqrt (4 - (Y + σ * ε * p) ^ 2)) + |X - X₀| := by
        rw [abs_of_nonpos (sub_nonpos.mpr hsqrt_le), abs_sub_comm]
        ring
      _ ≤ (Y + σ * ε * p) ^ 2 / 2 + |X - X₀| :=
        by
          calc
            2 - Real.sqrt (4 - (Y + σ * ε * p) ^ 2) + |X - X₀| =
                |X - X₀| + (2 - Real.sqrt (4 - (Y + σ * ε * p) ^ 2)) := by ring
            _ ≤ |X - X₀| + (Y + σ * ε * p) ^ 2 / 2 :=
              add_le_add_right hroot_error |X - X₀|
            _ = (Y + σ * ε * p) ^ 2 / 2 + |X - X₀| := by ring
      _ = |X - X₀| + (Y + σ * ε * p) ^ 2 / 2 := by ring
  have hcoef : |σ / ε| = 1 / ε := by
    rw [abs_div, hsigma, abs_of_pos hε]
  calc
    |rootValue σ ε X Y p - A * σ| =
        |σ / ε| *
          |Real.sqrt (4 - (Y + σ * ε * p) ^ 2) - 2 + (X₀ - X)| := by
      rw [hlin, abs_mul]
    _ = (1 / ε) *
        |Real.sqrt (4 - (Y + σ * ε * p) ^ 2) - 2 + (X₀ - X)| := by
      rw [hcoef]
    _ ≤ (1 / ε) *
        (|X - X₀| + (Y + σ * ε * p) ^ 2 / 2) := by
      exact mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = (|X - X₀| + (Y + σ * ε * p) ^ 2 / 2) / ε := by ring

end
end StructuralNote.FixedSchurScalarRoot
