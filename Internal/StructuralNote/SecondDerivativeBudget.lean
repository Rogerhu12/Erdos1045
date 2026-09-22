import StructuralNote.CommonFiberDerivativeEnergy

/-! Scalar summation estimates at the scales of the actual first derivatives. -/

namespace StructuralNote.SecondDerivativeBudget

open scoped BigOperators
noncomputable section

theorem mixed_sum_bound {ι : Type*} [Fintype ι] (a u : ι → ℝ) {n E A : ℝ}
    (hn : 1 ≤ n) (hE : 0 ≤ E) (hA : 0 ≤ A)
    (ha : n * (∑ j, a j ^ 2) ≤ 4 * E)
    (hu : n ^ 2 * (∑ j, u j ^ 2) ≤ 400000 / n * E + 400000 * A) :
    n * (∑ j, |a j| * |u j|) ≤
      2000 * (Real.sqrt (A * E) / Real.sqrt n + E / n) := by
  have hn0 : 0 < n := by linarith
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => |a j|) (fun j => |u j|)
  simp only [sq_abs] at hs
  have hprod := mul_le_mul ha hu (by positivity : 0 ≤ n ^ 2 * ∑ j, u j ^ 2)
    (by positivity : 0 ≤ 4 * E)
  have hscaled := mul_le_mul_of_nonneg_left hs (show 0 ≤ n ^ 3 by positivity)
  have hbound : (n * (∑ j, |a j| * |u j|)) ^ 2 ≤
      1600000 * (A * E / n + E ^ 2 / n ^ 2) := by
    apply (mul_le_mul_iff_left₀ hn0).mp
    have he : (1600000 * (A * E / n + E ^ 2 / n ^ 2)) * n =
        4 * E * (400000 / n * E + 400000 * A) := by field_simp; ring
    rw [he]
    nlinarith only [hprod, hscaled]
  have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hr : (Real.sqrt (A * E) / Real.sqrt n) ^ 2 = A * E / n := by
    rw [div_pow, Real.sq_sqrt (mul_nonneg hA hE), Real.sq_sqrt hn0.le]
  have ht : (E / n) ^ 2 = E ^ 2 / n ^ 2 := div_pow E n 2
  have hc : 0 ≤ Real.sqrt (A * E) / Real.sqrt n * (E / n) := by positivity
  have hnonneg : 0 ≤ 2000 * (Real.sqrt (A * E) / Real.sqrt n + E / n) := by positivity
  apply (sq_le_sq₀ (by positivity) hnonneg).mp
  nlinarith [sq_nonneg (Real.sqrt (A * E) / Real.sqrt n), sq_nonneg (E / n)]

theorem acceleration_budget {n E A X Y U M Z : ℝ} (hn : 1 ≤ n)
    (hE : 0 ≤ E) (hA : 0 ≤ A) (hY : 0 ≤ Y)
    (hXbound : n * X ≤ 4 * E) (hYbound : n ^ 2 * Y ≤ 128 * E)
    (hUbound : n ^ 2 * U ≤ 400000 / n * E + 400000 * A)
    (hMbound : n * M ≤ 2000 * (Real.sqrt (A * E) / Real.sqrt n + E / n))
    (hZbound : Z ≤ (2 / n + 5 / n) * X + (5 / n + 1) * Y + 4 * M + 4 * U) :
    36 * n * Z ≤ 1000000000 * ((A + E) / n + Real.sqrt (A * E) / Real.sqrt n) := by
  have hn0 : 0 < n := by linarith
  have hX : X ≤ 4 * E / n := (le_div_iff₀ hn0).mpr (by nlinarith only [hXbound])
  have hEn : E / n ≤ E := div_le_self hE hn
  have hNY : n * Y ≤ 128 * E / n := (le_div_iff₀ hn0).mpr (by nlinarith only [hYbound])
  have hY' : (5 + n) * Y ≤ 768 * E / n := by
    have hmul := mul_le_mul_of_nonneg_right (show 5 + n ≤ 6 * n by linarith) hY
    simp only [div_eq_mul_inv] at hNY ⊢
    nlinarith only [hmul, hNY]
  have hNU : n * U ≤ 400000 * (A + E) / n := by
    apply (le_div_iff₀ hn0).mpr
    have he : 400000 / n * E = 400000 * (E / n) := by ring
    rw [he] at hUbound
    nlinarith only [hUbound, hEn]
  have hZ := mul_le_mul_of_nonneg_left hZbound hn0.le
  have he : n * ((2 / n + 5 / n) * X + (5 / n + 1) * Y + 4 * M + 4 * U) =
      7 * X + (5 + n) * Y + 4 * (n * M) + 4 * (n * U) := by field_simp; ring
  rw [he] at hZ
  have hJ : E / n ≤ (A + E) / n := div_le_div_of_nonneg_right (by linarith) hn0.le
  have hR : 0 ≤ Real.sqrt (A * E) / Real.sqrt n := by positivity
  have hJ0 : 0 ≤ (A + E) / n := by positivity
  simp only [div_eq_mul_inv] at hX hY' hNU hMbound hJ hR hJ0 ⊢
  nlinarith only [hX, hY', hNU, hMbound, hZ, hJ, hR, hJ0]

end
end StructuralNote.SecondDerivativeBudget
