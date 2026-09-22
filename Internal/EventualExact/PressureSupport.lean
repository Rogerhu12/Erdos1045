import EventualExact.FiniteBoxMaximum
import EventualExact.LensAlgebra

/-! Actual supporting prices for the finite box and the two cross-distance constraints. -/

noncomputable section
open scoped BigOperators

namespace Erdos1045.EventualExact.PressureSupport

open FourierMultiplier FiniteBox Complex

theorem quadratic_support {ι : Type*} [Fintype ι]
    {T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} (hs : FiniteSelfAdjoint T)
    (hp : FinitePositiveSemidefinite T) (q f : ι → ℝ) :
    boxEnergy T q ≤ boxEnergy T f + finitePairing (q - f) (T q) := by
  have he := boxEnergy_sub hs q f
  have hpos := boxEnergy_nonneg hp (f - q)
  have hpair : finitePairing (f - q) (T q) = -finitePairing (q - f) (T q) := by
    simp only [finitePairing, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [hpair] at he
  linarith

/-- Manuscript (5.8) for the concrete finite Schur operator and its attained box maximum.
The column q need not itself lie in the box. -/
theorem box_support {m : ℕ} (hm : 0 < m) (q : Fin (2 * m) → ℝ) :
    normalizedBoxEnergy (operator (2 * m)) q ≤ B hm +
      (finitePairing q (operator (2 * m) q) -
        amplitude (2 * m) * ∑ j, |operator (2 * m) q j|) / (2 * m : ℕ) := by
  let A := amplitude (2 * m)
  let g := operator (2 * m) q
  let s := patternSign (seedPattern hm)
  let f := roundedBoxVertex A s g
  have hs : IsSignVector s := patternSign_is_sign _
  have hf : ∀ j, |f j| ≤ A := roundedBoxVertex_mem_box (amplitude_pos (by omega)).le hs g
  have hB := energy_le_maximum hm f hf
  have hp := quadratic_support (selfAdjoint (2 * m)) (positiveSemidefinite (2 * m)) q f
  have hpair : finitePairing (q - f) g = finitePairing q g - A * ∑ j, |g j| := by
    simp only [finitePairing, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    change A * roundedSign (s j) (g j) * g j = A * |g j|
    rw [mul_assoc, roundedSign_mul (hs j)]
  change boxEnergy (operator (2 * m)) q ≤ boxEnergy (operator (2 * m)) f +
    finitePairing (q - f) g at hp
  rw [hpair] at hp
  have hn : (0 : ℝ) < (2 * m : ℕ) := by exact_mod_cast (show 0 < 2 * m by omega)
  have hdiv := div_le_div_of_nonneg_right hp hn.le
  rw [add_div] at hdiv
  change normalizedBoxEnergy (operator (2 * m)) q ≤ _
  have hnorm : normalizedBoxEnergy (operator (2 * m)) q ≤
      normalizedBoxEnergy (operator (2 * m)) f +
        (finitePairing q g - A * ∑ j, |g j|) / (2 * m : ℕ) := by
    simpa only [normalizedBoxEnergy, Fintype.card_fin] using hdiv
  exact hnorm.trans (add_le_add hB le_rfl)

theorem scalar_cross_price {x y R t s : ℝ} (hx : 0 < x)
    (hs : s = 1 ∨ s = -1)
    (hp : (x + R) ^ 2 + (y + t) ^ 2 ≤ 4)
    (hm : (x - R) ^ 2 + (y - t) ^ 2 ≤ 4) :
    s * R ≤ 2 / x - x / 2 + (|y| / x) * |t| := by
  have hy : |y * t| = |y| * |t| := abs_mul _ _
  have hprod := abs_le.mp (le_of_eq hy)
  have he : 2 / x - x / 2 + (|y| / x) * |t| =
      (4 - x ^ 2 + 2 * |y| * |t|) / (2 * x) := by field_simp; ring
  rw [he]
  apply (le_div_iff₀ (show 0 < 2 * x by positivity)).mpr
  rcases hs with rfl | rfl <;>
    nlinarith [sq_nonneg y, sq_nonneg R, sq_nonneg t]

theorem actual_cross_price {D B : ℂ} (hx : 0 < D.re) {s : ℝ}
    (hs : s = 1 ∨ s = -1) (hp : ‖D + B‖ ≤ 2) (hm : ‖D - B‖ ≤ 2) :
    s * B.re ≤ 2 / D.re - D.re / 2 + (|D.im| / D.re) * |B.im| := by
  have hps := (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).2 hp
  have hms := (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).2 hm
  rw [Complex.sq_norm] at hps hms
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im] at hps hms
  exact scalar_cross_price hx hs (by nlinarith [hps]) (by nlinarith [hms])

theorem rotated_cross_price {D B u : ℂ} (hu : ‖u‖ = 1)
    (hx : 0 < ((starRingEnd ℂ) u * D).re) {s : ℝ}
    (hs : s = 1 ∨ s = -1) (hp : ‖D + B‖ ≤ 2) (hm : ‖D - B‖ ≤ 2) :
    s * ((starRingEnd ℂ) u * B).re ≤ 2 / ((starRingEnd ℂ) u * D).re -
      ((starRingEnd ℂ) u * D).re / 2 +
      (|((starRingEnd ℂ) u * D).im| / ((starRingEnd ℂ) u * D).re) *
        |((starRingEnd ℂ) u * B).im| := by
  apply actual_cross_price hx hs
  · simpa only [← mul_add, norm_mul, Complex.norm_conj, hu, one_mul] using hp
  · simpa only [← mul_sub, norm_mul, Complex.norm_conj, hu, one_mul] using hm

end Erdos1045.EventualExact.PressureSupport
