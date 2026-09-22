import StructuralNote.FixedSchurFirstSourceMoments

/-! The quantitative first-variation estimate for a solution of the actual
linearized equation. The chosen-path equation is connected separately. -/

namespace StructuralNote.FixedSchurFirstDerivativeBounds

open Filter Complex Erdos1045.EventualExact FiniteBox SchurSpectrum SchurLiftBounds
open CommonDomainClosure CommonDomainRadius
open FixedSchurFirstSource FixedSchurFirstSourceMoments FixedSchurRotatedCoefficients
open FixedSchurRotatedInverse
open scoped BigOperators Topology

noncomputable section

theorem sqrt_rate_bound {n b E A X : ℝ} (hn : 0 < n) (hb : 0 ≤ b)
    (hE : 0 ≤ E) (hA : 0 ≤ A) (hX : X ≤ 80000 * E / n + 96 * b ^ 2 * A / n ^ 3) :
    Real.sqrt X ≤ 300 * (Real.sqrt E / Real.sqrt n) +
      10 * (b * Real.sqrt A / (n * Real.sqrt n)) := by
  let x := Real.sqrt E / Real.sqrt n
  let y := b * Real.sqrt A / (n * Real.sqrt n)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hxsq : x ^ 2 = E / n := by
    dsimp [x]
    rw [div_pow, Real.sq_sqrt hE, Real.sq_sqrt hn.le]
  have hysq : y ^ 2 = b ^ 2 * A / n ^ 3 := by
    dsimp [y]
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hn.le]
    ring
  change Real.sqrt X ≤ 300 * x + 10 * y
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity, ?_⟩
  have hbudget : X ≤ 80000 * x ^ 2 + 96 * y ^ 2 := by
    rw [hxsq, hysq]
    exact hX.trans_eq (by ring)
  nlinarith only [hbudget, sq_nonneg x, sq_nonneg y, mul_nonneg hx hy]

theorem eventual_first_solution_meanSquare :
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      (∑ j, (η j : ℂ) = 0) → ∀ q : Fin (2 * m) → ℝ,
      normalLinearization (by omega) s θ v q = source (by omega) s θ η v h →
      meanSquare q ≤
        80000 * pairEnergy (by omega) (fun j => (η j : ℂ)) / (2 * m : ℝ) +
        96 * betaBudget (2 * m) ^ 2 * pairEnergy (by omega) h / (2 * m : ℝ) ^ 3 := by
  filter_upwards [eventual_source_meanSquare, eventual_actual_coefficients_small]
    with m hsource hcoeff
  intro hm s θ η v h hdom hmean q hq
  have hc := hcoeff hm s θ v hdom
  have hnorm := solution_meanSquare_bound (show 0 < 2 * m by omega)
    (coefficientA (by omega) s θ v) (coefficientB (by omega) s θ v) q
    (fun j => (hc j).1) (fun j => (hc j).2.1)
  change meanSquare q ≤ 4 * meanSquare (normalLinearization (by omega) s θ v q) at hnorm
  rw [hq] at hnorm
  exact (hnorm.trans (mul_le_mul_of_nonneg_left
    (hsource hm s θ η v h hdom hmean) (by norm_num))).trans_eq (by ring)

theorem eventual_first_solution_l2 :
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      (∑ j, (η j : ℂ) = 0) → ∀ q : Fin (2 * m) → ℝ,
      normalLinearization (by omega) s θ v q = source (by omega) s θ η v h →
      Real.sqrt (meanSquare q) ≤ 2000 *
        (Real.sqrt (pairEnergy (by omega) (fun j => (η j : ℂ))) / Real.sqrt (2 * m : ℝ) +
          (logOrder (2 * m) : ℝ) * Real.sqrt (1 + Real.log (2 * m : ℝ)) *
            Real.sqrt (pairEnergy (by omega) h) / ((2 * m : ℝ) * Real.sqrt (2 * m : ℝ))) := by
  filter_upwards [eventual_first_solution_meanSquare] with m hbound
  intro hm s θ η v h hdom hmean q hq
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hE := pairEnergy_nonneg (show 0 < 2 * m by omega) (fun j => (η j : ℂ))
  have hA := pairEnergy_nonneg (show 0 < 2 * m by omega) h
  have hbase := sqrt_rate_bound hn (betaBudget_nonneg (2 * m)) hE hA
    (hbound hm s θ η v h hdom hmean q hq)
  have hb := betaBudget_le (show 1 ≤ 2 * m by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hb
  have hbr := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg (pairEnergy (by omega) h)))
    (show 0 ≤ (2 * m : ℝ) * Real.sqrt (2 * m : ℝ) by positivity)
  have hx : 0 ≤ Real.sqrt (pairEnergy (by omega) (fun j => (η j : ℂ))) /
      Real.sqrt (2 * m : ℝ) := by positivity
  have hy : 0 ≤ (logOrder (2 * m) : ℝ) * Real.sqrt (1 + Real.log (2 * m : ℝ)) *
      Real.sqrt (pairEnergy (by omega) h) / ((2 * m : ℝ) * Real.sqrt (2 * m : ℝ)) := by positivity
  ring_nf at hbase hbr hx hy ⊢
  linarith only [hbase, hbr, hx, hy]

end
end StructuralNote.FixedSchurFirstDerivativeBounds
