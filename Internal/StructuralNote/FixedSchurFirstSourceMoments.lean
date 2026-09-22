import StructuralNote.FixedSchurFirstSource

/-! The first-variation source is bounded in normalized mean square using
the actual direction energies, before applying the linearized inverse. -/

namespace StructuralNote.FixedSchurFirstSourceMoments

open Filter Complex Erdos1045.EventualExact FiniteBox SchurSpectrum SchurLiftBounds
open CommonDomainClosure CommonDomainRadius CommonClosureEnergy EdgeCoordinates
open FixedSchurNormalInnerEnergy FixedSchurFirstSource FixedSchurDirectionMoments
open FixedSchurRotatedCoefficients
open scoped BigOperators Topology

noncomputable section

theorem source_meanSquare_of_coefficients {m : ℕ} (hm : 0 < m) (s : SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (hmean : ∑ j, (η j : ℂ) = 0)
    (hc : ∀ j, |angularCoefficient hm s θ j| ≤ 2 * (2 * m : ℝ) ∧
      |coefficientB hm s θ v j| ≤ betaBudget (2 * m) / (2 * m : ℝ) ^ 2 ∧
      |rotationCoefficient hm s θ v j| ≤ 36 * (logOrder (2 * m) : ℝ)) :
    meanSquare (source hm s θ η v h) ≤
      96 * Real.pi ^ 2 * pairEnergy (by omega) (fun j => (η j : ℂ)) / (2 * m : ℝ) +
      (3 * Real.pi ^ 2 / 2) * betaBudget (2 * m) ^ 2 * pairEnergy (by omega) h / (2 * m : ℝ) ^ 3 +
      15552 * (logOrder (2 * m) : ℝ) ^ 2 *
        pairEnergy (by omega) (fun j => (η j : ℂ)) / (2 * m : ℝ) ^ 2 := by
  let f : Fin (2 * m) → ℝ := fun j => angularCoefficient hm s θ j * angleDifference (by omega) η j
  let g : Fin (2 * m) → ℝ := fun j => coefficientB hm s θ v j * tangent (by omega) h j
  let w : Fin (2 * m) → ℝ := fun j => rotationCoefficient hm s θ v j * angleAverage (by omega) η j
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hbeta := betaBudget_nonneg (2 * m)
  have hf : meanSquare f ≤ (2 * (2 * m : ℝ)) ^ 2 *
      (8 * Real.pi ^ 2 * pairEnergy (by omega) (fun j => (η j : ℂ)) / (2 * m : ℝ) ^ 3) := by
    have hdom : meanSquare f ≤ (2 * (2 * m : ℝ)) ^ 2 * meanSquare (angleDifference (by omega) η) := by
      apply meanSquare_domination f _ (by positivity)
      intro j
      dsimp [f]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hc j).1 (abs_nonneg _)
    apply hdom.trans
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using angleDifference_meanSquare_le (by omega) η
  have hg : meanSquare g ≤ (betaBudget (2 * m) / (2 * m : ℝ) ^ 2) ^ 2 *
      ((Real.pi ^ 2 / 2) * (2 * m : ℝ) * pairEnergy (by omega) h) := by
    have hdom : meanSquare g ≤ (betaBudget (2 * m) / (2 * m : ℝ) ^ 2) ^ 2 *
        meanSquare (tangent (by omega) h) := by
      apply meanSquare_domination g _ (by positivity)
      intro j
      dsimp [g]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hc j).2.1 (abs_nonneg _)
    apply hdom.trans
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using tangent_meanSquare_le (by omega) h
  have hw : meanSquare w ≤ (36 * (logOrder (2 * m) : ℝ)) ^ 2 *
      (4 * pairEnergy (by omega) (fun j => (η j : ℂ)) / (2 * m : ℝ) ^ 2) := by
    have hdom : meanSquare w ≤ (36 * (logOrder (2 * m) : ℝ)) ^ 2 *
        meanSquare (angleAverage (by omega) η) := by
      apply meanSquare_domination w _ (by positivity)
      intro j
      dsimp [w]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hc j).2.2 (abs_nonneg _)
    apply hdom.trans
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using angleAverage_meanSquare_le (by omega) η hmean
  have hsum := meanSquare_sub_sub_bound f g w
  change meanSquare (source hm s θ η v h) ≤ _ at hsum
  apply hsum.trans
  calc
    _ ≤ 3 * ((2 * (2 * m : ℝ)) ^ 2 *
        (8 * Real.pi ^ 2 * pairEnergy (by omega) (fun j => (η j : ℂ)) / (2 * m : ℝ) ^ 3)) +
        3 * ((betaBudget (2 * m) / (2 * m : ℝ) ^ 2) ^ 2 *
          ((Real.pi ^ 2 / 2) * (2 * m : ℝ) * pairEnergy (by omega) h)) +
        3 * ((36 * (logOrder (2 * m) : ℝ)) ^ 2 *
          (4 * pairEnergy (by omega) (fun j => (η j : ℂ)) / (2 * m : ℝ) ^ 2)) := by linarith only [hf, hg, hw]
    _ = _ := by field_simp; ring

theorem eventual_source_meanSquare :
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      (∑ j, (η j : ℂ) = 0) →
      meanSquare (source (by omega) s θ η v h) ≤
        20000 * pairEnergy (by omega) (fun j => (η j : ℂ)) / (2 * m : ℝ) +
        24 * betaBudget (2 * m) ^ 2 * pairEnergy (by omega) h / (2 * m : ℝ) ^ 3 := by
  have hnat : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 2 * m) tendsto_id
  filter_upwards [eventual_source_coefficients, hnat.eventually eventual_radius_le_inverse]
    with m hcoeff hrad
  intro hm s θ η v h hdom hmean
  have hsource := source_meanSquare_of_coefficients (by omega) s θ η v h hmean
    (hcoeff hm s θ v hdom)
  have hE := pairEnergy_nonneg (show 0 < 2 * m by omega) (fun j => (η j : ℂ))
  have hA := pairEnergy_nonneg (show 0 < 2 * m by omega) h
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hpi : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hfirst := mul_le_mul_of_nonneg_right hpi
    (show 0 ≤ pairEnergy (by omega) (fun j => (η j : ℂ)) / (2 * m : ℝ) by positivity)
  have hsecond := mul_le_mul_of_nonneg_right hpi
    (show 0 ≤ betaBudget (2 * m) ^ 2 * pairEnergy (by omega) h / (2 * m : ℝ) ^ 3 by positivity)
  have hthird := mul_le_mul_of_nonneg_right hrad hE
  simp only [energyRadius, Nat.cast_mul, Nat.cast_ofNat] at hthird
  have hnonneg := div_nonneg hE hn.le
  ring_nf at hsource hfirst hsecond hthird hnonneg ⊢
  linarith only [hsource, hfirst, hsecond, hthird, hnonneg]

end
end StructuralNote.FixedSchurFirstSourceMoments
