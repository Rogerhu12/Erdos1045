import StructuralNote.FixedSchurFirstDerivativeBounds

/-! Supremum control for the actual first-variation source. The estimate
retains the tangential direction's small coefficient. -/

namespace StructuralNote.FixedSchurFirstSourceSup

open Filter Complex Erdos1045.EventualExact FiniteBox SchurSpectrum SchurLiftBounds
open CommonDomainClosure CommonDomainRadius CommonClosureEnergy EdgeCoordinates
open FixedSchurFirstSource FixedSchurDirectionMoments FixedSchurRotatedCoefficients
open FixedSchurRotatedInverse
open scoped BigOperators Topology

noncomputable section

theorem source_pointwise_sq_of_coefficients {m : ℕ} (hm : 0 < m) (s : SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (hmean : ∑ j, (η j : ℂ) = 0) (j : Fin (2 * m))
    (hc : |angularCoefficient hm s θ j| ≤ 2 * (2 * m : ℝ) ∧
      |coefficientB hm s θ v j| ≤ betaBudget (2 * m) / (2 * m : ℝ) ^ 2 ∧
      |rotationCoefficient hm s θ v j| ≤ 36 * (logOrder (2 * m) : ℝ)) :
    source hm s θ η v h j ^ 2 ≤
      96 * Real.pi ^ 2 * pairEnergy (by omega) (fun j => (η j : ℂ)) +
      (3 * Real.pi ^ 2 / 2) * betaBudget (2 * m) ^ 2 * pairEnergy (by omega) h / (2 * m : ℝ) ^ 2 +
      46656 * (logOrder (2 * m) : ℝ) ^ 2 * Real.log (2 * m : ℝ) *
        pairEnergy (by omega) (fun j => (η j : ℂ)) / (2 * m : ℝ) ^ 2 := by
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hf := pow_le_pow_left₀ (abs_nonneg _) hc.1 2
  have hg := pow_le_pow_left₀ (abs_nonneg _) hc.2.1 2
  have hw := pow_le_pow_left₀ (abs_nonneg _) hc.2.2 2
  simp only [sq_abs] at hf hg hw
  have he := angleDifference_pointwise_sq_le (show 0 < 2 * m by omega) η j
  have hp := tangent_pointwise_sq_le (show 2 ≤ 2 * m by omega) h j
  have hu := angleAverage_pointwise_sq_le (show 2 ≤ 2 * m by omega) η hmean j
  simp only [Nat.cast_mul, Nat.cast_ofNat] at he hp hu
  have h₁ := mul_le_mul hf he (sq_nonneg _) (sq_nonneg _)
  have h₂ := mul_le_mul hg hp (sq_nonneg _) (sq_nonneg _)
  have h₃ := mul_le_mul hw hu (sq_nonneg _) (sq_nonneg _)
  have hs : source hm s θ η v h j ^ 2 ≤
      3 * (angularCoefficient hm s θ j * angleDifference (by omega) η j) ^ 2 +
      3 * (coefficientB hm s θ v j * tangent (by omega) h j) ^ 2 +
      3 * (rotationCoefficient hm s θ v j * angleAverage (by omega) η j) ^ 2 := by
    unfold source
    nlinarith [sq_nonneg (angularCoefficient hm s θ j * angleDifference (by omega) η j +
      coefficientB hm s θ v j * tangent (by omega) h j),
      sq_nonneg (angularCoefficient hm s θ j * angleDifference (by omega) η j +
        rotationCoefficient hm s θ v j * angleAverage (by omega) η j),
      sq_nonneg (coefficientB hm s θ v j * tangent (by omega) h j -
        rotationCoefficient hm s θ v j * angleAverage (by omega) η j)]
  simp only [mul_pow] at hs
  apply hs.trans
  calc
    _ ≤ 3 * ((2 * (2 * m : ℝ)) ^ 2 *
        (8 * Real.pi ^ 2 * pairEnergy (by omega) (fun j => (η j : ℂ)) / (2 * m : ℝ) ^ 2)) +
      3 * ((betaBudget (2 * m) / (2 * m : ℝ) ^ 2) ^ 2 *
        ((Real.pi ^ 2 / 2) * (2 * m : ℝ) ^ 2 * pairEnergy (by omega) h)) +
      3 * ((36 * (logOrder (2 * m) : ℝ)) ^ 2 *
        (12 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 * pairEnergy (by omega) (fun j => (η j : ℂ)))) := by
          linarith only [h₁, h₂, h₃]
    _ = _ := by field_simp; ring

theorem eventual_source_pointwise_sq :
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      (∑ j, (η j : ℂ) = 0) → ∀ j,
      source (by omega) s θ η v h j ^ 2 ≤
        50000 * pairEnergy (by omega) (fun j => (η j : ℂ)) +
        24 * betaBudget (2 * m) ^ 2 * pairEnergy (by omega) h / (2 * m : ℝ) ^ 2 := by
  have hnat : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 2 * m) tendsto_id
  filter_upwards [eventual_source_coefficients, hnat.eventually eventual_radius_le_inverse]
    with m hcoeff hrad
  intro hm s θ η v h hdom hmean j
  have hs := source_pointwise_sq_of_coefficients (by omega) s θ η v h hmean j (hcoeff hm s θ v hdom j)
  have hE := pairEnergy_nonneg (show 0 < 2 * m by omega) (fun j => (η j : ℂ))
  have hA := pairEnergy_nonneg (show 0 < 2 * m by omega) h
  have hn : (1 : ℝ) ≤ 2 * m := by exact_mod_cast (show 1 ≤ 2 * m by omega)
  have hnpos : (0 : ℝ) < 2 * m := by linarith
  have hlog : 0 ≤ Real.log (2 * m : ℝ) := Real.log_nonneg hn
  have hlogle : Real.log (2 * m : ℝ) / (2 * m : ℝ) ≤ 1 :=
    (div_le_iff₀ hnpos).2 (by linarith [Real.log_le_sub_one_of_pos hnpos])
  have hLlog := mul_le_mul_of_nonneg_right hrad hlog
  simp only [energyRadius, Nat.cast_mul, Nat.cast_ofNat] at hLlog
  have hratio : (logOrder (2 * m) : ℝ) ^ 2 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 ≤ 1 := by
    ring_nf at hLlog hlogle ⊢
    linarith only [hLlog, hlogle]
  have hpi : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hfirst := mul_le_mul_of_nonneg_right hpi hE
  have hsecond := mul_le_mul_of_nonneg_right hpi
    (show 0 ≤ betaBudget (2 * m) ^ 2 * pairEnergy (by omega) h / (2 * m : ℝ) ^ 2 by positivity)
  have hthird := mul_le_mul_of_nonneg_right hratio hE
  ring_nf at hs hfirst hsecond hthird ⊢
  linarith only [hs, hfirst, hsecond, hthird, hE]

theorem norm_sq_le_of_pointwise {n : ℕ} (q : Fin n → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hq : ∀ j, q j ^ 2 ≤ C) : ‖q‖ ^ 2 ≤ C := by
  have hnorm : ‖q‖ ≤ Real.sqrt C := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
    intro j
    rw [Real.norm_eq_abs]
    exact (Real.le_sqrt (abs_nonneg _) hC).2 (by simpa only [sq_abs] using hq j)
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans_eq (Real.sq_sqrt hC)

theorem eventual_first_solution_sup_sq :
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      (∑ j, (η j : ℂ) = 0) → ∀ q : Fin (2 * m) → ℝ,
      normalLinearization (by omega) s θ v q = source (by omega) s θ η v h →
      ‖q‖ ^ 2 ≤
        200000 * pairEnergy (by omega) (fun j => (η j : ℂ)) +
        96 * betaBudget (2 * m) ^ 2 * pairEnergy (by omega) h / (2 * m : ℝ) ^ 2 := by
  filter_upwards [eventual_source_pointwise_sq, eventual_actual_solution_bounds] with m hsource hinv
  intro hm s θ η v h hdom hmean q heq
  have hE := pairEnergy_nonneg (show 0 < 2 * m by omega) (fun j => (η j : ℂ))
  have hA := pairEnergy_nonneg (show 0 < 2 * m by omega) h
  have hS := norm_sq_le_of_pointwise (source (by omega) s θ η v h) (by positivity)
    (hsource hm s θ η v h hdom hmean)
  have hnorm := (hinv hm s θ v hdom q).2.2
  rw [heq] at hnorm
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  ring_nf at hsq hS ⊢
  linarith only [hsq, hS]

end
end StructuralNote.FixedSchurFirstSourceSup
