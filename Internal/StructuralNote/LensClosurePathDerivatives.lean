import StructuralNote.LensIncrementDerivatives

/-! Differentiating the actual moving closure equation. The closure correction
is solved by the actual Jacobian, and its norm is bounded by the direct source. -/

namespace StructuralNote.LensClosurePathDerivatives

open Erdos1045.EventualExact Complex LensClosure LensIncrementDerivatives Filter
open scoped BigOperators Topology
noncomputable section

theorem velocity_split (α L σ t a l u v : ℝ) :
    incrementVelocity α L σ t a l (u + v) =
      incrementVelocity α L σ t a l u + (v : ℂ) * tangent α σ t := by
  unfold incrementVelocity bodyVelocity tangent heightSlope
  push_cast
  ring

theorem acceleration_split (α L σ t a l u aa ll uu v : ℝ) :
    incrementAcceleration α L σ t a l u aa ll (uu + v) =
      incrementAcceleration α L σ t a l u aa ll uu + (v : ℂ) * tangent α σ t := by
  unfold incrementAcceleration bodyAcceleration tangent heightSlope
  push_cast
  ring

theorem heightParameter_hasDerivAt {m : ℕ} {ν : ℝ → Fin m → ℝ} {ξ : ℝ → ℂ}
    {x : ℝ} {ν' : Fin m → ℝ} {ξ' : ℂ}
    (hν : ∀ j, HasDerivAt (fun s => ν s j) (ν' j) x) (hξ : HasDerivAt ξ ξ' x) (j : Fin m) :
    HasDerivAt (fun s => heightParameter (ν s) (ξ s) j)
      (heightParameter ν' ξ' j) x := by
  exact (hν j).add ((harmonicFunctional (midpoint m j)).hasFDerivAt.comp_hasDerivAt x hξ)

theorem closureDerivative_apply_sum {m : ℕ} (α σ ν : Fin m → ℝ) (ξ ξ' : ℂ) :
    closureDerivative α σ ν ξ ξ' =
      ∑ j, (harmonicFunctional (midpoint m j) ξ' : ℂ) *
        tangent (α j) (σ j) (heightParameter ν ξ j) := by
  simp only [closureDerivative, sum_apply, ContinuousLinearMap.smulRight_apply,
    Complex.real_smul]

theorem closure_path_hasDerivAt {m : ℕ} {α L ν : ℝ → Fin m → ℝ}
    {ξ : ℝ → ℂ} {x : ℝ} (σ α' L' ν' : Fin m → ℝ) {ξ' : ℂ}
    (hα : ∀ j, HasDerivAt (fun s => α s j) (α' j) x)
    (hL : ∀ j, HasDerivAt (fun s => L s j) (L' j) x)
    (hν : ∀ j, HasDerivAt (fun s => ν s j) (ν' j) x) (hξ : HasDerivAt ξ ξ' x)
    (ht : ∀ j, heightParameter (ν x) (ξ x) j ^ 2 < 4) :
    HasDerivAt (fun s => closure (α s) (L s) σ (ν s) (ξ s))
      ((∑ j, incrementVelocity (α x j) (L x j) (σ j)
        (heightParameter (ν x) (ξ x) j) (α' j) (L' j) (ν' j)) +
        closureDerivative (α x) σ (ν x) (ξ x) ξ') x := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    LensIncrementDerivatives.increment_hasDerivAt (σ j) (hα j) (hL j)
      (heightParameter_hasDerivAt hν hξ j) (ht j))
  change HasDerivAt (fun s => closure (α s) (L s) σ (ν s) (ξ s)) _ x at hd
  apply hd.congr_deriv
  simp only [heightParameter, velocity_split, Finset.sum_add_distrib,
    closureDerivative_apply_sum]

theorem closure_path_derivative_eq {m : ℕ} {α L ν : ℝ → Fin m → ℝ}
    {ξ : ℝ → ℂ} {x : ℝ} (σ α' L' ν' : Fin m → ℝ) {ξ' : ℂ}
    (hα : ∀ j, HasDerivAt (fun s => α s j) (α' j) x)
    (hL : ∀ j, HasDerivAt (fun s => L s j) (L' j) x)
    (hν : ∀ j, HasDerivAt (fun s => ν s j) (ν' j) x) (hξ : HasDerivAt ξ ξ' x)
    (ht : ∀ j, heightParameter (ν x) (ξ x) j ^ 2 < 4)
    (hz : ∀ᶠ s in 𝓝 x, closure (α s) (L s) σ (ν s) (ξ s) = 0) :
    closureDerivative (α x) σ (ν x) (ξ x) ξ' =
      -∑ j, incrementVelocity (α x j) (L x j) (σ j)
        (heightParameter (ν x) (ξ x) j) (α' j) (L' j) (ν' j) := by
  have hd := closure_path_hasDerivAt σ α' L' ν' hα hL hν hξ ht
  have hc : HasDerivAt (fun s => closure (α s) (L s) σ (ν s) (ξ s)) 0 x :=
    (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq hz
  have he := hd.unique hc
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using he)

theorem correction_bound {m : ℕ} (hm : 2 ≤ m) (α σ ν : Fin m → ℝ) (ξ v : ℂ)
    (source : Fin m → ℂ) (hσ : ∀ j, |σ j| ≤ 1)
    (hsmall : ∀ j, |α j - midpoint m j| + |heightParameter ν ξ j| ≤ 1 / 4)
    (heq : closureDerivative α σ ν ξ v = -∑ j, source j) :
    ‖v‖ ≤ (4 / m : ℝ) * ∑ j, ‖source j‖ := by
  have ht (j : Fin m) : |heightParameter ν ξ j| ≤ 1 := by
    have := hsmall j
    linarith [abs_nonneg (α j - midpoint m j)]
  have hb := closureDerivative_lower hm α σ ν ξ v
    (fun j => (tangent_error (hσ j) (ht j)).trans (hsmall j))
  rw [heq, norm_neg] at hb
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hmR).mpr
  have hs := norm_sum_le Finset.univ source
  nlinarith

theorem tangent_norm_le {α μ σ t : ℝ} (hσ : |σ| ≤ 1)
    (hsmall : |α - μ| + |t| ≤ 1 / 4) : ‖tangent α σ t‖ ≤ 2 := by
  have ht : |t| ≤ 1 := by linarith [abs_nonneg (α - μ)]
  have he := (tangent_error hσ ht).trans hsmall
  have hn := norm_le_norm_sub_add (tangent α σ t) (unit μ * I)
  simp only [norm_mul, norm_unit, norm_I, mul_one] at hn
  linarith

theorem corrected_source_l1 {m : ℕ} (hm : 2 ≤ m) (α σ ν : Fin m → ℝ) (ξ v : ℂ)
    (source : Fin m → ℂ) (hσ : ∀ j, |σ j| ≤ 1)
    (hsmall : ∀ j, |α j - midpoint m j| + |heightParameter ν ξ j| ≤ 1 / 4)
    (heq : closureDerivative α σ ν ξ v = -∑ j, source j) :
    (∑ j, ‖source j + (harmonicFunctional (midpoint m j) v : ℂ) *
      tangent (α j) (σ j) (heightParameter ν ξ j)‖) ≤ 9 * ∑ j, ‖source j‖ := by
  have hv := correction_bound hm α σ ν ξ v source hσ hsmall heq
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have he (j : Fin m) :
      ‖source j + (harmonicFunctional (midpoint m j) v : ℂ) *
        tangent (α j) (σ j) (heightParameter ν ξ j)‖ ≤ ‖source j‖ + 2 * ‖v‖ := by
    refine (norm_add_le _ _).trans (add_le_add_right ?_ _)
    rw [norm_mul, norm_real, Real.norm_eq_abs]
    exact (mul_le_mul (harmonicFunctional_le_norm _ _) (tangent_norm_le (hσ j) (hsmall j))
      (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_comm _ _)
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => he j)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hs
  have hv' : (m : ℝ) * ‖v‖ ≤ 4 * ∑ j, ‖source j‖ := by
    have := (le_div_iff₀ hmR).mp (show ‖v‖ ≤ (4 * ∑ j, ‖source j‖) / m by
      simpa only [div_mul_eq_mul_div] using hv)
    nlinarith
  nlinarith

theorem correction_square_bound {m : ℕ} (hm : 2 ≤ m) (α σ ν : Fin m → ℝ) (ξ v : ℂ)
    (source : Fin m → ℂ) (hσ : ∀ j, |σ j| ≤ 1)
    (hsmall : ∀ j, |α j - midpoint m j| + |heightParameter ν ξ j| ≤ 1 / 4)
    (heq : closureDerivative α σ ν ξ v = -∑ j, source j) :
    (m : ℝ) * ‖v‖ ^ 2 ≤ 16 * ∑ j, ‖source j‖ ^ 2 := by
  have hv := correction_bound hm α σ ν ξ v source hσ hsmall heq
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hv' : ‖v‖ * (m : ℝ) ≤ 4 * ∑ j, ‖source j‖ :=
    (le_div_iff₀ hmR).mp (by simpa only [div_mul_eq_mul_div] using hv)
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j : Fin m => ‖source j‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hs
  have hvs := pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) hmR.le) hv' 2
  apply (mul_le_mul_iff_left₀ hmR).mp
  nlinarith

theorem corrected_source_l2 {m : ℕ} (hm : 2 ≤ m) (α σ ν : Fin m → ℝ) (ξ v : ℂ)
    (source : Fin m → ℂ) (hσ : ∀ j, |σ j| ≤ 1)
    (hsmall : ∀ j, |α j - midpoint m j| + |heightParameter ν ξ j| ≤ 1 / 4)
    (heq : closureDerivative α σ ν ξ v = -∑ j, source j) :
    (∑ j, ‖source j + (harmonicFunctional (midpoint m j) v : ℂ) *
      tangent (α j) (σ j) (heightParameter ν ξ j)‖ ^ 2) ≤
        130 * ∑ j, ‖source j‖ ^ 2 := by
  have hv := correction_square_bound hm α σ ν ξ v source hσ hsmall heq
  have he (j : Fin m) :
      ‖source j + (harmonicFunctional (midpoint m j) v : ℂ) *
        tangent (α j) (σ j) (heightParameter ν ξ j)‖ ^ 2 ≤
      2 * ‖source j‖ ^ 2 + 8 * ‖v‖ ^ 2 := by
    have hb : ‖(harmonicFunctional (midpoint m j) v : ℂ) *
        tangent (α j) (σ j) (heightParameter ν ξ j)‖ ≤ 2 * ‖v‖ := by
      rw [norm_mul, norm_real, Real.norm_eq_abs]
      exact (mul_le_mul (harmonicFunctional_le_norm _ _) (tangent_norm_le (hσ j) (hsmall j))
        (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_comm _ _)
    have hnorm := (norm_add_le (source j) _).trans (add_le_add_right hb _)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    nlinarith [sq_nonneg (‖source j‖ - 2 * ‖v‖)]
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => he j)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hs
  nlinarith

theorem velocity_residual_eq (α μ L σ t a l u : ℝ) :
    incrementVelocity α L σ t a l u - (u : ℂ) * (unit μ * I) =
      unit α * ((a : ℂ) * I * body L σ t - ((σ * l : ℝ) : ℂ)) +
        (u : ℂ) * (tangent α σ t - unit μ * I) := by
  unfold incrementVelocity bodyVelocity heightSlope tangent
  push_cast
  ring

theorem velocity_residual_bound {α μ L σ t a l u : ℝ}
    (hσ : |σ| ≤ 1) (ht : |t| ≤ 1) :
    ‖incrementVelocity α L σ t a l u - (u : ℂ) * (unit μ * I)‖ ≤
      |a| * ‖body L σ t‖ + |l| + |u| * (|α - μ| + |t|) := by
  rw [velocity_residual_eq]
  calc
    _ ≤ ‖unit α * ((a : ℂ) * I * body L σ t - ((σ * l : ℝ) : ℂ))‖ +
        ‖(u : ℂ) * (tangent α σ t - unit μ * I)‖ := norm_add_le _ _
    _ = ‖(a : ℂ) * I * body L σ t - ((σ * l : ℝ) : ℂ)‖ +
        |u| * ‖tangent α σ t - unit μ * I‖ := by simp only [norm_mul, norm_unit,
          one_mul, norm_real, Real.norm_eq_abs]
    _ ≤ (‖(a : ℂ) * I * body L σ t‖ + ‖((σ * l : ℝ) : ℂ)‖) +
        |u| * (|α - μ| + |t|) :=
      add_le_add (norm_sub_le _ _) (mul_le_mul_of_nonneg_left (tangent_error hσ ht) (abs_nonneg _))
    _ ≤ _ := by
      simp only [norm_mul, norm_real, Real.norm_eq_abs, norm_I, mul_one]
      nlinarith [abs_nonneg l]

end
end StructuralNote.LensClosurePathDerivatives
