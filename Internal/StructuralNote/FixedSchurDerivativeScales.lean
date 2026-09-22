import StructuralNote.FixedSchurFirstSourceSup

/-! Coarser consequences of the sharp first-variation estimates, used to
control products in the second-variation equation. -/

namespace StructuralNote.FixedSchurDerivativeScales

open Filter Complex Erdos1045.EventualExact FiniteBox SchurSpectrum SchurLiftBounds
open CommonDomainClosure CommonDomainRadius HessianErrorLimits
open FixedSchurFirstSource FixedSchurFirstDerivativeBounds FixedSchurFirstSourceSup
open FixedSchurRotatedCoefficients
open scoped BigOperators Topology

noncomputable section

theorem eventual_betaBudget_le_order : ∀ᶠ m : ℕ in atTop,
    betaBudget (2 * m) ≤ (2 * m : ℝ) := by
  have hnat : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 2 * m) tendsto_id
  have hlim : Tendsto (fun m : ℕ =>
      148 * ((logOrder (2 * m) : ℝ) * (1 + Real.log (2 * m : ℝ)) / (2 * m : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Real.rpow_one, Function.comp_def, Nat.cast_mul, Nat.cast_ofNat, mul_zero] using
      ((logOrder_log_div_power_tendsto (p := 1) (by norm_num)).const_mul 148).comp hnat
  filter_upwards [hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    eventually_ge_atTop 1] with m hsmall hm
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hlog : 0 ≤ Real.log (2 * m : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * m by omega))
  have hsqrt : Real.sqrt (1 + Real.log (2 * m : ℝ)) ≤ 1 + Real.log (2 * m : ℝ) := by
    apply (Real.sqrt_le_iff).2
    exact ⟨by linarith, by nlinarith [sq_nonneg (Real.log (2 * m : ℝ))]⟩
  have hbeta := betaBudget_le (show 1 ≤ 2 * m by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hbeta
  have hnum : 148 * ((logOrder (2 * m) : ℝ) * (1 + Real.log (2 * m : ℝ))) ≤ 2 * m := by
    rw [← mul_div_assoc] at hsmall
    exact (by simpa only [one_mul] using ((div_lt_iff₀ hn).mp hsmall).le)
  calc
    _ ≤ 148 * (logOrder (2 * m) : ℝ) * Real.sqrt (1 + Real.log (2 * m : ℝ)) := hbeta
    _ ≤ 148 * (logOrder (2 * m) : ℝ) * (1 + Real.log (2 * m : ℝ)) := by gcongr
    _ ≤ _ := by simpa only [mul_assoc] using hnum

theorem eventual_first_solution_coarse :
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      (∑ j, (η j : ℂ) = 0) → ∀ q : Fin (2 * m) → ℝ,
      normalLinearization (by omega) s θ v q = source (by omega) s θ η v h →
      meanSquare q ≤ 80000 *
        (pairEnergy (by omega) (fun j => (η j : ℂ)) + pairEnergy (by omega) h) / (2 * m : ℝ) ∧
      ‖q‖ ^ 2 ≤ 200000 *
        (pairEnergy (by omega) (fun j => (η j : ℂ)) + pairEnergy (by omega) h) := by
  filter_upwards [eventual_betaBudget_le_order, eventual_first_solution_meanSquare,
    eventual_first_solution_sup_sq] with m hbeta hms hsup
  intro hm s θ η v h hdom hmean q heq
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hA := pairEnergy_nonneg (show 0 < 2 * m by omega) h
  have hE := pairEnergy_nonneg (show 0 < 2 * m by omega) (fun j => (η j : ℂ))
  have hb2 := pow_le_pow_left₀ (betaBudget_nonneg (2 * m)) hbeta 2
  have hmul := mul_le_mul_of_nonneg_right hb2 hA
  have h₁ : betaBudget (2 * m) ^ 2 * pairEnergy (by omega) h / (2 * m : ℝ) ^ 3 ≤
      pairEnergy (by omega) h / (2 * m : ℝ) := by
    exact (div_le_div_of_nonneg_right hmul (by positivity)).trans_eq (by field_simp)
  have h₂ : betaBudget (2 * m) ^ 2 * pairEnergy (by omega) h / (2 * m : ℝ) ^ 2 ≤
      pairEnergy (by omega) h := by
    exact (div_le_div_of_nonneg_right hmul (sq_nonneg _)).trans_eq (by field_simp)
  have hfirst := hms hm s θ η v h hdom hmean q heq
  have hsecond := hsup hm s θ η v h hdom hmean q heq
  have hAdiv := div_nonneg hA hn.le
  constructor
  · ring_nf at hfirst h₁ hAdiv ⊢
    linarith only [hfirst, h₁, hAdiv]
  · ring_nf at hsecond h₂ ⊢
    linarith only [hsecond, h₂, hA]

end
end StructuralNote.FixedSchurDerivativeScales
