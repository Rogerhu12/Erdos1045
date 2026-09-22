import Erdos1045.DirectFourierParseval
import Mathlib.Analysis.PSeries

/-! Sampling analytic series by finite trigonometric polynomials and passage
to the limit. General Sobolev realization is unnecessary. -/

namespace Erdos1045.DirectFourier

open MeasureTheory FaberFourier Filter
open scoped BigOperators Topology
noncomputable section

def truncated (s : Finset ℕ) (d : ℕ → ℂ) (m : ℕ) : ℂ := if m ∈ s then d m else 0

theorem truncated_summable (s : Finset ℕ) (d : ℕ → ℂ) :
    Summable (fun m => ‖truncated s d m‖) := by
  apply summable_of_ne_finset_zero (s := s)
  intro m hm
  simp [truncated, hm]

def trigPolynomial (s : Finset ℕ) (d : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ m ∈ s, d m * character m t

theorem series_truncated (s : Finset ℕ) (d : ℕ → ℂ) (t : ℝ) :
    series (truncated s d) t = trigPolynomial s d t := by
  unfold series trigPolynomial
  rw [tsum_eq_sum (s := s) (fun m hm => by simp [truncated, hm])]
  apply Finset.sum_congr rfl
  intro m hm
  simp [truncated, hm]

theorem polynomial_continuous (s : Finset ℕ) (d : ℕ → ℂ) :
    Continuous (trigPolynomial s d) := by
  simpa only [funext (series_truncated s d)] using series_continuous (truncated_summable s d)

theorem polynomial_periodic (s : Finset ℕ) (d : ℕ → ℂ) :
    Function.Periodic (trigPolynomial s d) (2 * Real.pi) := by
  intro t
  simp_rw [← series_truncated s d, ← sumMap_coe (truncated_summable s d)]
  rw [AddCircle.coe_add_period]

def derivativeCoefficients (d : ℕ → ℂ) (m : ℕ) : ℂ := -(m : ℂ) * Complex.I * d m

theorem character_hasDerivAt (m : ℕ) (t : ℝ) :
    HasDerivAt (character m) (-(m : ℂ) * Complex.I * character m t) t := by
  have h := hasDerivAt_fourier (2 * Real.pi) (-(m : ℤ)) t
  have heq (x : ℝ) : fourier (-(m : ℤ)) (x : Circle) = character m x := monomial_coe m x
  simp only [heq] at h
  convert! h using 1
  push_cast
  field_simp

theorem polynomial_hasDerivAt (s : Finset ℕ) (d : ℕ → ℂ) (t : ℝ) :
    HasDerivAt (trigPolynomial s d)
      (trigPolynomial s (derivativeCoefficients d) t) t := by
  have h := HasDerivAt.sum (u := s) (fun m _ => (character_hasDerivAt m t).const_mul (d m))
  convert! h using 1
  · ext x
    simp [trigPolynomial]
  · apply Finset.sum_congr rfl
    intro m _
    unfold derivativeCoefficients
    ring

def polynomialH1 (s : Finset ℕ) (d : ℕ → ℂ) : CircleH1 where
  value := trigPolynomial s d
  weakDerivative := trigPolynomial s (derivativeCoefficients d)
  continuous_value := polynomial_continuous s d
  periodic_value := polynomial_periodic s d
  derivative_locally_integrable := (polynomial_continuous s (derivativeCoefficients d)).locallyIntegrable
  fundamental_identity := by
    intro a b
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => polynomial_hasDerivAt s d t)
      ((polynomial_continuous s (derivativeCoefficients d)).intervalIntegrable a b)).symm
  square_integrable_value := by
    simpa only [funext (series_truncated s d)] using
      series_square_integrable (truncated_summable s d)
  square_integrable_derivative := by
    simpa only [funext (series_truncated s (derivativeCoefficients d))] using
      series_square_integrable (truncated_summable s (derivativeCoefficients d))

theorem polynomial_energy (s : Finset ℕ) (d : ℕ → ℂ) :
    energy (trigPolynomial s d) = 2 * Real.pi * ∑ m ∈ s, ‖d m‖ ^ 2 := by
  have hp := (parseval (truncated s d) (truncated_summable s d)).2.2
  rw [funext (series_truncated s d)] at hp
  rw [hp, tsum_eq_sum (s := s) (fun m hm => by simp [truncated, hm])]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  simp [truncated, hm]

theorem derivativeCoefficients_norm (d : ℕ → ℂ) (m : ℕ) :
    ‖derivativeCoefficients d m‖ ^ 2 = (m : ℝ) ^ 2 * ‖d m‖ ^ 2 := by
  simp [derivativeCoefficients, mul_pow]

theorem weighted_square_absolute {d : ℕ → ℂ}
    (hd : Summable (fun m : ℕ => (1 + (m : ℝ) ^ 2) * ‖d m‖ ^ 2)) :
    Summable (fun m => ‖d m‖) := by
  let x : ℕ → ℂ := fun m => ((m + 1 : ℕ) : ℂ) * d (m + 1)
  let y : ℕ → ℂ := fun m => (((m + 1 : ℕ) : ℂ))⁻¹
  have hx : Summable (fun m => ‖x m‖ ^ 2) := by
    have hs := (coefficient_energies_summable hd).2.comp_injective
      (fun a b h => Nat.add_right_cancel h : Function.Injective (fun m : ℕ => m + 1))
    simpa only [x, norm_mul, Complex.norm_natCast, mul_pow, Function.comp_def] using! hs
  have hy : Summable (fun m => ‖y m‖ ^ 2) := by
    have hs : Summable (fun m : ℕ => ((m : ℝ) ^ 2)⁻¹) :=
      Real.summable_nat_pow_inv.mpr (by norm_num)
    have ht := hs.comp_injective
      (fun a b h => Nat.add_right_cancel h : Function.Injective (fun m : ℕ => m + 1))
    simpa only [y, norm_inv, Complex.norm_natCast, inv_pow, Function.comp_def] using! ht
  have hp : Summable (fun m => ‖x m * y m‖) := by
    apply Summable.of_nonneg_of_le (fun m => norm_nonneg _) _ ((hx.add hy).div_const 2)
    intro m
    rw [norm_mul]
    nlinarith [sq_nonneg (‖x m‖ - ‖y m‖)]
  have heq (m : ℕ) : x m * y m = d (m + 1) := by
    have hm : (((m + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    dsimp only [x, y]
    field_simp
  simp_rw [heq] at hp
  exact (summable_nat_add_iff 1).mp hp

/-- Apply circle sampling only to smooth finite polynomials, then pass to the
limit. This replaces the former general H1 realization hypothesis. -/
theorem series_sampling {n : ℕ} {C : ℝ} (θ : Fin n → ℝ)
    (hsampling : H1Sampling θ C) (d : ℕ → ℂ)
    (hd : Summable (fun m : ℕ => (1 + (m : ℝ) ^ 2) * ‖d m‖ ^ 2)) :
    (∑ j, ‖series d (θ j)‖ ^ 2) ≤ (2 * Real.pi * C) *
      ((n : ℝ) * (∑' m, ‖d m‖ ^ 2) +
        (∑' m : ℕ, (m : ℝ) ^ 2 * ‖d m‖ ^ 2) / n) := by
  have ha := weighted_square_absolute hd
  have he := coefficient_energies_summable hd
  have ht (t : ℝ) : Tendsto (fun N => trigPolynomial (Finset.range N) d t) atTop
      (nhds (series d t)) := by
    have hs : Summable (fun m => d m * character m t) := by
      apply Summable.of_norm
      simpa only [norm_mul, norm_character, mul_one] using ha
    exact hs.hasSum.tendsto_sum_nat
  have hl := tendsto_finsetSum Finset.univ (fun j _ => ((ht (θ j)).norm.pow 2))
  have hr := ((he.1.hasSum.tendsto_sum_nat.const_mul (n : ℝ)).add
    (he.2.hasSum.tendsto_sum_nat.div_const (n : ℝ))).const_mul (2 * Real.pi * C)
  apply le_of_tendsto_of_tendsto' hl hr
  intro N
  have h := hsampling (polynomialH1 (Finset.range N) d)
  simp only [polynomialH1, polynomial_energy, derivativeCoefficients_norm] at h
  convert h using 1 <;> first | rfl | ring

theorem coefficient_sampling {n : ℕ} {c C : ℝ} (hc : 0 < c)
    (a : ℕ → ℂ) (θ : Fin n → ℝ) (hsampling : H1Sampling θ C)
    (ha : Summable (fun m : ℕ => (1 + (m : ℝ) ^ 2) * ‖a m‖ ^ 2)) (k : ℕ) :
    (∑ j, ‖coefficient c a θ j k‖ ^ 2) ≤ (2 * Real.pi * C / c ^ 2) *
      ((n : ℝ) * (∑' m, ‖a (m + k)‖ ^ 2) +
        (∑' m : ℕ, (m : ℝ) ^ 2 * ‖a (m + k)‖ ^ 2) / n) := by
  have hs := series_sampling θ hsampling (tailCoefficients a k) (tail_summable ha k)
  have hb : (∑ j, ‖coefficient c a θ j k‖ ^ 2) =
      (∑ j, ‖series (tailCoefficients a k) (θ j)‖ ^ 2) / c ^ 2 := by
    simp_rw [norm_coefficient_sq hc, Finset.sum_div]
  rw [hb]
  have hd := div_le_div_of_nonneg_right hs (sq_nonneg c)
  dsimp [tailCoefficients] at hd
  convert hd using 1 <;> first | rfl | ring

end
end Erdos1045.DirectFourier
