import StructuralNote.CommonFiberSmallCoefficients
import StructuralNote.CommonFiberSmooth

/-! The uniform first differential estimate (9.9), with one explicit universal
constant. All coefficient bounds are obtained from the actual common domain. -/

namespace StructuralNote.CommonFiberDifferentialEstimate

open Erdos1045.EventualExact Complex LensClosure CommonClosureEnergy
open CommonTangentialParameters CommonDomainClosure CommonDomainRadius CommonFiberBounds
open CommonFiberFirstDerivative CommonFiberDerivativeEnergy CommonFiberSmallCoefficients
open SchurSpectrum Filter
open scoped BigOperators Topology
noncomputable section

theorem angular_price_bound {n L B S : ℝ} (hn : 0 < n) (hL : 1 ≤ L) (hLn : L ^ 2 ≤ n)
    (hB0 : 0 ≤ B) (hS0 : 0 ≤ S) (hB : B ≤ (10 * L + 1049) / n ^ 2) (hS : S ≤ 5 / n) :
    195 / 2 * n ^ 2 * B ^ 2 + 195 * Real.pi ^ 2 * n * S ^ 2 ≤ 4000000000 / n := by
  have hb : B * n ^ 2 ≤ 1059 * L := by
    have := (le_div_iff₀ (sq_pos_of_pos hn)).mp hB
    linarith
  have hb2 := pow_le_pow_left₀ (mul_nonneg hB0 (sq_nonneg n)) hb 2
  have hb3 : n ^ 3 * B ^ 2 ≤ 1059 ^ 2 := by
    apply (mul_le_mul_iff_left₀ hn).mp
    have hl := mul_le_mul_of_nonneg_left hLn (show (0 : ℝ) ≤ 1059 ^ 2 by norm_num)
    nlinarith only [hb2, hl]
  have hs := pow_le_pow_left₀ (mul_nonneg hS0 hn.le) ((le_div_iff₀ hn).mp hS) 2
  have hp : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
  have hpS : Real.pi ^ 2 * (n ^ 2 * S ^ 2) ≤ 400 := by
    calc
      _ ≤ 16 * (n ^ 2 * S ^ 2) := mul_le_mul_of_nonneg_right hp (by positivity)
      _ ≤ _ := by nlinarith only [hs]
  apply (le_div_iff₀ hn).mpr
  nlinarith only [hb3, hpS]

theorem tangential_price_bound {n L g T : ℝ} (hn : 0 < n) (hL : 1 ≤ L) (hg : 1 ≤ g)
    (hT0 : 0 ≤ T) (hT : T ≤ (4 * L * Real.sqrt g + 10 * L + 1024) / n ^ 2) :
    195 * Real.pi ^ 2 * n * T ^ 2 ≤ 4000000000 * L ^ 2 * g / n ^ 3 := by
  have hg0 : 0 ≤ g := by linarith
  have hs : 1 ≤ Real.sqrt g := Real.one_le_sqrt.mpr hg
  have hLs : L ≤ L * Real.sqrt g := by nlinarith
  have hLs1 : 1 ≤ L * Real.sqrt g := hL.trans hLs
  have hb : T * n ^ 2 ≤ 1038 * L * Real.sqrt g := by
    have := (le_div_iff₀ (sq_pos_of_pos hn)).mp hT
    nlinarith
  have ht := pow_le_pow_left₀ (mul_nonneg hT0 (sq_nonneg n)) hb 2
  simp only [mul_pow, Real.sq_sqrt hg0] at ht
  have hp : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
  have hh : 195 * Real.pi ^ 2 * (T ^ 2 * n ^ 4) ≤ 4000000000 * L ^ 2 * g := by
    calc
      _ ≤ 195 * 16 * (T ^ 2 * n ^ 4) := by gcongr
      _ ≤ 195 * 16 * (1038 ^ 2 * L ^ 2 * g) :=
        mul_le_mul_of_nonneg_left (by nlinarith only [ht]) (by norm_num)
      _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg L) hg0]
  apply (le_div_iff₀ (pow_pos hn 3)).mpr
  nlinarith only [hh]

theorem domain_jacobian_small {m : ℕ} (hm : 128 ≤ m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (hdom : InDomain (by omega) θ v) {ξ : ℂ}
    (hξ : ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2)
    (hscale : energyRadius (2 * m) ≤ 1 / (2 * m : ℝ)) (j : Fin m) :
    |phase (by omega) θ j - LensClosure.midpoint m j| +
      |heightParameter (coordinates (by omega) v) ξ j| ≤ 1 / 4 := by
  obtain ⟨hθ, hv⟩ := domain_energy_bounds (by omega) θ v hdom
  have hs := CommonFiberSmooth.double_radius_small hm σ (θ, v) hdom.2.1
    (hθ.trans hscale) (hv.trans hscale) j
  have ht : |heightParameter (coordinates (by omega) v) ξ j| ≤
      |coordinates (by omega) v j| + ‖ξ‖ :=
    (abs_add_le _ _).trans (add_le_add le_rfl (harmonicFunctional_le_norm _ ξ))
  simp only [CommonFiberSmooth.data] at hs
  have hR : (0 : ℝ) ≤ 1024 / (2 * m : ℝ) ^ 2 := by positivity
  linarith

theorem first_derivative_energy_bound {m : ℕ} (hm : 128 ≤ m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ) (η : Fin (2 * m) → ℝ)
    (h : Fin (2 * m) → ℂ) (ξ' : ℂ)
    (hdom : InDomain (by omega) θ v) (hξ : ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2)
    (hmean : ∑ j, (η j : ℂ) = 0) (hh : ParameterSpace (by omega) h)
    (hz : (∑ j, velocity (by omega) θ v σ ξ η h ξ' j) = 0) (hσ : ∀ j, |σ j| ≤ 1)
    (hscale : energyRadius (2 * m) ≤ 1 / (2 * m : ℝ))
    (horder : 10 * (logOrder (2 * m) : ℝ) + 1024 ≤ 2 * m)
    (hlog : 1 ≤ Real.log (2 * m : ℝ)) :
    pairEnergy (by omega) (centerVelocity (by omega) θ v σ ξ η h ξ' - h) ≤
      4000000000 / (2 * m : ℝ) * pairEnergy (by omega) (fun j => (η j : ℂ)) +
      4000000000 * (logOrder (2 * m) : ℝ) ^ 2 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 3 *
        pairEnergy (by omega) h := by
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hLnat : 0 < logOrder (2 * m) := by
    apply Nat.ceil_pos.mpr
    apply div_pos
    · simpa only [Nat.cast_mul, Nat.cast_ofNat] using (show 0 < Real.log (2 * m : ℝ) by linarith)
    · exact Real.log_pos (by norm_num)
  have hL : (1 : ℝ) ≤ logOrder (2 * m) := by exact_mod_cast hLnat
  have hLn : (logOrder (2 * m) : ℝ) ^ 2 ≤ 2 * m := by
    have he : 1 / (2 * m : ℝ) = (2 * m) / (2 * m) ^ 2 := by field_simp
    simp only [energyRadius, Nat.cast_mul, Nat.cast_ofNat, he] at hscale
    exact (div_le_div_iff_of_pos_right (sq_pos_of_pos hn)).mp hscale
  have hb := domain_bodyNorm_bound (by omega) θ v σ hdom hξ hσ horder
  have hs := domain_sineNorm_bound (by omega) θ v hdom horder
  have ht := domain_tangentErrorNorm_bound (by omega) θ v hdom hξ
  have hA := angular_price_bound hn hL hLn (norm_nonneg _) (norm_nonneg _) hb hs
  have hT := tangential_price_bound hn hL hlog (norm_nonneg _) ht
  have hE := first_center_energy_actual_coefficients (by omega) θ v σ ξ η h ξ' hmean hh hz hσ
    (domain_jacobian_small hm θ v σ hdom hξ hscale)
  exact hE.trans (add_le_add
    (mul_le_mul_of_nonneg_right hA (pairEnergy_nonneg _ _))
    (mul_le_mul_of_nonneg_right hT (pairEnergy_nonneg _ _)))

theorem eventual_size_conditions : ∀ᶠ m : ℕ in atTop,
    128 ≤ m ∧ energyRadius (2 * m) ≤ 1 / (2 * m : ℝ) ∧
      10 * (logOrder (2 * m) : ℝ) + 1024 ≤ 2 * m ∧ 1 ≤ Real.log (2 * m : ℝ) := by
  have hnat : Tendsto (fun m : ℕ => 2 * m) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with m hm
    omega
  have hreal : Tendsto (fun m : ℕ => (2 * m : ℝ)) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat] using
      tendsto_natCast_atTop_atTop.comp hnat
  have hlog := (Real.tendsto_log_atTop.comp hreal).eventually_ge_atTop 1
  have hr := hnat.eventually eventual_radius_le_inverse
  have ho := hnat.eventually eventual_order_bound
  filter_upwards [eventually_ge_atTop 128, hr, ho, hlog] with m hm hr ho hl
  exact ⟨hm, by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hr,
    by simpa only [Nat.cast_mul, Nat.cast_ofNat] using ho, hl⟩

/-- The first estimate in Lemma 9.3 for actual closed parameter paths. The
derivative of the reconstructed center is included in the conclusion. -/
theorem eventual_actual_first_derivative : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (θ : ℝ → Fin (2 * m) → ℝ) (v : ℝ → Fin (2 * m) → ℂ)
      (ξ : ℝ → ℂ) (η : Fin (2 * m) → ℝ) (h : Fin (2 * m) → ℂ) (ξ' : ℂ) (x : ℝ) (σ : Fin m → ℝ),
    (∀ j, HasDerivAt (fun s => θ s j) (η j) x) →
    (∀ j, HasDerivAt (fun s => v s j) (h j) x) → HasDerivAt ξ ξ' x →
    InDomain hm (θ x) (v x) → ‖ξ x‖ ≤ 1024 / (2 * m : ℝ) ^ 2 →
    (∑ j, (η j : ℂ)) = 0 → ParameterSpace hm h → (∀ j, |σ j| ≤ 1) →
    (∀ᶠ s in 𝓝 x, closure (phase hm (θ s)) (fun j => 2 * Real.cos (halfAngle hm (θ s) j))
      σ (coordinates hm (v s)) (ξ s) = 0) →
    (∀ j, HasDerivAt (fun s => CommonFiberGeometry.center hm (θ s) (v s) σ (ξ s) j)
      (centerVelocity hm (θ x) (v x) σ (ξ x) η h ξ' j) x) ∧
    pairEnergy (by omega) (centerVelocity hm (θ x) (v x) σ (ξ x) η h ξ' - h) ≤
      4000000000 / (2 * m : ℝ) * pairEnergy (by omega) (fun j => (η j : ℂ)) +
      4000000000 * (logOrder (2 * m) : ℝ) ^ 2 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 3 *
        pairEnergy (by omega) h := by
  filter_upwards [eventual_size_conditions] with m hsize
  intro hm θ v ξ η h ξ' x σ hθ hv hξ hdom hroot hmean hh hσ hz
  have hs := domain_jacobian_small hsize.1 (θ x) (v x) σ hdom hroot hsize.2.1
  have ht (j : Fin m) : heightParameter (coordinates hm (v x)) (ξ x) j ^ 2 < 4 := by
    have h := hs j
    have hb : |heightParameter (coordinates hm (v x)) (ξ x) j| ≤ 1 / 4 := by
      linarith [abs_nonneg (phase hm (θ x) j - LensClosure.midpoint m j)]
    nlinarith [(abs_le.mp hb).1, (abs_le.mp hb).2]
  refine ⟨center_hasDerivAt hm σ hθ hv hξ ht, ?_⟩
  exact first_derivative_energy_bound hsize.1 (θ x) (v x) σ (ξ x) η h ξ' hdom hroot hmean hh
    (velocity_sum_eq_zero hm σ hθ hv hξ ht hz) hσ hsize.2.1 hsize.2.2.1 hsize.2.2.2

end
end StructuralNote.CommonFiberDifferentialEstimate
