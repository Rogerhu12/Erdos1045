import StructuralNote.FixedSchurChart
import StructuralNote.FixedSchurDomainBounds
import StructuralNote.FixedSchurHarmonicBounds
import StructuralNote.CommonFiberNonlocalSizes
import StructuralNote.CommonFiberInjectivity

/-! Quantitative step and collision bounds for the chosen fixed-Schur chart. -/

namespace StructuralNote.FixedSchurChartSizes

open scoped BigOperators Topology

open Complex Filter
open Erdos1045 Erdos1045.EventualExact
open FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open CommonDomainClosure CommonDomainRadius EdgeCoordinates FixedSchurData FixedSchurLinear
open CommonFiberGeometry
open FixedSchurEdgeGeometry
open FixedSchurChart FixedSchurDomainBounds FixedSchurDomainSmallness
open FixedSchurHarmonicBounds CommonFiberSmallCoefficients
open CommonFiberNonlocalSizes CommonFiberInjectivity

noncomputable section

theorem tangent_total_bound {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (hdom : InDomain hm θ v) (q : Fin (2 * m) → ℝ) (hq : ‖q‖ ≤ 5)
    (j : Fin (2 * m)) :
    |(J q + EdgeCoordinates.tangent (by omega) v) j| ≤
      13 * (logOrder (2 * m) : ℝ) := by
  have hL : 1 ≤ (logOrder (2 * m) : ℝ) :=
    logOrder_one_le (show 2 ≤ 2 * m by omega)
  have hJnorm := J_norm_le (show 0 < 2 * m by omega) q
  have hJpoint : |J q j| ≤ ‖J q‖ := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (J q) j)
  have hJ : |J q j| ≤ 10 := by
    calc
      |J q j| ≤ ‖J q‖ := hJpoint
      _ ≤ 2 * ‖q‖ := hJnorm
      _ ≤ 10 := by nlinarith
  have ht := domain_tangent_bound hm θ v hdom j
  change |J q j + EdgeCoordinates.tangent (by omega) v j| ≤ _
  exact (abs_add_le _ _).trans (by nlinarith)

theorem center_step_bound {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (hdom : InDomain (by omega) θ v) (q : Fin (2 * m) → ℝ)
    (hq : ‖q‖ ≤ 5)
    (j : Fin (2 * m)) :
    ‖difference (by omega) (center q v) j‖ ≤
      144 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2 := by
  rw [center_difference hm q v hdom.2.2.1.2.2]
  have hp := tangent_total_bound (by omega) θ v hdom q hq j
  have hqj : |q j| ≤ 5 := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm q j).trans hq
  have heps := epsilon_le (show 2 ≤ 2 * m by omega)
  have heps' : epsilon (2 * m) ≤ 8 / (2 * m : ℝ) ^ 2 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using heps
  unfold edgeIncrement
  rw [norm_mul, norm_mul]
  simp only [Pi.add_apply]
  change ‖(epsilon (2 * m) : ℂ)‖ * ‖frame (2 * m) j‖ *
      ‖(q j : ℂ) + I * ((J q + EdgeCoordinates.tangent (by omega) v) j : ℂ)‖ ≤ _
  have hcoef : ‖(epsilon (2 * m) : ℂ)‖ = epsilon (2 * m) := by
    rw [norm_real, Real.norm_eq_abs, abs_of_pos]
    exact epsilon_pos (show 2 ≤ 2 * m by omega)
  rw [hcoef, norm_frame]
  have hinner : ‖(q j : ℂ) + I * ((J q + EdgeCoordinates.tangent (by omega) v) j : ℂ)‖ ≤
      |q j| + |(J q + EdgeCoordinates.tangent (by omega) v) j| := by
    calc
      ‖(q j : ℂ) + I * ((J q + EdgeCoordinates.tangent (by omega) v) j : ℂ)‖ ≤
          ‖(q j : ℂ)‖ + ‖I * ((J q + EdgeCoordinates.tangent (by omega) v) j : ℂ)‖ :=
        norm_add_le _ _
      _ = |q j| + |(J q + EdgeCoordinates.tangent (by omega) v) j| := by
        simp only [norm_real, Real.norm_eq_abs, norm_mul, norm_I, one_mul]
  have hsum : |q j| + |(J q + EdgeCoordinates.tangent (by omega) v) j| ≤
      18 * (logOrder (2 * m) : ℝ) := by
    have hL : 1 ≤ (logOrder (2 * m) : ℝ) :=
      logOrder_one_le (show 2 ≤ 2 * m by omega)
    nlinarith [hp]
  calc
    _ ≤ epsilon (2 * m) * (|q j| + |(J q + EdgeCoordinates.tangent (by omega) v) j|) := by
      simpa only [mul_one, one_mul] using
        (mul_le_mul_of_nonneg_left hinner
          (epsilon_pos (show 2 ≤ 2 * m by omega)).le)
    _ ≤ epsilon (2 * m) * (18 * (logOrder (2 * m) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hsum
        (epsilon_pos (show 2 ≤ 2 * m by omega)).le
    _ ≤ (8 / (2 * m : ℝ) ^ 2) * (18 * (logOrder (2 * m) : ℝ)) := by
      exact mul_le_mul_of_nonneg_right heps' (by positivity)
    _ = 144 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2 := by ring

private theorem eventual_step_numeric :
    ∀ᶠ m : ℕ in atTop,
      144 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2 ≤
        1 / (1000 * (2 * m : ℝ)) := by
  have hnat : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 2 * m) tendsto_id
  have hlim : Tendsto
      (fun m : ℕ => (logOrder (2 * m) : ℝ) / (2 * m : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv]
      using (HessianErrorLimits.logOrder_div_tendsto.comp hnat)
  filter_upwards [hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 144000 by norm_num)),
    eventually_ge_atTop 1] with m hm hmpos
  have hm0 : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hratio : 144000 * ((logOrder (2 * m) : ℝ) / (2 * m : ℝ)) ≤ 1 := by
    nlinarith
  have hid :
      144 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2 =
        (1 / (1000 * (2 * m : ℝ))) *
          (144000 * ((logOrder (2 * m) : ℝ) / (2 * m : ℝ))) := by
    have hn : (2 : ℝ) * m ≠ 0 := by positivity
    field_simp
    ring
  rw [hid]
  have hfactor : 0 ≤ 1 / (1000 * (2 * m : ℝ)) := by positivity
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio hfactor

private theorem eventual_theta_numeric :
    ∀ᶠ m : ℕ in atTop,
      4 * (logOrder (2 * m) : ℝ) * Real.sqrt (Real.log (2 * m : ℝ)) /
          (2 * m : ℝ) ^ 2 ≤ 1 / (1000 * (2 * m : ℝ)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    CommonFiberNonlocalSizes.eventual_small_coefficients
  filter_upwards [eventually_ge_atTop ((N + 1) / 2)] with m hm
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using (hN (2 * m) (by omega)).2.2.1

theorem eventual_chart_small_steps : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      (∀ j, |θ j| ≤ 1 / (1000 * (2 * m : ℝ))) ∧
      (∀ j, ‖difference (by omega)
        (center (coordinate (by omega) s θ v) v) j‖ ≤
          1 / (1000 * (2 * m : ℝ))) := by
  filter_upwards [eventual_coordinate_properties, eventual_theta_numeric,
    eventual_step_numeric] with m hprops hθnum hnum
  intro hm s θ v hdom
  have hP := hprops hm s θ v hdom
  have hθ : ∀ j, |θ j| ≤ 1 / (1000 * (2 * m : ℝ)) := by
    intro j
    exact (domain_theta_bound (by omega) θ v hdom j).trans
      hθnum
  have hstep : ∀ j, ‖difference (by omega)
      (center (coordinate (by omega) s θ v) v) j‖ ≤
      1 / (1000 * (2 * m : ℝ)) := by
    intro j
    exact (center_step_bound hm θ v hdom (coordinate (by omega) s θ v)
      hP.norm_le j).trans (hnum)
  exact ⟨hθ, hstep⟩

theorem eventual_configuration_injective : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      Function.Injective (configuration (by omega) s θ v) := by
  filter_upwards [eventual_chart_small_steps] with m hsmall
  intro hm s θ v hdom
  obtain ⟨hθ, hstep⟩ := hsmall hm s θ v hdom
  have hinj := small_center_step_injective (by omega : 4 ≤ 2 * m) θ
    (center (coordinate (by omega) s θ v) v)
    (fun j => by
      have h := hθ j
      have hrat : 1 / (1000 * (2 * m : ℝ)) ≤
          1 / (8 * (2 * m : ℝ)) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        nlinarith
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using h.trans hrat)
    (fun j => by
      have h := hstep j
      have hrat : 1 / (1000 * (2 * m : ℝ)) ≤
          1 / (2 * (2 * m : ℝ)) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        nlinarith
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using h.trans hrat)
  change Function.Injective
    (fun j => diameterVector θ j + center (coordinate (by omega) s θ v) v j)
  exact hinj

end
end StructuralNote.FixedSchurChartSizes
