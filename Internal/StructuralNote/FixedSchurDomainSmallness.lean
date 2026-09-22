import StructuralNote.FixedSchurDomainBounds
import StructuralNote.HessianErrorLimits
import EventualExact.WholeBoxObjective

/-! A single eventual smallness package for the actual fixed-Schur domain. -/

namespace StructuralNote.FixedSchurDomainSmallness

open scoped BigOperators Topology

open Erdos1045 Erdos1045.EventualExact
open Complex FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open CommonClosureEnergy CommonDomainClosure CommonDomainRadius
open FixedSchurData FixedSchurDomainBounds
open Filter HessianErrorLimits

noncomputable section

def radius (n : ℕ) : ℝ := 4096 * (logOrder n : ℝ) / (n : ℝ)

def baseWord {n : ℕ} (σ : Fin n → ℝ) : Fin n → ℝ :=
  fun j => FiniteBox.amplitude n * σ j

theorem radius_nonneg {n : ℕ} (hn : 0 < n) : 0 ≤ radius n := by
  unfold radius
  positivity

theorem baseWord_norm_le_four {n : ℕ} (hn : 2 ≤ n) {σ : Fin n → ℝ}
    (hsign : ∀ j, σ j = 1 ∨ σ j = -1) :
    ‖baseWord σ‖ ≤ 4 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).2
  intro j
  have hσ : |σ j| = 1 := by
    rcases hsign j with h | h <;> simp [h]
  have hA0 : 0 ≤ FiniteBox.amplitude n :=
    (FiniteBox.amplitude_pos hn).le
  have hA := Erdos1045.EventualExact.WholeBoxObjective.amplitude_le_four hn
  calc
    ‖baseWord σ j‖ = |FiniteBox.amplitude n * σ j| := by
      simp [baseWord, Real.norm_eq_abs]
    _ = FiniteBox.amplitude n * |σ j| := by
      rw [abs_mul, abs_of_nonneg hA0]
    _ = FiniteBox.amplitude n := by rw [hσ, mul_one]
    _ ≤ 4 := hA

private theorem sqrt_log_le_one_add_log {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt (Real.log (n : ℝ)) ≤ 1 + Real.log (n : ℝ) := by
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  apply (Real.sqrt_le_iff).2
  constructor
  · linarith [Real.sqrt_nonneg (Real.log (n : ℝ))]
  · nlinarith [sq_nonneg (Real.log (n : ℝ))]

theorem logOrder_one_le {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ (logOrder n : ℝ) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hratio : (1 : ℝ) ≤ Real.log n / Real.log 2 := by
    apply (le_div_iff₀ hlog2).2
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hnR
    linarith
  exact hratio.trans (by exact_mod_cast (Nat.le_ceil (Real.log n / Real.log 2)))

private theorem domain_pointwise_upper {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (σ : Fin (2 * m) → ℝ) (hdom : InDomain hm θ v)
    (hsign : ∀ j, σ j = 1 ∨ σ j = -1)
    (hR : radius (2 * m) ≤ 1) (j : Fin (2 * m)) :
    |FixedSchurData.Y (by omega) θ j| +
        epsilon (2 * m) *
          (|EdgeCoordinates.tangent (by omega) v j| +
            2 * (‖baseWord σ‖ + radius (2 * m))) ≤
      128 * (logOrder (2 * m) : ℝ) *
        (1 + Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2 := by
  have hn : 2 ≤ 2 * m := by omega
  have hL : 1 ≤ (logOrder (2 * m) : ℝ) := logOrder_one_le hn
  have hlog : 0 ≤ Real.log (2 * m : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ 2 * m by omega)
  have hsqrt := sqrt_log_le_one_add_log (show 1 ≤ 2 * m by omega)
  have hsqrt' : Real.sqrt (Real.log (2 * m : ℝ)) ≤
      1 + Real.log (2 * m : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hsqrt
  have hY := domain_Y_bound hm θ v hdom j
  have hT := domain_tangent_bound hm θ v hdom j
  have hε := epsilon_le hn
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hε
  have hbase := baseWord_norm_le_four hn hsign
  have hR0 := radius_nonneg (show 0 < 2 * m by omega)
  have hinside :
      |EdgeCoordinates.tangent (by omega) v j| +
          2 * (‖baseWord σ‖ + radius (2 * m)) ≤
        (25 / 2 : ℝ) * (logOrder (2 * m) : ℝ) := by
    calc
      _ ≤ (5 / 2 : ℝ) * (logOrder (2 * m) : ℝ) +
          2 * (4 + 1) := by gcongr
      _ ≤ (25 / 2 : ℝ) * (logOrder (2 * m) : ℝ) := by nlinarith
  have hprod :
      epsilon (2 * m) *
          (|EdgeCoordinates.tangent (by omega) v j| +
            2 * (‖baseWord σ‖ + radius (2 * m))) ≤
        100 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2 := by
    calc
      _ ≤ (8 / (2 * m : ℝ) ^ 2) *
          ((25 / 2 : ℝ) * (logOrder (2 * m) : ℝ)) := by
        exact mul_le_mul hε hinside (by positivity) (by positivity)
      _ = 100 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2 := by ring
  calc
    _ ≤ 8 * (logOrder (2 * m) : ℝ) *
        Real.sqrt (Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2 +
        100 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2 :=
      add_le_add hY hprod
    _ ≤ 8 * (logOrder (2 * m) : ℝ) *
          (1 + Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2 +
          100 * (logOrder (2 * m) : ℝ) *
            (1 + Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2 := by
      apply add_le_add
      · have hcoef : 0 ≤ 8 * (logOrder (2 * m) : ℝ) /
              (2 * m : ℝ) ^ 2 := by positivity
        calc
          8 * (logOrder (2 * m) : ℝ) *
              Real.sqrt (Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2 =
              (8 * (logOrder (2 * m) : ℝ) /
                (2 * m : ℝ) ^ 2) * Real.sqrt (Real.log (2 * m : ℝ)) := by ring
          _ ≤ (8 * (logOrder (2 * m) : ℝ) /
                (2 * m : ℝ) ^ 2) * (1 + Real.log (2 * m : ℝ)) :=
            mul_le_mul_of_nonneg_left hsqrt' hcoef
          _ = 8 * (logOrder (2 * m) : ℝ) *
              (1 + Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2 := by ring
      · apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 1 + Real.log (2 * m : ℝ) by linarith)
            (show 0 ≤ 100 * (logOrder (2 * m) : ℝ) by positivity))
    _ = 108 * (logOrder (2 * m) : ℝ) *
        (1 + Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2 := by ring
    _ ≤ 128 * (logOrder (2 * m) : ℝ) *
        (1 + Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2 := by
      have hcoef : 0 ≤ (logOrder (2 * m) : ℝ) *
          (1 + Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2 := by positivity
      calc
        108 * (logOrder (2 * m) : ℝ) *
            (1 + Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2 =
            108 * ((logOrder (2 * m) : ℝ) *
              (1 + Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2) := by ring
        _ ≤ 128 * ((logOrder (2 * m) : ℝ) *
            (1 + Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right (by norm_num) hcoef
        _ = 128 * (logOrder (2 * m) : ℝ) *
            (1 + Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2 := by ring

theorem eventual_domain_log_scale :
    ∀ᶠ m : ℕ in atTop,
      (logOrder (2 * m) : ℝ) * (1 + Real.log (2 * m : ℝ)) /
          (2 * m : ℝ) ≤ 1 := by
  have hnat : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 2 * m) tendsto_id
  have hlim : Tendsto
      (fun m : ℕ => (logOrder (2 * m) : ℝ) *
        (1 + Real.log (2 * m : ℝ)) / (2 * m : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat, Real.rpow_one] using
      (logOrder_log_div_power_tendsto (p := 1) (by norm_num)).comp hnat
  filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with m hm
  exact hm.le

theorem eventual_domain_smallness :
    ∀ᶠ m : ℕ in atTop,
      ∀ (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
        (σ : Fin (2 * m) → ℝ),
        InDomain hm θ v → (∀ j, σ j = 1 ∨ σ j = -1) →
        0 ≤ radius (2 * m) ∧ radius (2 * m) ≤ 1 ∧
          ∀ j, |FixedSchurData.Y (by omega) θ j| +
            epsilon (2 * m) *
              (|EdgeCoordinates.tangent (by omega) v j| +
                2 * (‖baseWord σ‖ + radius (2 * m))) ≤ 1 / 4 := by
  have hnat : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 2 * m) tendsto_id
  have hRlim0 : Tendsto
      (fun m : ℕ => 4096 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ)) atTop (𝓝 0) := by
    convert (logOrder_div_tendsto.const_mul 4096).comp hnat using 1
    · funext m
      simp only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat]
      ring
    · norm_num
  have hsmall0 : Tendsto
      (fun m : ℕ => 128 * ((logOrder (2 * m) : ℝ) *
        (1 + Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat, Real.rpow_two,
      mul_zero] using
      ((logOrder_log_div_power_tendsto (p := 2) (by norm_num)).const_mul 128).comp hnat
  have hRlim := hRlim0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hsmall := hsmall0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [hRlim, hsmall, eventually_ge_atTop 1] with m hR hsmall hm
  intro hm' θ v σ hdom hsign
  have hn : 2 ≤ 2 * m := by omega
  have hR' : radius (2 * m) ≤ 1 := by
    simpa only [radius, Nat.cast_mul, Nat.cast_ofNat, mul_div_assoc] using hR.le
  have hsmall' :
      128 * (logOrder (2 * m) : ℝ) * (1 + Real.log (2 * m : ℝ)) /
          (2 * m : ℝ) ^ 2 ≤ 1 / 4 := by
    calc
      128 * (logOrder (2 * m) : ℝ) * (1 + Real.log (2 * m : ℝ)) /
          (2 * m : ℝ) ^ 2 =
        128 * ((logOrder (2 * m) : ℝ) *
          (1 + Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2) := by ring
      _ ≤ 1 / 4 := hsmall.le
  refine ⟨radius_nonneg (by omega), hR', ?_⟩
  intro j
  exact (domain_pointwise_upper hm' θ v σ hdom hsign hR' j).trans hsmall'

theorem eventual_domain_smallness_bundle :
    ∀ᶠ m : ℕ in atTop,
      (logOrder (2 * m) : ℝ) * (1 + Real.log (2 * m : ℝ)) /
          (2 * m : ℝ) ≤ 1 ∧
      (∀ (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
        (σ : Fin (2 * m) → ℝ),
        InDomain hm θ v → (∀ j, σ j = 1 ∨ σ j = -1) →
        0 ≤ radius (2 * m) ∧ radius (2 * m) ≤ 1 ∧
          ∀ j, |FixedSchurData.Y (by omega) θ j| +
            epsilon (2 * m) *
              (|EdgeCoordinates.tangent (by omega) v j| +
                2 * (‖baseWord σ‖ + radius (2 * m))) ≤ 1 / 4) := by
  filter_upwards [eventual_domain_log_scale, eventual_domain_smallness] with m hscale hsmall
  exact ⟨hscale, hsmall⟩

end

end StructuralNote.FixedSchurDomainSmallness
