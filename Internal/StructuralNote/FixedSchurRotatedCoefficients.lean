import StructuralNote.FixedSchurRotatedInverse
import StructuralNote.FixedSchurRotatedPath
import StructuralNote.FixedSchurRotatedStability

/-! Smallness of the literal coefficients of the linearized rotated constraint,
uniform on the complete fixed-Schur domain and in the chosen sign word. -/

namespace StructuralNote.FixedSchurRotatedCoefficients

open Filter Erdos1045.EventualExact FiniteBox SchurLiftBounds
open CommonDomainClosure CommonDomainRadius CommonClosureEnergy
open CommonTangentialParameters
open FixedSchurData FixedSchurChart FixedSchurChartSizes FixedSchurDomainBounds
open FixedSchurNormalExpansion FixedSchurRotatedPath FixedSchurRotatedStability
open FixedSchurRotatedInverse HessianErrorLimits
open scoped BigOperators Topology

noncomputable section

theorem scalar_coefficients_small {ε σ b y : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hb : |b| ≤ (1 / 40 : ℝ)) (hy : |ε * y| ≤ (1 / 40 : ℝ)) :
    |alpha ε σ b y - 1| ≤ (1 / 10 : ℝ) ∧
      |beta ε σ b y| ≤ (1 / 10 : ℝ) ∧ 1 ≤ H ε y := by
  have hysq : (ε * y) ^ 2 ≤ (1 / 40 : ℝ) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hy 2
  have hH : 1 ≤ H ε y := by
    unfold H
    exact (Real.le_sqrt (by norm_num) (by linarith : 0 ≤ 4 - (ε * y) ^ 2)).2 (by nlinarith)
  have hHpos : 0 < H ε y := by linarith
  have hsign : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hw : |σ * ε * (y / H ε y)| ≤ (1 / 40 : ℝ) := by
    calc
      |σ * ε * (y / H ε y)| = |ε * y| / H ε y := by
        rw [show σ * ε * (y / H ε y) = σ * (ε * y) / H ε y by ring,
          abs_div, abs_mul, hsign, one_mul, abs_of_pos hHpos]
      _ ≤ 1 / 40 := (div_le_iff₀ hHpos).2 (by nlinarith only [hy, hH])
  have hb2 : b ^ 2 ≤ (1 / 40 : ℝ) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hb 2
  have hc : |Real.cos b - 1| ≤ b ^ 2 / 2 := by
    rw [abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one b))]
    linarith only [Real.one_sub_sq_div_two_le_cos (x := b)]
  have hws : |σ * ε * (y / H ε y) * Real.sin b| ≤ (1 / 40 : ℝ) := by
    rw [abs_mul]
    exact (mul_le_mul hw (Real.abs_sin_le_one b) (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  have hwc : |σ * ε * (y / H ε y) * Real.cos b| ≤ (1 / 40 : ℝ) := by
    rw [abs_mul]
    exact (mul_le_mul hw (Real.abs_cos_le_one b) (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  refine ⟨?_, ?_, hH⟩
  · have heq : alpha ε σ b y - 1 = (Real.cos b - 1) - σ * ε * (y / H ε y) * Real.sin b := by
      unfold alpha
      ring
    rw [heq]
    have hh := abs_sub (Real.cos b - 1) (σ * ε * (y / H ε y) * Real.sin b)
    linarith only [hh, hc, hb2, hws]
  · unfold beta
    have hs := (Real.abs_sin_le_abs (x := b)).trans hb
    have hh := abs_add_le (Real.sin b) (σ * ε * (y / H ε y) * Real.cos b)
    linarith only [hh, hs, hwc]

theorem rotatedS_abs_le_log {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) (hdom : InDomain hm θ v)
    (q : Fin (2 * m) → ℝ) (hq : ‖q‖ ≤ 5) (j : Fin (2 * m)) :
    |rotatedS (by omega) θ v q j| ≤ 18 * (logOrder (2 * m) : ℝ) := by
  have hp := tangent_total_bound hm θ v hdom q hq j
  have hqj : |q j| ≤ 5 := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm q j).trans hq
  have hL := FixedSchurDomainSmallness.logOrder_one_le (show 2 ≤ 2 * m by omega)
  have htan : |rotatedS (by omega) θ v q j| ≤ |rotatedP (by omega) v q j| + |q j| := by
    unfold rotatedS FixedSchurRotatedAlgebra.tangential
    apply (abs_sub _ _).trans
    rw [abs_mul, abs_mul]
    exact add_le_add
      ((mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)).trans_eq (mul_one _))
      ((mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)).trans_eq (mul_one _))
  change |rotatedP (by omega) v q j| ≤ 13 * (logOrder (2 * m) : ℝ) at hp
  linarith only [htan, hp, hqj, hL]

theorem eventual_actual_coefficients_small :
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      ∀ j, |alpha (epsilon (2 * m)) (patternSign s j) (angleAverage (by omega) θ j)
        (rotatedS (by omega) θ v (coordinate (by omega) s θ v) j) - 1| ≤ (1 / 10 : ℝ) ∧
      |beta (epsilon (2 * m)) (patternSign s j) (angleAverage (by omega) θ j)
        (rotatedS (by omega) θ v (coordinate (by omega) s θ v) j)| ≤ (1 / 10 : ℝ) ∧
      1 ≤ H (epsilon (2 * m)) (rotatedS (by omega) θ v (coordinate (by omega) s θ v) j) := by
  have hnat : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 2 * m) tendsto_id
  have hlim : Tendsto (fun m : ℕ => 144 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat, mul_div_assoc, mul_zero] using
      (logOrder_div_tendsto.const_mul 144).comp hnat
  filter_upwards [eventual_coordinate_properties, eventual_angleAverage_inv,
    hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 40 by norm_num)),
    eventually_ge_atTop 20] with m hprops havg hsmall hm20
  intro hm s θ v hdom j
  have hn : (40 : ℝ) ≤ 2 * m := by exact_mod_cast (show 40 ≤ 2 * m by omega)
  have hnpos : (0 : ℝ) < 2 * m := by linarith
  have hb : |angleAverage (by omega) θ j| ≤ (1 / 40 : ℝ) := by
    apply (havg (by omega) θ v hdom j).trans
    exact (div_le_iff₀ hnpos).2 (by linarith)
  have hq := (hprops hm s θ v hdom).norm_le
  have hS := rotatedS_abs_le_log (by omega) θ v hdom _ hq j
  have heps := epsilon_le (show 2 ≤ 2 * m by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at heps
  have hy : |epsilon (2 * m) * rotatedS (by omega) θ v (coordinate (by omega) s θ v) j| ≤
      (1 / 40 : ℝ) := by
    rw [abs_mul, abs_of_pos (epsilon_pos (show 2 ≤ 2 * m by omega))]
    calc
      _ ≤ (8 / (2 * m : ℝ) ^ 2) * (18 * (logOrder (2 * m) : ℝ)) :=
        mul_le_mul heps hS (abs_nonneg _) (by positivity)
      _ = 144 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2 := by ring
      _ ≤ 144 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) := by
        apply div_le_div_of_nonneg_left (by positivity) hnpos
        nlinarith only [hn]
      _ ≤ 1 / 40 := hsmall.le
  exact scalar_coefficients_small (patternSign_is_sign s j) hb hy

def coefficientA {m : ℕ} (hm : 0 < m) (s : SignPattern hm)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) (j : Fin (2 * m)) : ℝ :=
  alpha (epsilon (2 * m)) (patternSign s j) (angleAverage (by omega) θ j)
    (rotatedS (by omega) θ v (coordinate hm s θ v) j)

def coefficientB {m : ℕ} (hm : 0 < m) (s : SignPattern hm)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) (j : Fin (2 * m)) : ℝ :=
  beta (epsilon (2 * m)) (patternSign s j) (angleAverage (by omega) θ j)
    (rotatedS (by omega) θ v (coordinate hm s θ v) j)

def normalLinearization {m : ℕ} (hm : 0 < m) (s : SignPattern hm)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) (q : Fin (2 * m) → ℝ) :
    Fin (2 * m) → ℝ := linearized (coefficientA hm s θ v) (coefficientB hm s θ v) q

theorem eventual_actual_solution_bounds :
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      ∀ q : Fin (2 * m) → ℝ,
      (∑ j, |q j|) / (2 * m : ℝ) ≤
        2 * ((∑ j, |normalLinearization (by omega) s θ v q j|) / (2 * m : ℝ)) ∧
      Real.sqrt (meanSquare q) ≤
        2 * Real.sqrt (meanSquare (normalLinearization (by omega) s θ v q)) ∧
      ‖q‖ ≤ 2 * ‖normalLinearization (by omega) s θ v q‖ := by
  filter_upwards [eventual_actual_coefficients_small] with m hsmall
  intro hm s θ v hdom q
  have ha (j : Fin (2 * m)) : |coefficientA (by omega) s θ v j - 1| ≤ (1 / 10 : ℝ) :=
    (hsmall hm s θ v hdom j).1
  have hb (j : Fin (2 * m)) : |coefficientB (by omega) s θ v j| ≤ (1 / 10 : ℝ) :=
    (hsmall hm s θ v hdom j).2.1
  refine ⟨?_, solution_l2_bound (by omega) _ _ q ha hb,
    solution_sup_bound (by omega) _ _ q ha hb⟩
  simpa only [normalLinearization, Nat.cast_mul, Nat.cast_ofNat] using
    solution_l1_bound (by omega) _ _ q ha hb

end
end StructuralNote.FixedSchurRotatedCoefficients
