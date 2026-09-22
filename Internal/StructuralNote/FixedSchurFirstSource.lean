import StructuralNote.FixedSchurDirectionMoments

/-! The three actual coefficients of the first normal-coordinate variation.
Keeping the tangential coefficient at its logarithmic n^-2 scale preserves
the sharper dependence on the free-center direction. -/

namespace StructuralNote.FixedSchurFirstSource

open Filter Complex Erdos1045.EventualExact FiniteBox SchurSpectrum SchurLiftBounds
open CommonDomainClosure CommonDomainRadius CommonClosureEnergy CommonFiberBounds
open FixedSchurData FixedSchurChart FixedSchurChartRadial FixedSchurDomainBounds
open FixedSchurNormalExpansion FixedSchurRotatedPath FixedSchurRotatedCoefficients
open CommonFiberNormalProjectionScaled HessianErrorLimits
open scoped BigOperators Topology

noncomputable section

def betaBudget (n : ℕ) : ℝ :=
  (4 * Real.sqrt (Real.log (n : ℝ)) + 144) * (logOrder n : ℝ)

def angularCoefficient {m : ℕ} (hm : 0 < m) (s : SignPattern hm)
    (θ : Fin (2 * m) → ℝ) (j : Fin (2 * m)) : ℝ :=
  patternSign s j / epsilon (2 * m) *
    Real.sin (Real.pi / (2 * m : ℝ) + angleDifference (by omega) θ j / 2)

def rotationCoefficient {m : ℕ} (hm : 0 < m) (s : SignPattern hm)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) (j : Fin (2 * m)) : ℝ :=
  L (Real.pi / (2 * m : ℝ) + angleDifference (by omega) θ j / 2) /
    H (epsilon (2 * m)) (rotatedS (by omega) θ v (coordinate hm s θ v) j) *
      rotatedS (by omega) θ v (coordinate hm s θ v) j

def source {m : ℕ} (hm : 0 < m) (s : SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ) (j : Fin (2 * m)) : ℝ :=
  angularCoefficient hm s θ j * angleDifference (by omega) η j -
    coefficientB hm s θ v j * EdgeCoordinates.tangent (by omega) h j -
      rotationCoefficient hm s θ v j * angleAverage (by omega) η j

theorem betaBudget_nonneg (n : ℕ) : 0 ≤ betaBudget n := by unfold betaBudget; positivity

theorem betaBudget_le {n : ℕ} (hn : 1 ≤ n) :
    betaBudget n ≤ 148 * (logOrder n : ℝ) * Real.sqrt (1 + Real.log (n : ℝ)) := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hroot : Real.sqrt (Real.log (n : ℝ)) ≤ Real.sqrt (1 + Real.log (n : ℝ)) :=
    Real.sqrt_le_sqrt (by linarith)
  have hone : 1 ≤ Real.sqrt (1 + Real.log (n : ℝ)) :=
    (Real.le_sqrt (by norm_num) (by linarith)).2 (by nlinarith)
  have h := mul_le_mul_of_nonneg_right (show 4 * Real.sqrt (Real.log (n : ℝ)) + 144 ≤
      148 * Real.sqrt (1 + Real.log (n : ℝ)) by linarith) (Nat.cast_nonneg (logOrder n))
  unfold betaBudget
  nlinarith only [h]

theorem beta_abs_le {ε σ b y : ℝ} (hσ : σ = 1 ∨ σ = -1) (hH : 1 ≤ H ε y) :
    |beta ε σ b y| ≤ |b| + |ε * y| := by
  have hsign : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hHpos : 0 < H ε y := by linarith
  have hw : |σ * ε * (y / H ε y)| ≤ |ε * y| := by
    rw [show σ * ε * (y / H ε y) = σ * (ε * y) / H ε y by ring,
      abs_div, abs_mul, hsign, one_mul, abs_of_pos hHpos]
    exact div_le_self (abs_nonneg _) hH
  unfold beta
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  exact add_le_add Real.abs_sin_le_abs
    ((mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)).trans_eq (mul_one _) |>.trans hw)

theorem eventual_source_coefficients :
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      ∀ j, |angularCoefficient (by omega) s θ j| ≤ 2 * (2 * m : ℝ) ∧
      |coefficientB (by omega) s θ v j| ≤ betaBudget (2 * m) / (2 * m : ℝ) ^ 2 ∧
      |rotationCoefficient (by omega) s θ v j| ≤ 36 * (logOrder (2 * m) : ℝ) := by
  have hnat : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 2 * m) tendsto_id
  have hlim : Tendsto (fun m : ℕ => 5 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat, mul_div_assoc, mul_zero] using
      (logOrder_div_tendsto.const_mul 5).comp hnat
  filter_upwards [eventual_actual_coefficients_small, eventual_coordinate_properties,
    hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with m hcoeff hprops hsmall
  intro hm s θ v hdom j
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hL : 5 * (logOrder (2 * m) : ℝ) ≤ 2 * m :=
    (by simpa only [one_mul] using ((div_lt_iff₀ hn).mp hsmall).le)
  have hH := (hcoeff hm s θ v hdom j).2.2
  have hq := (hprops hm s θ v hdom).norm_le
  have hS := rotatedS_abs_le_log (by omega) θ v hdom _ hq j
  have hangle : |Real.pi / (2 * m : ℝ) + angleDifference (by omega) θ j / 2| ≤
      5 / (2 * m : ℝ) := by
    have hd := domain_angle_difference (by omega) θ v hdom j
    have hp : Real.pi / (2 * m : ℝ) ≤ 4 / (2 * m : ℝ) :=
      div_le_div_of_nonneg_right Real.pi_lt_four.le hn.le
    have hLi : 5 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2 ≤ 1 / (2 * m : ℝ) := by
      calc
        _ ≤ (2 * m : ℝ) / (2 * m : ℝ) ^ 2 := div_le_div_of_nonneg_right hL (sq_nonneg _)
        _ = _ := by field_simp
    have ha := abs_add_le (Real.pi / (2 * m : ℝ)) (angleDifference (by omega) θ j / 2)
    rw [abs_of_pos (by positivity : 0 < Real.pi / (2 * m : ℝ)),
      abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ha
    have hd' : |angleDifference (by omega) θ j| / 2 ≤ 1 / (2 * m : ℝ) := by
      calc
        _ ≤ (10 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2) / 2 :=
          div_le_div_of_nonneg_right hd (by norm_num)
        _ = 5 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2 := by ring
        _ ≤ _ := hLi
    exact (ha.trans (add_le_add hp hd')).trans_eq (by ring)
  have hε := epsilon_pos (show 2 ≤ 2 * m by omega)
  have hκ := (scale_bounds (show 2 ≤ 2 * m by omega)).2
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hκ
  have hsign : |patternSign s j| = 1 := by
    rcases patternSign_is_sign s j with h | h <;> rw [h] <;> norm_num
  refine ⟨?_, ?_, ?_⟩
  · unfold angularCoefficient
    rw [abs_mul, abs_div, hsign, abs_of_pos hε, one_div, epsilon_inv (show 2 ≤ 2 * m by omega)]
    calc
      _ ≤ ((2 * m : ℝ) ^ 2 / 4) * (5 / (2 * m : ℝ)) :=
        mul_le_mul hκ (Real.abs_sin_le_abs.trans hangle) (abs_nonneg _) (by positivity)
      _ ≤ 2 * (2 * m : ℝ) := by field_simp; nlinarith
  · have hb := beta_abs_le (b := angleAverage (by omega) θ j) (patternSign_is_sign s j) hH
    have hθ := domain_angleAverage_bound_all (by omega) θ v hdom j
    have hep := epsilon_le (show 2 ≤ 2 * m by omega)
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hep
    have hy : |epsilon (2 * m) * rotatedS (by omega) θ v (coordinate (by omega) s θ v) j| ≤
        144 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2 := by
      rw [abs_mul, abs_of_pos hε]
      exact (mul_le_mul hep hS (abs_nonneg _) (by positivity)).trans_eq (by ring)
    exact (hb.trans (add_le_add hθ hy)).trans_eq (by
      unfold betaBudget
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      ring)
  · have hHpos : 0 < H (epsilon (2 * m))
        (rotatedS (by omega) θ v (coordinate (by omega) s θ v) j) := by linarith
    have hlen : |L (Real.pi / (2 * m : ℝ) + angleDifference (by omega) θ j / 2)| ≤ 2 := by
      unfold L
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      nlinarith only [Real.abs_cos_le_one (Real.pi / (2 * m : ℝ) + angleDifference (by omega) θ j / 2)]
    unfold rotationCoefficient
    rw [abs_mul, abs_div, abs_of_pos hHpos]
    have hr : |L (Real.pi / (2 * m : ℝ) + angleDifference (by omega) θ j / 2)| /
        H (epsilon (2 * m)) (rotatedS (by omega) θ v (coordinate (by omega) s θ v) j) ≤ 2 :=
      (div_le_iff₀ hHpos).2 (by linarith only [hlen, hH])
    exact (mul_le_mul hr hS (abs_nonneg _) (by norm_num)).trans_eq (by ring)

end
end StructuralNote.FixedSchurFirstSource
