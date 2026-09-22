import StructuralNote.FixedSchurNormalExpansion
import StructuralNote.FixedSchurHammingStability

/-! Actual rotated tangential fields for two words at the same parameters. -/

namespace StructuralNote.FixedSchurRotatedStability

open Filter Complex Erdos1045.EventualExact FiniteBox
open FixedSchurChart FixedSchurNormalExpansion FixedSchurRotatedAlgebra
open FixedSchurHammingStability SolWordHamming CommonDomainClosure
open CommonDomainRadius CommonTangentialParameters CommonFiberNonlocalSizes
open FixedSchurRadialLimits HessianErrorLimits
open CommonClosureEnergy CommonFiberSmallCoefficients FiniteFourierLift
open scoped BigOperators Topology

noncomputable section

theorem eventual_angleAverage_inv : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain hm θ v → ∀ j, |angleAverage (by omega) θ j| ≤ 1 / (2 * m : ℝ) := by
  have hnat : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 2 * m) tendsto_id
  have hlim : Tendsto (fun m : ℕ =>
      4 * (logOrder (2 * m) : ℝ) * (1 + Real.log (2 * m : ℝ)) / (2 * m : ℝ))
      atTop (𝓝 0) := by
    simpa only [Real.rpow_one, mul_zero, Nat.cast_mul, Nat.cast_ofNat,
      Function.comp_def, mul_div_assoc, mul_assoc] using
      ((logOrder_log_div_power_tendsto (p := 1) (by norm_num)).const_mul 4).comp hnat
  filter_upwards [hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with m hsmall
  intro hm θ v hdom j
  have hnpos : (0 : ℝ) < 2 * m := by positivity
  have hj := domain_theta_bound hm θ v hdom j
  have hk := domain_theta_bound hm θ v hdom (successor (by omega) j)
  have hb : |angleAverage (by omega) θ j| ≤
      4 * (logOrder (2 * m) : ℝ) * Real.sqrt (Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2 := by
    unfold angleAverage
    rw [abs_div]
    norm_num
    linarith [abs_add_le (θ j) (θ (successor (by omega) j))]
  have hsqrt := sqrt_log_le_one_add_log (show 1 ≤ 2 * m by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hsqrt
  have hs : 4 * (logOrder (2 * m) : ℝ) * (1 + Real.log (2 * m : ℝ)) ≤ 2 * m := by
    simpa only [one_mul] using ((div_lt_iff₀ hnpos).mp hsmall).le
  calc
    _ ≤ 4 * (logOrder (2 * m) : ℝ) * Real.sqrt (Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2 := hb
    _ ≤ 4 * (logOrder (2 * m) : ℝ) * (1 + Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2 := by gcongr
    _ ≤ (2 * m : ℝ) / (2 * m : ℝ) ^ 2 := div_le_div_of_nonneg_right hs (sq_nonneg _)
    _ = _ := by field_simp

theorem tangential_difference_le (b q q' p p' : ℝ) :
    |tangential b q p - tangential b q' p'| ≤
      |p - p'| + |q - q'| * |b| := by
  have hid : tangential b q p - tangential b q' p' =
      (p - p') * Real.cos b - (q - q') * Real.sin b := by
    unfold tangential
    ring
  rw [hid]
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_mul]
  have hp := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one b) (abs_nonneg (p - p'))
  have hq := mul_le_mul_of_nonneg_left (Real.abs_sin_le_abs (x := b)) (abs_nonneg (q - q'))
  simpa only [mul_one] using add_le_add hp hq

theorem eventual_rotated_stability : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s t : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → ∀ j,
      |rotatedP (by omega) v (coordinate (by omega) s θ v) j -
        rotatedP (by omega) v (coordinate (by omega) t θ v) j| ≤
        80 * (hamming s t : ℝ) / (2 * m : ℝ) ∧
      |rotatedS (by omega) θ v (coordinate (by omega) s θ v) j -
        rotatedS (by omega) θ v (coordinate (by omega) t θ v) j| ≤
        (80 * (hamming s t : ℝ) + 10) / (2 * m : ℝ) := by
  filter_upwards [eventual_hamming_stability, eventual_angleAverage_inv,
    eventual_coordinate_properties] with m hstab hb hprop
  intro hm s t θ v hdom j
  have hp := (hstab hm s t θ v hdom).2.1 j
  have hp' : |rotatedP (by omega) v (coordinate (by omega) s θ v) j -
      rotatedP (by omega) v (coordinate (by omega) t θ v) j| ≤
      80 * (hamming s t : ℝ) / (2 * m : ℝ) := by
    simpa only [rotatedP, Pi.add_apply, add_sub_add_right_eq_sub] using hp
  refine ⟨hp', ?_⟩
  have hq (w : SignPattern (show 0 < m by omega)) : |coordinate (by omega) w θ v j| ≤ 5 := by
    simpa only [Real.norm_eq_abs] using
      (norm_le_pi_norm (coordinate (by omega) w θ v) j).trans (hprop hm w θ v hdom).norm_le
  have hqdiff : |coordinate (by omega) s θ v j - coordinate (by omega) t θ v j| ≤ 10 :=
    (abs_sub _ _).trans (by linarith [hq s, hq t])
  have hbound := tangential_difference_le (angleAverage (by omega) θ j)
    (coordinate (by omega) s θ v j) (coordinate (by omega) t θ v j)
    (rotatedP (by omega) v (coordinate (by omega) s θ v) j)
    (rotatedP (by omega) v (coordinate (by omega) t θ v) j)
  apply hbound.trans
  calc
    _ ≤ 80 * (hamming s t : ℝ) / (2 * m : ℝ) + 10 * (1 / (2 * m : ℝ)) :=
      add_le_add hp' (mul_le_mul hqdiff (hb (by omega) θ v hdom j) (abs_nonneg _) (by norm_num))
    _ = _ := by ring

end
end StructuralNote.FixedSchurRotatedStability
