import StructuralNote.FixedSchurChartSizes
import StructuralNote.FixedSchurRadialLimits

/-! Sharp radial step control on the literal domain, uniformly in the word. -/

namespace StructuralNote.FixedSchurChartRadial

open Complex Filter Erdos1045.EventualExact
open FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open CommonClosureEnergy CommonDomainClosure CommonDomainRadius
open CommonFiberNonlocalFrames CommonFiberNonlocalProjection
open EdgeCoordinates FixedSchurData FixedSchurLinear FixedSchurDomainSmallness FixedSchurChart
open FixedSchurRadialAlgebra FixedSchurRadialLimits
open scoped Topology

noncomputable section

theorem domain_angleAverage_bound_all {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) (hdom : InDomain hm θ v)
    (j : Fin (2 * m)) :
    |angleAverage (by omega) θ j| ≤
      4 * (logOrder (2 * m) : ℝ) * Real.sqrt (Real.log (2 * m : ℝ)) /
        (2 * m : ℝ) ^ 2 := by
  have hj := CommonFiberSmallCoefficients.domain_theta_bound hm θ v hdom j
  have hk := CommonFiberSmallCoefficients.domain_theta_bound hm θ v hdom
    (successor (by omega) j)
  unfold angleAverage
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have ht := abs_add_le (θ j) (θ (successor (by omega) j))
  linarith

theorem domain_radial_bound {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (σ q : Fin (2 * m) → ℝ) (hdom : InDomain (by omega) θ v)
    (hσ : ∀ j, σ j = 1 ∨ σ j = -1)
    (hq : ‖q - baseWord σ‖ ≤ radius (2 * m)) (hnorm : ‖q‖ ≤ 5)
    (j : Fin (2 * m)) :
    |radial (meanFrame (by omega) θ j) (difference (by omega) (center q v) j)| ≤
      (Real.pi ^ 2 + error (2 * m)) / (2 * m : ℝ) ^ 2 := by
  rw [center_difference hm q v hdom.2.2.1.2.2]
  have hh := radial_edgeIncrement_bound (show 2 ≤ 2 * m by omega) θ q
    (J q + EdgeCoordinates.tangent (by omega) v) j
    (pointwise_close_bound (by omega) q σ hσ hq j)
    (FixedSchurChartSizes.tangent_total_bound (by omega) θ v hdom q hnorm j)
    (domain_angleAverage_bound_all (by omega) θ v hdom j)
  have hb := numeric_bound (show 2 ≤ 2 * m by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hh hb
  exact hh.trans hb

theorem eventual_coordinate_radial : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → ∀ j,
      |radial (meanFrame (by omega) θ j)
        (difference (by omega) (center (coordinate (by omega) s θ v) v) j)| ≤
          10 / (2 * m : ℝ) ^ 2 := by
  filter_upwards [eventual_coordinate_properties, eventual_radial_coefficient]
    with m hprop hcoef
  intro hm s θ v hdom j
  have hp := hprop hm s θ v hdom
  exact (domain_radial_bound hm θ v _ _ hdom (FiniteBox.patternSign_is_sign s)
    hp.close hp.norm_le j).trans
      (div_le_div_of_nonneg_right hcoef (sq_nonneg _))

end
end StructuralNote.FixedSchurChartRadial
