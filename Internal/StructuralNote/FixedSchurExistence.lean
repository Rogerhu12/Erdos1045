import StructuralNote.FixedSchurDomainSource

/-! Uniform existence and uniqueness for the actual fixed-Schur equations.
The only parameter assumption is membership in the manuscript's common domain. -/

namespace StructuralNote.FixedSchurExistence

open Real Complex Filter Set Metric
open Erdos1045.EventualExact FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open CommonDomainClosure CommonDomainRadius EdgeCoordinates FixedSchurData
open FixedSchurDomainSmallness FixedSchurDomainSource FixedSchurSourceArithmetic
open FixedSchurEquations FixedSchurContraction
open scoped Topology

noncomputable section

theorem eventual_domain_root : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
      (σ : Fin (2 * m) → ℝ), InDomain hm θ v → (∀ j, σ j = 1 ∨ σ j = -1) →
      ∃! q : Fin (2 * m) → ℝ,
        ‖q - baseWord σ‖ ≤ radius (2 * m) ∧ equationMap hm θ v σ q = q := by
  filter_upwards [eventual_domain_smallness_bundle] with m hsize
  intro hm θ v σ hdom hσ
  have hs := hsize.2 hm θ v σ hdom hσ
  have hf : baseWord σ ∈ closedBall (baseWord σ) (radius (2 * m)) := by simp [hs.1]
  have hsmall : ∀ j, |Y (by omega) θ j + σ j * epsilon (2 * m) *
      (tangent (by omega) v j + J (baseWord σ) j)| ≤ 1 := by
    intro j
    exact (ball_input_bound (by omega) (epsilon_pos (show 2 ≤ 2 * m by omega))
      _ _ _ _ hσ hs.2.2 hf j).trans (by norm_num)
  have hsource := domain_source_bound hm θ v σ hdom hσ hsmall
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hlog : 0 ≤ Real.log (2 * m : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * m by omega))
  have hb := source_error_bound_under_unit_ratio
    (H := Real.sqrt (Real.log (2 * m : ℝ))) hn
    (logOrder_one_le (show 2 ≤ 2 * m by omega)) (Real.sqrt_nonneg _)
    (by simpa only [Real.sq_sqrt hlog] using hsize.1)
  have hsource' : ‖equationMap hm θ v σ (baseWord σ) - baseWord σ‖ ≤ radius (2 * m) / 2 := by
    apply hsource.trans
    calc
      _ ≤ 2048 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) := by
        simpa only [Real.sq_sqrt hlog] using hb
      _ = radius (2 * m) / 2 := by simp only [radius, Nat.cast_mul, Nat.cast_ofNat]; ring
  exact exists_unique_fixedPoint (by omega) (epsilon_pos (show 2 ≤ 2 * m by omega)) hs.1
    _ _ _ _ _ hσ hs.2.2 hsource'

theorem eventual_ball_positive_input : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
      (σ : Fin (2 * m) → ℝ), InDomain hm θ v → (∀ j, σ j = 1 ∨ σ j = -1) →
      ∀ q : Fin (2 * m) → ℝ, ‖q - baseWord σ‖ ≤ radius (2 * m) →
        ∀ j, |Y (by omega) θ j + σ j * epsilon (2 * m) *
          (tangent (by omega) v j + J q j)| < 2 := by
  filter_upwards [eventual_domain_smallness] with m hsize
  intro hm θ v σ hdom hσ q hq j
  have hs := hsize hm θ v σ hdom hσ
  have hqmem : q ∈ closedBall (baseWord σ) (radius (2 * m)) := by
    simpa only [mem_closedBall, dist_eq_norm] using hq
  exact (ball_input_bound (by omega) (epsilon_pos (show 2 ≤ 2 * m by omega))
    _ _ _ _ hσ hs.2.2 hqmem j).trans_lt (by norm_num)

theorem eventual_signPattern_root : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (s : FiniteBox.SignPattern hm) (θ : Fin (2 * m) → ℝ)
      (v : Fin (2 * m) → ℂ), InDomain hm θ v →
      ∃! q : Fin (2 * m) → ℝ,
        ‖q - baseWord (FiniteBox.patternSign s)‖ ≤ radius (2 * m) ∧
        equationMap hm θ v (FiniteBox.patternSign s) q = q := by
  filter_upwards [eventual_domain_root] with m he
  intro hm s θ v hdom
  exact he hm θ v _ hdom (FiniteBox.patternSign_is_sign s)

end
end StructuralNote.FixedSchurExistence
