import StructuralNote.FixedSchurChart

/-! The fixed root lies strictly inside its contraction ball. The quantitative
margin is needed to use the contraction estimate on a neighborhood of the root. -/

namespace StructuralNote.FixedSchurStrictInterior

open Real Complex Filter Set Metric
open Erdos1045.EventualExact FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open CommonDomainClosure CommonDomainRadius EdgeCoordinates FixedSchurData
open FixedSchurDomainSmallness FixedSchurDomainSource
open FixedSchurEquations FixedSchurContraction FixedSchurChart
open scoped Topology

noncomputable section

theorem source_bound_2010 {N L H : ℝ} (hN : 0 < N) (hL : 0 ≤ L)
    (hsmall : L * H / N ≤ 1) :
    10 * L / N + 2000 * L ^ 2 * H / N ^ 2 ≤ 2010 * L / N := by
  have hprod := mul_le_mul_of_nonneg_left hsmall (div_nonneg hL hN.le)
  have he : (L / N) * (L * H / N) = L ^ 2 * H / N ^ 2 := by ring
  rw [he, mul_one] at hprod
  calc
    _ = 10 * (L / N) + 2000 * (L ^ 2 * H / N ^ 2) := by ring
    _ ≤ 10 * (L / N) + 2000 * (L / N) := by linarith
    _ = _ := by ring

theorem eventual_root_error : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
      (σ q : Fin (2 * m) → ℝ), InDomain hm θ v →
      (∀ j, σ j = 1 ∨ σ j = -1) →
      ‖q - baseWord σ‖ ≤ radius (2 * m) → equationMap hm θ v σ q = q →
      ‖q - baseWord σ‖ ≤ 4020 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) := by
  filter_upwards [eventual_domain_smallness_bundle] with m hsize
  intro hm θ v σ q hdom hσ hq hfix
  have hs := hsize.2 hm θ v σ hdom hσ
  have hf : baseWord σ ∈ closedBall (baseWord σ) (radius (2 * m)) := by simp [hs.1]
  have hsmall : ∀ j, |Y (by omega) θ j + σ j * epsilon (2 * m) *
      (tangent (by omega) v j + J (baseWord σ) j)| ≤ 1 := by
    intro j
    exact (ball_input_bound (by omega) (epsilon_pos (show 2 ≤ 2 * m by omega))
      _ _ _ _ hσ hs.2.2 hf j).trans (by norm_num)
  have hsource := domain_source_bound hm θ v σ hdom hσ hsmall
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hb := source_bound_2010 hn
    (show 0 ≤ (logOrder (2 * m) : ℝ) by positivity) hsize.1
  have herr := fixedPoint_error (by omega)
    (epsilon_pos (show 2 ≤ 2 * m by omega)) hs.1 _ _ _ _ _ hσ hs.2.2 hq hfix
  change ‖q - baseWord σ‖ ≤ 2 * ‖equationMap hm θ v σ (baseWord σ) - baseWord σ‖ at herr
  calc
    _ ≤ 2 * ‖equationMap hm θ v σ (baseWord σ) - baseWord σ‖ := herr
    _ ≤ 2 * (2010 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (hsource.trans hb) (by norm_num)
    _ = _ := by ring

theorem eventual_coordinate_interior : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (s : FiniteBox.SignPattern hm)
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain hm θ v →
      ‖coordinate hm s θ v - baseWord (FiniteBox.patternSign s)‖ < radius (2 * m) := by
  filter_upwards [eventual_root_error, eventual_coordinate_spec] with m herr hspec
  intro hm s θ v hdom
  have hp := hspec hm s θ v hdom
  have he := herr hm θ v _ _ hdom (FiniteBox.patternSign_is_sign s) hp.1 hp.2
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hL := logOrder_one_le (show 2 ≤ 2 * m by omega)
  apply he.trans_lt
  unfold radius
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  exact (div_lt_div_iff_of_pos_right hn).2 (by nlinarith)

end
end StructuralNote.FixedSchurStrictInterior
