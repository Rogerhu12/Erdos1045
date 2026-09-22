import StructuralNote.FixedSchurChartSizes
import EventualExact.SchurLiftBounds
import EventualExact.QuadraticStability

/-! Uniform center size and energy on the actual fixed-Schur parameter domain. -/

namespace StructuralNote.FixedSchurChartCenterBounds

open Complex Filter Erdos1045.EventualExact
open FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum SchurLiftBounds
open CommonDomainClosure CommonDomainRadius CommonFiberBounds
open FixedSchurLinear FixedSchurChart
open scoped BigOperators Topology

noncomputable section

theorem domain_free_center_bound {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (hdom : InDomain hm θ v) (j : Fin (2 * m)) :
    ‖v j‖ ≤ 4 * (logOrder (2 * m) : ℝ) * Real.sqrt (Real.log (2 * m : ℝ)) /
      (2 * m : ℝ) ^ 2 := by
  have hn : (2 : ℝ) ≤ 2 * m := by exact_mod_cast (show 2 ≤ 2 * m by omega)
  have hlog : 0 ≤ Real.log (2 * m : ℝ) := Real.log_nonneg (by linarith)
  have hp := DiscreteSobolev.pointwise_sq_le (by omega : 2 ≤ 2 * m) v hdom.2.2.1.2.1 j
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hp
  have hb : pairEnergy (by omega) v ≤
      (logOrder (2 * m) : ℝ) ^ 2 / (2 * m : ℝ) ^ 2 := by
    simpa only [energyRadius, Nat.cast_mul, Nat.cast_ofNat] using
      (domain_energy_bounds hm θ v hdom).2
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc
    _ ≤ 12 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 *
        ((logOrder (2 * m) : ℝ) ^ 2 / (2 * m : ℝ) ^ 2) :=
      hp.trans (mul_le_mul_of_nonneg_left hb (by positivity))
    _ ≤ 16 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 *
        ((logOrder (2 * m) : ℝ) ^ 2 / (2 * m : ℝ) ^ 2) := by gcongr; norm_num
    _ = _ := by simp only [div_pow, mul_pow, Real.sq_sqrt hlog]; ring

theorem meanSquare_le_twentyFive {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (hq : ‖q‖ ≤ 5) : meanSquare q ≤ 25 := by
  have h := meanSquare_le_of_bound hn q (by norm_num : (0 : ℝ) ≤ 5)
    (fun j => by simpa only [Real.norm_eq_abs] using (norm_le_pi_norm q j).trans hq)
  norm_num at h
  exact h

theorem canonicalLift_bound {n : ℕ} (hn : 3 ≤ n) (q : Fin n → ℝ)
    (hq : ‖q‖ ≤ 5) (j : Fin n) : ‖canonicalLift q j‖ ≤ 120 / (n : ℝ) := by
  have hms := meanSquare_le_twentyFive (by omega) q hq
  have hs : Real.sqrt (meanSquare q) ≤ 5 := by
    exact (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num; exact hms⟩
  calc
    _ ≤ 6 * Real.pi / n * Real.sqrt (meanSquare q) := canonicalLift_norm_le hn q j
    _ ≤ 6 * Real.pi / n * 5 := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (30 * Real.pi) / n := by ring
    _ ≤ 120 / n := div_le_div_of_nonneg_right (by linarith [Real.pi_lt_four]) (by positivity)

theorem eventual_center_bounds : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      ‖center (coordinate (by omega) s θ v) v‖ ≤ 121 / (2 * m : ℝ) ∧
        pairEnergy (by omega) (center (coordinate (by omega) s θ v) v) ≤ 1602 := by
  have hnat : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 2 * m) tendsto_id
  filter_upwards [eventual_coordinate_properties,
    hnat.eventually CommonFiberNonlocalSizes.eventual_small_coefficients,
    hnat.eventually eventual_radius_le_inverse] with m hprops hcoeff hradius
  intro hm s θ v hdom
  have hp := hprops hm s θ v hdom
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hvsmall (j : Fin (2 * m)) : ‖v j‖ ≤ 1 / (1000 * (2 * m : ℝ)) := by
    apply (domain_free_center_bound (by omega) θ v hdom j).trans
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcoeff.2.2.1
  constructor
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro j
    have hq := canonicalLift_bound (show 3 ≤ 2 * m by omega)
      (coordinate (by omega) s θ v) hp.norm_le j
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hq
    calc
      _ ≤ ‖canonicalLift (coordinate (by omega) s θ v) j‖ + ‖v j‖ := norm_add_le _ _
      _ ≤ 120 / (2 * m : ℝ) + 1 / (1000 * (2 * m : ℝ)) := add_le_add hq (hvsmall j)
      _ ≤ 121 / (2 * m : ℝ) := by
        field_simp
        nlinarith
  · have hA := canonicalLift_pairEnergy_le hm (coordinate (by omega) s θ v) hp.antiperiodic
    have hms := meanSquare_le_twentyFive (by omega) (coordinate (by omega) s θ v) hp.norm_le
    have hv : pairEnergy (by omega) v ≤ 1 := by
      have hv' := ((domain_energy_bounds (by omega) θ v hdom).2).trans hradius
      apply hv'.trans
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((2 * m : ℕ) : ℝ))).2
      norm_num
      exact_mod_cast (show 1 ≤ 2 * m by omega)
    have hadd := QuadraticStability.pairEnergy_add_le (show 0 < 2 * m by omega)
      (canonicalLift (coordinate (by omega) s θ v)) v
    change pairEnergy (by omega) (canonicalLift (coordinate (by omega) s θ v) + v) ≤ 1602
    linarith

end
end StructuralNote.FixedSchurChartCenterBounds
