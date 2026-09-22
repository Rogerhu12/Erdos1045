import StructuralNote.CommonFiberNonlocalFrames
import StructuralNote.CommonFiberAdjacent

/-! Uniform smallness needed by the nonlocal projection argument follows from
the literal logarithmic common domain and the constructed closure root. -/

namespace StructuralNote.CommonFiberNonlocalSizes

open Erdos1045 Erdos1045.EventualExact Complex Filter
open LensClosure FiniteFourierLift FourierMultiplier SchurSpectrum
open CommonClosureEnergy CommonTangentialParameters CommonDomainClosure CommonDomainRadius
open CommonFiberGeometry CommonFiberBounds CommonFiberSmallCoefficients
open CommonFiberNonlocalFrames CommonFiberNonlocalProjection
open scoped Topology
noncomputable section

theorem eventual_small_coefficients : ∀ᶠ n : ℕ in atTop,
    16 ≤ n ∧ 10 * (logOrder n : ℝ) + 1024 ≤ n ∧
      4 * (logOrder n : ℝ) * Real.sqrt (Real.log n) / (n : ℝ) ^ 2 ≤ 1 / (1000 * n) ∧
      (10 * (logOrder n : ℝ) + 1049) / (n : ℝ) ^ 2 ≤ 1 / (1000 * n) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hq := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  have ht : Tendsto (fun n : ℕ => 16 * (Real.log n ^ 2 / (n : ℝ))) atTop (𝓝 0) := by
    simpa only [Real.rpow_two, Real.rpow_one, Function.comp_def, mul_zero] using (hq.comp hn).const_mul 16
  have hl := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hn).const_mul 40
  have hi := (tendsto_inv_atTop_zero.comp hn).const_mul 1049
  have hb : Tendsto (fun n : ℕ => (40 * Real.log n + 1049) / (n : ℝ)) atTop (𝓝 0) := by
    convert hl.add hi using 1 <;> simp only [Function.comp_def, id_eq, mul_zero, add_zero]
    funext n
    ring
  filter_upwards [eventually_ge_atTop 16, eventual_order_bound,
    (Real.tendsto_log_atTop.comp hn).eventually_ge_atTop 1,
    ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 1000 by norm_num)),
    hb.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 1000 by norm_num))] with n hn16 ho hlog ht hb
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hL := logOrder_le (show 2 ≤ n by omega)
  change 1 ≤ Real.log n at hlog
  have hs : Real.sqrt (Real.log n) ≤ Real.log n := by
    nlinarith [Real.sq_sqrt (show 0 ≤ Real.log n by linarith), Real.sqrt_nonneg (Real.log n),
      mul_nonneg (show 0 ≤ Real.log n - 1 by linarith) (show 0 ≤ Real.log n by linarith)]
  have hp : 4 * (logOrder n : ℝ) * Real.sqrt (Real.log n) ≤ 16 * Real.log n ^ 2 := by
    have hh := mul_le_mul hL hs (Real.sqrt_nonneg _) (show 0 ≤ 4 * Real.log n by linarith)
    nlinarith
  refine ⟨hn16, ho, ?_, ?_⟩
  · have ht' : 16 * Real.log n ^ 2 < (n : ℝ) / 1000 := by
      have hh := (div_lt_iff₀ hn0).mp (show 16 * Real.log n ^ 2 / (n : ℝ) < 1 / 1000 by simpa only [mul_div_assoc] using ht)
      linarith
    apply (div_le_div_iff₀ (sq_pos_of_pos hn0) (by positivity : (0 : ℝ) < 1000 * n)).mpr
    nlinarith [mul_le_mul_of_nonneg_right (hp.trans ht'.le) hn0.le]
  · have hb' := (div_lt_iff₀ hn0).mp hb
    apply (div_le_div_iff₀ (sq_pos_of_pos hn0) (by positivity : (0 : ℝ) < 1000 * n)).mpr
    have hx : 10 * (logOrder n : ℝ) + 1049 ≤ (n : ℝ) / 1000 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hx hn0.le]

theorem radial_width_bound {m : ℕ} (hm : 8 ≤ m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (hdom : InDomain (by omega) θ v) {ξ : ℂ}
    (hξ : ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2)
    (horder : 10 * (logOrder (2 * m) : ℝ) + 1024 ≤ 2 * m)
    (hθ : ∀ i, |θ i| ≤ 1 / (1000 * (2 * m : ℝ))) (j : Fin m) :
    0 ≤ Lens.width (2 * Real.cos (halfAngle (by omega) θ j)) (heightParameter (coordinates (by omega) v) ξ j) ∧
      Lens.width (2 * Real.cos (halfAngle (by omega) θ j)) (heightParameter (coordinates (by omega) v) ξ j) ≤
        10 / (2 * m : ℝ) ^ 2 := by
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have ha0 : 0 ≤ halfAngle (by omega) θ j :=
    (by positivity : (0 : ℝ) ≤ 2 / (2 * m)).trans (domain_angle_bounds (by omega) θ v hdom horder j).1
  have ha : halfAngle (by omega) θ j ≤ (Real.pi + 1 / 1000) / (2 * m : ℝ) := by
    have h₁ := (abs_le.mp (hθ (CommonClosureEnergy.halfIndex j))).1
    have h₂ := (abs_le.mp (hθ (successor (by omega) (CommonClosureEnergy.halfIndex j)))).2
    unfold halfAngle angleDifference
    have he : (Real.pi + 1 / 1000) / (2 * m : ℝ) = Real.pi / (2 * m : ℝ) + 1 / (1000 * (2 * m : ℝ)) := by ring
    rw [he]
    linarith
  have hasq := pow_le_pow_left₀ ha0 ha 2
  have hpi : (Real.pi + 1 / 1000) ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d4, Real.pi_pos]
  have ha10 : halfAngle (by omega) θ j ^ 2 ≤ 10 / (2 * m : ℝ) ^ 2 := by
    apply hasq.trans
    rw [div_pow]
    exact div_le_div_of_nonneg_right hpi (sq_nonneg _)
  have hw := domain_width_bound hm θ v hdom hξ horder j
  obtain ⟨_, ht, _⟩ := domain_lens_positive hm θ v hdom hξ horder j
  have hheight := Lens.height_sq ht
  have hheight0 := Lens.height_nonneg (heightParameter (coordinates (by omega) v) ξ j)
  have hheight2 : Lens.height (heightParameter (coordinates (by omega) v) ξ j) ≤ 2 := by
    nlinarith [sq_nonneg (heightParameter (coordinates (by omega) v) ξ j)]
  refine ⟨hw.1, ?_⟩
  unfold Lens.width
  nlinarith [Real.one_sub_sq_div_two_le_cos (x := halfAngle (by omega) θ j)]

theorem eventual_domain_sizes : ∃ N : ℕ, ∀ (m : ℕ) (hm : N + 128 ≤ m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ),
    InDomain (by omega) θ v → (∀ j, |σ j| ≤ 1) → ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2 →
    closure (phase (by omega) θ) (fun j => 2 * Real.cos (halfAngle (by omega) θ j)) σ (coordinates (by omega) v) ξ = 0 →
    (∀ j, |θ j| ≤ 1 / (1000 * (2 * m : ℝ))) ∧
    (∀ j, ‖difference (by omega) (center (by omega) θ v σ ξ) j‖ ≤ 1 / (1000 * (2 * m : ℝ))) ∧
    (∀ j, |radial (meanFrame (by omega) θ j) (difference (by omega) (center (by omega) θ v σ ξ) j)| ≤ 10 / (2 * m : ℝ) ^ 2) ∧
    CommonFiberAdjacent.AdjacentGeometry (by omega) θ v σ ξ := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp eventual_small_coefficients
  refine ⟨N, ?_⟩
  intro m hm θ v σ ξ hdom hσ hξ hz
  obtain ⟨_, ho, ht, hb⟩ := hN (2 * m) (by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at ho ht hb
  have hθ (j) := (domain_theta_bound (by omega) θ v hdom j).trans ht
  refine ⟨hθ, ?_, ?_, CommonFiberAdjacent.adjacent_geometry (by omega) θ v σ ξ hdom hσ hξ hz ho⟩
  · apply center_step_bound (by omega) θ v σ ξ hz
    intro j
    have hn := norm_le_pi_norm (fun k => LensIncrementDerivatives.body
      (2 * Real.cos (halfAngle (by omega) θ k)) (σ k) (heightParameter (coordinates (by omega) v) ξ k)) j
    have hB := domain_bodyNorm_bound (by omega) θ v σ hdom hξ hσ ho
    have he : ‖fiberIncrement (by omega) θ v σ ξ j‖ =
        ‖LensIncrementDerivatives.body (2 * Real.cos (halfAngle (by omega) θ j)) (σ j)
          (heightParameter (coordinates (by omega) v) ξ j)‖ := by
      simp only [fiberIncrement, LensClosure.increment, LensIncrementDerivatives.body, norm_mul, norm_unit, one_mul]
    rw [he]
    exact hn.trans (hB.trans hb)
  · apply radial_center_bound (by omega) θ v σ ξ hdom.1 hz
    intro j
    obtain ⟨hw0, hw⟩ := radial_width_bound (by omega) θ v hdom hξ ho hθ j
    rw [abs_mul, abs_of_nonneg hw0]
    exact (mul_le_mul_of_nonneg_right (hσ j) hw0).trans (by simpa only [one_mul] using hw)

end
end StructuralNote.CommonFiberNonlocalSizes
