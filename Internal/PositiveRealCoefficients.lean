import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Tactic

/-! # Taylor coefficient bounds for functions with nonnegative real part

This file concerns ordinary holomorphic disk functions. It does not assert
existence of an exterior conformal map or positivity of a Faber kernel. -/

namespace ExteriorReduction.PositiveReal

open Complex Metric MeasureTheory Set Real
open scoped ComplexConjugate Topology ENNReal
noncomputable section

def taylorCoefficient (H : ℂ → ℂ) (k : ℕ) : ℂ :=
  iteratedDeriv k H 0 / (k.factorial : ℂ)

theorem norm_circleAverage_le (f : ℂ → ℂ) (c : ℂ) (r : ℝ) :
    ‖circleAverage f c r‖ ≤ circleAverage (fun z => ‖f z‖) c r := by
  rw [circleAverage_def, circleAverage_def, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < (2 * Real.pi)⁻¹), smul_eq_mul]
  exact mul_le_mul_of_nonneg_left
    (intervalIntegral.norm_integral_le_integral_norm (by positivity : (0 : ℝ) ≤ 2 * Real.pi))
    (by positivity)

theorem mean_re {H : ℂ → ℂ} {r : ℝ}
    (hH : DiffContOnCl ℂ H (ball 0 |r|)) :
    circleAverage (fun z => (H z).re) 0 r = (H 0).re := by
  have hi := hH.continuousOn_ball.mono sphere_subset_closedBall |>.circleIntegrable'
  have h := Complex.reCLM.circleAverage_comp_comm hi
  simpa only [Function.comp_def, Complex.reCLM_apply, hH.circleAverage] using h

theorem mean_positive_mode {H : ℂ → ℂ} {r : ℝ} {k : ℕ} (hk : k ≠ 0)
    (hH : DiffContOnCl ℂ H (ball 0 |r|)) :
    circleAverage (fun z => z ^ k * H z) 0 r = 0 := by
  have h : DiffContOnCl ℂ (fun z => z ^ k * H z) (ball 0 |r|) :=
    ⟨(differentiableOn_id.pow k).mul hH.1, (continuousOn_id.pow k).mul hH.2⟩
  simpa [hk] using h.circleAverage

theorem mean_conjugate_mode {H : ℂ → ℂ} {r : ℝ} {k : ℕ} (hk : k ≠ 0)
    (hH : DiffContOnCl ℂ H (ball 0 |r|)) :
    circleAverage (fun z => conj z ^ k * conj (H z)) 0 r = 0 := by
  have hp : DiffContOnCl ℂ (fun z => z ^ k * H z) (ball 0 |r|) :=
    ⟨(differentiableOn_id.pow k).mul hH.1, (continuousOn_id.pow k).mul hH.2⟩
  have hi := hp.continuousOn_ball.mono sphere_subset_closedBall |>.circleIntegrable'
  have h := Complex.conjCLE.toContinuousLinearMap.circleAverage_comp_comm hi
  change circleAverage (fun z => conj (z ^ k * H z)) 0 r =
    conj (circleAverage (fun z => z ^ k * H z) 0 r) at h
  simpa only [map_mul, map_pow,
    mean_positive_mode hk hH, map_zero] using h

/-- The Fourier moment of a positive real part is controlled by its mean.
The vanishing of the conjugate mode comes from holomorphicity. -/
theorem weighted_moment_bound {H : ℂ → ℂ} {r : ℝ} {k : ℕ}
    (hr : 0 < r) (hk : k ≠ 0) (hH : DiffContOnCl ℂ H (ball 0 r))
    (hpos : ∀ z ∈ sphere (0 : ℂ) r, 0 ≤ (H z).re) :
    ‖circleAverage (fun z => conj z ^ k * H z) 0 r‖ ≤
      2 * r ^ k * (H 0).re := by
  have hH' : DiffContOnCl ℂ H (ball 0 |r|) := by rwa [abs_of_pos hr]
  have hcont : ContinuousOn H (sphere (0 : ℂ) r) :=
    hH.continuousOn_ball.mono sphere_subset_closedBall
  have hi₁ : CircleIntegrable (fun z => conj z ^ k * H z) 0 r :=
    ((continuous_conj.pow k).continuousOn.mul hcont).circleIntegrable hr.le
  have hi₂ : CircleIntegrable (fun z => conj z ^ k * conj (H z)) 0 r :=
    ((continuous_conj.pow k).continuousOn.mul (continuous_conj.comp_continuousOn hcont)).circleIntegrable hr.le
  have hadd : circleAverage (fun z => conj z ^ k * H z) 0 r =
      circleAverage (fun z => (2 : ℂ) * (conj z ^ k * ((H z).re : ℂ))) 0 r := by
    have hsum := circleAverage_fun_add hi₁ hi₂
    rw [mean_conjugate_mode hk hH', add_zero] at hsum
    rw [← hsum]
    congr 1
    funext z
    rw [← mul_add, Complex.add_conj]
    push_cast
    ring
  rw [hadd]
  apply (norm_circleAverage_le _ 0 r).trans
  have hi : CircleIntegrable (fun z => ‖(2 : ℂ) * (conj z ^ k * ((H z).re : ℂ))‖) 0 r := by
    apply ContinuousOn.circleIntegrable hr.le
    fun_prop (disch := assumption)
  have hj : CircleIntegrable (fun z => 2 * r ^ k * (H z).re) 0 r := by
    apply ContinuousOn.circleIntegrable hr.le
    fun_prop (disch := assumption)
  calc
    circleAverage (fun z => ‖(2 : ℂ) * (conj z ^ k * ((H z).re : ℂ))‖) 0 r ≤
        circleAverage (fun z => (2 * r ^ k) * (H z).re) 0 r := by
      apply circleAverage_mono hi hj
      intro z hz
      have hz' : ‖z‖ = r := by simpa [abs_of_pos hr, mem_sphere, dist_zero_right] using hz
      simp [norm_pow, hz', Complex.norm_real,
        abs_of_nonneg (hpos z (by simpa [abs_of_pos hr] using hz)), mul_assoc]
    _ = _ := by
      rw [show (fun z => (2 * r ^ k) * (H z).re) =
        (fun z => (2 * r ^ k) • (H z).re) from rfl, circleAverage_fun_smul, mean_re hH']
      rfl

theorem cauchy_coefficient_average {H : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hH : DiffContOnCl ℂ H (ball 0 r)) (k : ℕ) :
    circleAverage (fun z => (z ^ k)⁻¹ * H z) 0 r = taylorCoefficient H k := by
  rw [circleAverage_eq_circleIntegral hr.ne']
  have heq : (fun z : ℂ => (z - 0)⁻¹ • ((z ^ k)⁻¹ * H z)) =
      (fun z => (1 / (z - 0) ^ (k + 1)) • H z) := by
    funext z
    simp only [sub_zero, smul_eq_mul, one_div, pow_succ, mul_inv_rev]
    ring
  rw [heq, hH.circleIntegral_one_div_sub_center_pow_smul hr k]
  simp only [smul_eq_mul, taylorCoefficient]
  field_simp [Complex.two_pi_I_ne_zero]

theorem conjugate_on_sphere {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : z ∈ sphere (0 : ℂ) r) : conj z = (r : ℂ) ^ 2 / z := by
  have hnorm : ‖z‖ = r := by simpa [mem_sphere, dist_zero_right] using hz
  have hzero : z ≠ 0 := by intro h; simp [h] at hnorm; linarith
  apply (eq_div_iff hzero).mpr
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
  norm_cast

theorem weighted_moment_coefficient {H : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hH : DiffContOnCl ℂ H (ball 0 r)) (k : ℕ) :
    circleAverage (fun z => conj z ^ k * H z) 0 r =
      ((r : ℂ) ^ 2) ^ k * taylorCoefficient H k := by
  calc
    _ = circleAverage (fun z => ((r : ℂ) ^ 2) ^ k • ((z ^ k)⁻¹ * H z)) 0 r := by
      apply circleAverage_congr_sphere
      intro z hz
      dsimp only
      rw [conjugate_on_sphere hr (by simpa [abs_of_pos hr] using hz), div_pow]
      simp only [smul_eq_mul, div_eq_mul_inv]
      ring
    _ = _ := by rw [circleAverage_fun_smul, cauchy_coefficient_average hr hH]; rfl

/-- Caratheodory's finite-radius coefficient estimate, in terms of actual
Taylor coefficients computed by iterated derivatives. -/
theorem coefficient_radius_bound {H : ℂ → ℂ} {r : ℝ} {k : ℕ}
    (hr : 0 < r) (hk : k ≠ 0) (hH : DiffContOnCl ℂ H (ball 0 r))
    (hpos : ∀ z ∈ sphere (0 : ℂ) r, 0 ≤ (H z).re) :
    ‖taylorCoefficient H k‖ * r ^ k ≤ 2 * (H 0).re := by
  have h := weighted_moment_bound hr hk hH hpos
  rw [weighted_moment_coefficient hr hH k, norm_mul, norm_pow, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at h
  rw [show (r ^ 2) ^ k = (r ^ k) ^ 2 by rw [← pow_mul, ← pow_mul, Nat.mul_comm]] at h
  have hp : 0 < r ^ k := pow_pos hr k
  apply (mul_le_mul_iff_right₀ hp).mp
  convert h using 1 <;> first | rfl | ring

/-- The full Caratheodory coefficient estimate on the open unit disk. -/
theorem taylor_coefficient_bound {H : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H (ball 0 1))
    (hpos : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ (H z).re)
    (k : ℕ) (hk : k ≠ 0) :
    ‖taylorCoefficient H k‖ ≤ 2 * (H 0).re := by
  have hl : Filter.Tendsto (fun r : ℝ => ‖taylorCoefficient H k‖ * r ^ k)
      (nhdsWithin 1 (Iio 1)) (nhds ‖taylorCoefficient H k‖) := by
    simpa only [Pi.mul_apply, Pi.pow_apply, id_eq, one_pow, mul_one] using!
      ((continuous_const.mul (continuous_id.pow k)).continuousAt
      (x := (1 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hl
  have hp : ∀ᶠ r : ℝ in nhdsWithin 1 (Iio 1), 0 < r :=
    nhdsWithin_le_nhds (Ioi_mem_nhds zero_lt_one)
  filter_upwards [hp, self_mem_nhdsWithin] with r hr hr1
  have hsub : closedBall (0 : ℂ) r ⊆ ball 0 1 := closedBall_subset_ball hr1
  exact coefficient_radius_bound hr hk (hH.diffContOnCl_ball hsub)
    (fun z hz => hpos z (hsub (sphere_subset_closedBall hz)))

/-- Normalization H(0)=1 gives the coefficient bound 2 for every k>=1. -/
theorem normalized_taylor_coefficient_bound {H : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H (ball 0 1)) (hzero : H 0 = 1)
    (hpos : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ (H z).re)
    (k : ℕ) (hk : k ≠ 0) : ‖taylorCoefficient H k‖ ≤ 2 := by
  simpa [hzero] using taylor_coefficient_bound hH hpos k hk

theorem powerSeries_coefficient_eq {H : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {R : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall H p 0 R) (k : ℕ) :
    p k (fun _ => 1) = taylorCoefficient H k := by
  have h := hp.factorial_smul (1 : ℂ) k
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const_one, one_smul] at h
  unfold taylorCoefficient
  apply (eq_div_iff (by exact_mod_cast k.factorial_ne_zero)).mpr
  simpa only [nsmul_eq_mul, mul_comm] using h

/-- A direct bridge for a later identification of a generating kernel with
its actual holomorphic power series. No positivity or kernel identification
is asserted by this theorem. -/
theorem normalized_powerSeries_coefficient_bound {H : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {R : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall H p 0 R)
    (hH : DifferentiableOn ℂ H (ball 0 1)) (hzero : H 0 = 1)
    (hpos : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ (H z).re)
    (k : ℕ) (hk : k ≠ 0) : ‖p k (fun _ => 1)‖ ≤ 2 := by
  rw [powerSeries_coefficient_eq hp k]
  exact normalized_taylor_coefficient_bound hH hzero hpos k hk

theorem normalized_scalar_coefficient_bound {H : ℂ → ℂ} {a : ℕ → ℂ} {R : ℝ≥0∞}
    (ha : HasFPowerSeriesOnBall H (FormalMultilinearSeries.ofScalars ℂ a) 0 R)
    (hH : DifferentiableOn ℂ H (ball 0 1)) (hzero : H 0 = 1)
    (hpos : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ (H z).re)
    (k : ℕ) (hk : k ≠ 0) : ‖a k‖ ≤ 2 := by
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq, one_pow, smul_eq_mul, mul_one] using
    normalized_powerSeries_coefficient_bound ha hH hzero hpos k hk

end
end ExteriorReduction.PositiveReal
