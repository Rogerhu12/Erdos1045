import Erdos1045.CapacityControl
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Consequences of the exterior Schwarz--Christoffel formula

The SC formula itself is a permitted classical input. Its finite weighted
product bounds, off-boundary comparison, and the numerical separation
argument are proved here. The statements apply to arbitrary unit prevertices
and nonnegative turning weights of total mass two.
-/

namespace Erdos1045.ExteriorEstimates

open scoped BigOperators
noncomputable section

theorem weighted_product_scale {ι : Type*} [Fintype ι]
    (a b β : ι → ℝ) {r : ℝ} (hr : 0 < r)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hβ : ∀ i, 0 ≤ β i)
    (hab : ∀ i, a i ≤ r * b i) (hmass : ∑ i, β i = 2) :
    (∏ i, (a i) ^ (β i)) ≤ r ^ 2 * ∏ i, (b i) ^ (β i) := by
  calc
    (∏ i, (a i) ^ (β i)) ≤ ∏ i, (r * b i) ^ (β i) := by
      apply Finset.prod_le_prod
      · intro i _; exact Real.rpow_nonneg (ha i) _
      · intro i _; exact Real.rpow_le_rpow (ha i) (hab i) (hβ i)
    _ = (∏ i, r ^ (β i)) * ∏ i, (b i) ^ (β i) := by
      simp_rw [Real.mul_rpow hr.le (hb _)]
      rw [Finset.prod_mul_distrib]
    _ = r ^ 2 * ∏ i, (b i) ^ (β i) := by
      rw [← Real.rpow_sum_of_pos hr, hmass, Real.rpow_two]

def scSquared {ι : Type*} [Fintype ι] (ζ : ι → ℂ) (β : ι → ℝ) (w : ℂ) : ℝ :=
  ∏ i, (‖1 - ζ i / w‖ ^ 2 : ℝ) ^ (β i)

theorem scSquared_le_sixteen {ι : Type*} [Fintype ι]
    (ζ : ι → ℂ) (β : ι → ℝ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (hβ : ∀ i, 0 ≤ β i) (hmass : ∑ i, β i = 2)
    {w : ℂ} (hw : 1 ≤ ‖w‖) : scSquared ζ β w ≤ 16 := by
  have hfac (i : ι) : ‖1 - ζ i / w‖ ≤ 2 := by
    calc
      ‖1 - ζ i / w‖ ≤ ‖(1 : ℂ)‖ + ‖ζ i / w‖ := norm_sub_le _ _
      _ = 1 + 1 / ‖w‖ := by rw [norm_one, norm_div, hζ]
      _ ≤ 2 := by
        have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hw
        norm_num only [one_div, inv_one] at h ⊢
        linarith
  have hp := weighted_product_scale (fun i => ‖1 - ζ i / w‖ ^ 2)
    (fun _ => (1 : ℝ)) β (r := 4) (by norm_num)
    (fun i => sq_nonneg _) (fun _ => zero_le_one) hβ
    (fun i => by have h := hfac i; have hn := norm_nonneg (1 - ζ i / w); nlinarith)
    hmass
  norm_num [scSquared] at hp ⊢
  exact hp

theorem scSquared_radial {ι : Type*} [Fintype ι]
    (ζ : ι → ℂ) (β : ι → ℝ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (hβ : ∀ i, 0 ≤ β i) (hmass : ∑ i, β i = 2)
    {w : ℂ} (hw : ‖w‖ = 1) {r : ℝ} (hr : 1 ≤ r) :
    scSquared ζ β w ≤ r ^ 2 * scSquared ζ β ((r : ℂ) * w) := by
  have hr0 : 0 < r := by linarith
  apply weighted_product_scale _ _ β hr0 (fun i => sq_nonneg _)
    (fun i => sq_nonneg _) hβ _ hmass
  intro i
  have hnorm : ‖ζ i / w‖ = 1 := by rw [norm_div, hζ, hw]; norm_num
  have h := CapacityControl.radial_factor_sq hr (ζ i / w) hnorm
  have heq : ζ i / ((r : ℂ) * w) = (ζ i / w) / (r : ℂ) := by ring
  simpa only [heq] using h

theorem derivative_bound {c d p : ℝ} (hc : 0 ≤ c) (_hd : 0 ≤ d)
    (hformula : d ^ 2 = c ^ 2 * p) (hp : p ≤ 16) : d ≤ 4 * c := by
  have hm := mul_le_mul_of_nonneg_left hp (sq_nonneg c)
  nlinarith

theorem radial_derivative_bound {c r d₀ dᵣ p₀ pᵣ : ℝ}
    (hr : 0 ≤ r) (hd₀ : 0 ≤ d₀) (hdᵣ : 0 ≤ dᵣ)
    (hf₀ : d₀ ^ 2 = c ^ 2 * p₀) (hfᵣ : dᵣ ^ 2 = c ^ 2 * pᵣ)
    (hprod : p₀ ≤ r ^ 2 * pᵣ) : d₀ ≤ r * dᵣ := by
  have hm := mul_le_mul_of_nonneg_left hprod (sq_nonneg c)
  apply (sq_le_sq₀ hd₀ (mul_nonneg hr hdᵣ)).mp
  calc
    d₀ ^ 2 = c ^ 2 * p₀ := hf₀
    _ ≤ c ^ 2 * (r ^ 2 * pᵣ) := hm
    _ = (r * dᵣ) ^ 2 := by rw [mul_pow, hfᵣ]; ring

/-- A radial Cauchy--Schwarz estimate suffices on the single circle `1+1/n`.
This avoids optimizing a fractional power as in the original manuscript. -/
theorem fixed_radius_upper {n c E M : ℝ}
    (_hn : 0 < n) (hc : (1 / 2 : ℝ) ≤ c) (hE : 0 ≤ E)
    (hupper : M ≤ 1 + 1 / n + E * Real.sqrt n / (2 * c * Real.sqrt Real.pi)) :
    M ≤ 1 + 1 / n + E * Real.sqrt n / Real.sqrt Real.pi := by
  have hden : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hnum : 0 ≤ E * Real.sqrt n := by positivity
  have hcden : Real.sqrt Real.pi ≤ 2 * c * Real.sqrt Real.pi := by nlinarith
  have h := div_le_div_of_nonneg_left hnum hden hcden
  linarith

/-- Initial Hadamard localization, stated in the logarithmic form. -/
theorem initial_capacity_deficit {n c : ℝ} (hn : 1 < n) (hc : 0 < c)
    (hdet : 0 ≤ (n - 1) * Real.log 4 + n * (n - 1) * Real.log c) :
    n * (1 - c) ≤ Real.log 4 := by
  have hlog := Real.log_le_sub_one_of_pos hc
  have hm := mul_le_mul_of_nonneg_left hlog
    (show 0 ≤ n * (n - 1) by positivity)
  have hfactor : (n - 1) * (Real.log 4 - n * (1 - c)) ≥ 0 := by nlinarith
  have hnonneg := nonneg_of_mul_nonneg_right hfactor (show 0 < n - 1 by linarith)
  linarith

theorem capacity_half_of_initial {n c : ℝ} (hn : 0 < n)
    (hlarge : 2 * Real.log 4 ≤ n) (hdeficit : n * (1 - c) ≤ Real.log 4) :
    (1 / 2 : ℝ) ≤ c := by nlinarith

/-- The Holder error can be absorbed at distance `A/n` from the unit circle. -/
theorem absorb_holder_error {n A H C E d : ℝ}
    (hn : 0 < n) (hH : 0 ≤ H) (hE : 0 ≤ E) (hd : 0 ≤ d)
    (henergy : n * E ^ 2 ≤ C) (hA : 16 * H ^ 2 * C ≤ A)
    (hfar : A / n ≤ d) : H * E * Real.sqrt d ≤ d / 4 := by
  have hfar' := (div_le_iff₀ hn).mp hfar
  have henergyH := mul_le_mul_of_nonneg_left henergy (show 0 ≤ 16 * H ^ 2 by positivity)
  have hsmall : 16 * H ^ 2 * E ^ 2 ≤ d := by nlinarith
  have hsqrt := Real.sq_sqrt hd
  have hprod := mul_le_mul_of_nonneg_right hsmall hd
  have hnonneg : 0 ≤ H * E * Real.sqrt d := by positivity
  nlinarith

theorem map_separation {n A H C E d c imageDistance : ℝ}
    (hn : 0 < n) (hH : 0 ≤ H) (hE : 0 ≤ E) (hd : 0 ≤ d)
    (hc : (1 / 2 : ℝ) ≤ c)
    (henergy : n * E ^ 2 ≤ C) (hA : 16 * H ^ 2 * C ≤ A) (hfar : A / n ≤ d)
    (hmap : c * d - H * E * Real.sqrt d ≤ imageDistance) :
    A / (4 * n) ≤ imageDistance := by
  have herr := absorb_holder_error hn hH hE hd henergy hA hfar
  have hcd := mul_le_mul_of_nonneg_right hc hd
  have hfar' := (div_le_iff₀ hn).mp hfar
  apply (div_le_iff₀ (show 0 < 4 * n by positivity)).mpr
  nlinarith

theorem radius_power_bound {n : ℕ} (hn : 0 < n) {A : ℝ} (hA : 0 ≤ A) :
    (1 + A / n) ^ (n - 1) ≤ Real.exp A := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 < 1 + A / n := by positivity
  have hr1 : 1 ≤ 1 + A / (n : ℝ) := by
    have h : 0 ≤ A / (n : ℝ) := by positivity
    linarith
  have hpower : (1 + A / (n : ℝ)) ^ (n - 1) ≤ (1 + A / (n : ℝ)) ^ n :=
    pow_le_pow_right₀ hr1 (Nat.sub_le n 1)
  apply hpower.trans
  apply (Real.log_le_iff_le_exp (pow_pos hr _)).mp
  rw [Real.log_pow]
  have hlog := Real.log_le_sub_one_of_pos hr
  have hm := mul_le_mul_of_nonneg_left hlog hn0.le
  have heq : (n : ℝ) * (A / n) = A := by field_simp
  nlinarith

/-- Cauchy/Bernstein--Walsh and the SC Lipschitz bound give a uniform angle gap.
Both classical inequalities appear as explicit premises here. -/
theorem angle_separation {n A distance angleGap : ℝ}
    (hn : 0 < n) (hA : 0 < A)
    (hCauchy : 1 ≤ (8 * n * Real.exp A / A) * distance)
    (hSC : distance ≤ 4 * angleGap) :
    A / (32 * Real.exp A) / n ≤ angleGap := by
  have hexp : 0 < Real.exp A := Real.exp_pos _
  have hc := mul_le_mul_of_nonneg_left hSC (show 0 ≤ 8 * n * Real.exp A / A by positivity)
  have hmul := hCauchy.trans hc
  have hden : 0 < 32 * Real.exp A * n := by positivity
  rw [div_div]
  apply (div_le_iff₀ hden).mpr
  have hscaled := mul_le_mul_of_nonneg_right hmul hA.le
  have heq : ((8 * n * Real.exp A / A) * (4 * angleGap)) * A =
      angleGap * (32 * Real.exp A * n) := by field_simp; ring
  rw [heq] at hscaled
  simpa using hscaled

end
end Erdos1045.ExteriorEstimates
