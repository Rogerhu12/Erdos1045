import Erdos1045.ExteriorGenerating
import Erdos1045.AsymptoticScales

/-! # Uniform quotient bounds and the sharp capacity scale -/

namespace Erdos1045.ExteriorClassical

open Filter
open scoped Topology
open ExteriorBoundary Configuration
open ExteriorReduction Metric Set
noncomputable section

theorem ExteriorData.quotient_sq_bound {n : ℕ} {z : Points n} (d : ExteriorData z)
    {H : ℝ} (_hH : 0 ≤ H) (hc : (1 / 2 : ℝ) ≤ d.capacity)
    (hholder : ∀ u v : ℂ, 1 ≤ ‖u‖ → 1 ≤ ‖v‖ →
      ‖laurent d.coefficient u - laurent d.coefficient v‖ ≤
        H * Real.sqrt d.energySquared * Real.sqrt ‖u - v‖)
    {r : ℝ} (hr : 1 < r) (i : Fin n) (t : ℝ) :
    ‖d.quotient i ((r : ℂ) * unit t)‖ ^ 2 ≤
      4 * H ^ 2 * d.energySquared / (r - 1) := by
  let v := (r : ℂ) * unit t
  let w := unit (d.angles.angle i)
  have hv : ‖v‖ = r := radial_norm (by linarith) t
  have hw : ‖w‖ = 1 := norm_unit _
  have hdist : r - 1 ≤ ‖v - w‖ := by simpa only [hv, hw] using norm_sub_norm_le v w
  have hd : 0 < ‖v - w‖ := lt_of_lt_of_le (by linarith) hdist
  have hh := hholder v w (by rw [hv]; exact hr.le) hw.ge
  have hs := pow_le_pow_left₀ (norm_nonneg _) hh 2
  rw [mul_pow, mul_pow, Real.sq_sqrt d.energySquared_nonneg,
    Real.sq_sqrt (norm_nonneg _)] at hs
  have hq : ‖d.quotient i v‖ ^ 2 =
      ‖laurent d.coefficient v - laurent d.coefficient w‖ ^ 2 /
        (d.capacity ^ 2 * ‖v - w‖ ^ 2) := by
    simp [ExteriorData.quotient, w, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos d.capacity_pos, mul_pow, div_pow]
  rw [show (r : ℂ) * unit t = v from rfl, hq]
  apply (div_le_iff₀ (by positivity : 0 < d.capacity ^ 2 * ‖v - w‖ ^ 2)).2
  have hc2 : (1 / 4 : ℝ) ≤ d.capacity ^ 2 := by nlinarith
  have hratio : (r - 1) * ‖v - w‖ ≤ 4 * d.capacity ^ 2 * ‖v - w‖ ^ 2 := by
    have hd2 := mul_le_mul_of_nonneg_right hdist hd.le
    have hcs := mul_le_mul_of_nonneg_right hc2 (sq_nonneg ‖v - w‖)
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hratio
    (mul_nonneg (sq_nonneg H) d.energySquared_nonneg)
  have hs' := mul_le_mul_of_nonneg_right hs (show 0 ≤ r - 1 by linarith)
  apply (le_of_mul_le_mul_right ?_ (show 0 < r - 1 by linarith))
  have heq : (4 * H ^ 2 * d.energySquared / (r - 1) *
      (d.capacity ^ 2 * ‖v - w‖ ^ 2)) * (r - 1) =
      4 * H ^ 2 * d.energySquared * (d.capacity ^ 2 * ‖v - w‖ ^ 2) := by
    field_simp [show r - 1 ≠ 0 by linarith]
  rw [heq]
  nlinarith

theorem ExteriorData.quotient_half {n : ℕ} {z : Points n} (d : ExteriorData z)
    (hn : 0 < n) {H C A : ℝ} (hA : 0 < A)
    (henergy : (n : ℝ) * d.energySquared ≤ C) (hlarge : 16 * H ^ 2 * C ≤ A)
    (hbound : ∀ i t, ‖d.quotient i (((1 + A / n : ℝ) : ℂ) * unit t)‖ ^ 2 ≤
      4 * H ^ 2 * d.energySquared / ((1 + A / n) - 1)) :
    ∀ i t, ‖d.quotient i (((1 + A / n : ℝ) : ℂ) * unit t)‖ ≤ 1 / 2 := by
  intro i t
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have he := mul_le_mul_of_nonneg_left henergy (show 0 ≤ 16 * H ^ 2 by positivity)
  have hb : 4 * H ^ 2 * d.energySquared / ((1 + A / n) - 1) ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ (by linarith [div_pos hA hn0] : 0 < (1 + A / n) - 1)).2
    have hdiv : 16 * H ^ 2 * d.energySquared ≤ A / n :=
      (le_div_iff₀ hn0).2 (by nlinarith)
    nlinarith
  have hsq := (hbound i t).trans hb
  nlinarith [norm_nonneg (d.quotient i (((1 + A / n : ℝ) : ℂ) * unit t))]

theorem hardy_radial_bound {r n V s : ℝ} (hn : 0 < n) (hr : 1 < r)
    (hscale : 1 ≤ n * (r ^ 2 - 1))
    (hh : s ^ 2 ≤ V / (2 * Real.pi * r ^ 2 * (r ^ 2 - 1))) :
    r * s ≤ Real.sqrt (n * V / (2 * Real.pi)) := by
  have hdiff : 0 < r ^ 2 - 1 := by nlinarith
  have hd : 0 < 2 * Real.pi * r ^ 2 * (r ^ 2 - 1) := by positivity
  have h := (le_div_iff₀ hd).mp hh
  have hnH := mul_le_mul_of_nonneg_left h hn.le
  have hs := mul_le_mul_of_nonneg_left hscale
    (show 0 ≤ 2 * Real.pi * (r * s) ^ 2 by positivity)
  apply Real.le_sqrt_of_sq_le
  apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).2
  nlinarith

def sharpBoundaryError (n : ℕ) (V : ℝ) : ℝ :=
  1 / (n : ℝ) + 2 * Real.sqrt ((n : ℝ) * V / (2 * Real.pi))

theorem sharpBoundaryError_nonneg (n : ℕ) (V : ℝ) : 0 ≤ sharpBoundaryError n V := by
  unfold sharpBoundaryError
  positivity

theorem ExteriorData.sharp_boundary_bound {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HL : ClassicalLaurentAnalysis) (hn : 0 < n) (hc : (1 / 2 : ℝ) ≤ d.capacity) :
    ∀ᶠ ρ : ℝ in 𝓝[<] 1, ∀ ζ ∈ sphere (0 : ℂ) ρ,
      ‖modelDerivative d.model ζ‖ ≤ 1 + sharpBoundaryError n d.energySquared := by
  let r : ℝ := 1 + 1 / n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 1 < r := by dsimp [r]; linarith [one_div_pos.mpr hn0]
  have hr0 : 0 < r := zero_lt_one.trans hr
  apply d.eventual_model_bound (a := 1 / r) (one_div_pos.mpr hr0) ((div_lt_one hr0).mpr hr)
  intro u hu
  let v : ℂ := (r : ℂ) * u⁻¹
  have hv : ‖v‖ = r := by simp [v, hu, abs_of_pos hr0]
  have hvi : v⁻¹ = ((1 / r : ℝ) : ℂ) * u := by simp [v, mul_comm]
  have heval := HL.hardy_evaluation d.coefficient d.sobolev v (by rw [hv]; exact hr)
  rw [← d.parseval_identity, hv] at heval
  have hscale : 1 ≤ (n : ℝ) * (r ^ 2 - 1) := by
    dsimp [r]
    have heq : (n : ℝ) * ((1 + 1 / n) ^ 2 - 1) = 2 + 1 / n := by field_simp; ring
    rw [heq]
    linarith [one_div_pos.mpr hn0]
  have herr := hardy_radial_bound hn0 hr hscale heval
  have hder := d.derivative_identity v (by rw [hv]; exact hr)
  have htri : ‖d.derivative v‖ ≤ d.capacity + ‖laurentDerivative d.coefficient v‖ := by
    rw [hder]
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos d.capacity_pos] using
      norm_add_le (d.capacity : ℂ) (laurentDerivative d.coefficient v)
  have hdval : ‖d.derivative v‖ =
      d.capacity * ‖modelDerivative d.model (((1 / r : ℝ) : ℂ) * u)‖ := by
    rw [BoundaryData.derivative, hvi, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos d.capacity_pos]
  rw [hdval] at htri
  have hrad' := mul_le_mul_of_nonneg_left htri hr0.le
  have hcap := mul_le_mul_of_nonneg_right hc
    (Real.sqrt_nonneg ((n : ℝ) * d.energySquared / (2 * Real.pi)))
  have hfinal : r * ‖modelDerivative d.model (((1 / r : ℝ) : ℂ) * u)‖ ≤
      1 + sharpBoundaryError n d.energySquared := by
    apply (mul_le_mul_iff_right₀ d.capacity_pos).mp
    dsimp [sharpBoundaryError, r] at hrad' ⊢
    nlinarith
  simpa only [one_div_mul_eq_div] using (le_div_iff₀ hr0).mpr
    (by simpa only [mul_comm] using hfinal)

theorem sharpBoundaryError_tendsto {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {V : ℕ → ℝ} {K : ℝ} (hV : ∀ᶠ j in atTop, 0 ≤ V j)
    (hbound : ∀ᶠ j in atTop, (N j : ℝ) ^ 2 * V j ≤ K) :
    Tendsto (fun j => sharpBoundaryError (N j) (V j)) atTop (𝓝 0) := by
  have h := (AsymptoticScales.dimension_times_tendsto hN hV hbound).div_const (2 * Real.pi)
  have hs := (Real.continuous_sqrt.tendsto 0).comp (by simpa using h)
  have ht := (AsymptoticScales.inv_dimension hN).add (hs.const_mul 2)
  simpa only [Function.comp_def, sharpBoundaryError, Real.sqrt_zero, mul_zero, add_zero] using ht

end
end Erdos1045.ExteriorClassical
