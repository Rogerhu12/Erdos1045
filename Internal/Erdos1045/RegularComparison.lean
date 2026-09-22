import Erdos1045.HullExtremal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.Algebra.Order.Field

open scoped BigOperators Topology
open Filter

namespace Erdos1045.HullGeometry

open Configuration
noncomputable section

def regularComparison (n : ℕ) : ℝ :=
  (exponent n : ℝ) * Real.log (Real.pi / (n * Real.sin (Real.pi / n)))

def perimeterRegular (n : ℕ) : Points n :=
  fun i => ((2 * Real.pi / circlePerimeter n : ℝ) : ℂ) * regular n i

theorem perimeterRegular_perimeter (H : ClassicalHullGeometry) {n : ℕ} (hn : 3 ≤ n) :
    hullPerimeter (perimeterRegular n) = 2 * Real.pi := by
  have hr : 0 < 2 * Real.pi / circlePerimeter n :=
    div_pos (by positivity) (circlePerimeter_pos hn)
  have h := H.affine n (regular n) 0 (((2 * Real.pi / circlePerimeter n : ℝ) : ℂ))
  simp only [zero_add, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    H.regular_perimeter n hn] at h
  change hullPerimeter (perimeterRegular n) = _ at h
  rw [h]
  field_simp [(circlePerimeter_pos hn).ne']

theorem perimeterRegular_discriminant (H : ClassicalHullGeometry) {n : ℕ} (hn : 3 ≤ n) :
    discriminant (perimeterRegular n) =
      (2 * Real.pi / circlePerimeter n) ^ exponent n * (n : ℝ) ^ n := by
  have hr : 0 < 2 * Real.pi / circlePerimeter n :=
    div_pos (by positivity) (circlePerimeter_pos hn)
  change discriminant (fun i => ((2 * Real.pi / circlePerimeter n : ℝ) : ℂ) * regular n i) = _
  simpa only [zero_add, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    H.regular_discriminant n hn] using
      discriminant_affine (regular n) 0 (((2 * Real.pi / circlePerimeter n : ℝ) : ℂ))

theorem regularComparison_le_extremal (H : ClassicalHullGeometry) {n : ℕ}
    (hn : 3 ≤ n) {z : Points n} (hz : PerimeterExtremal n z) :
    regularComparison n ≤ Real.log (discriminant z) - n * Real.log n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hr : 0 < 2 * Real.pi / circlePerimeter n :=
    div_pos (by positivity) (circlePerimeter_pos hn)
  have hc : 0 < discriminant (perimeterRegular n) := by
    rw [perimeterRegular_discriminant H hn]
    positivity
  have h := Real.log_le_log hc (hz.2 (perimeterRegular n) (perimeterRegular_perimeter H hn).le)
  rw [perimeterRegular_discriminant H hn,
    Real.log_mul (pow_pos hr _).ne' (pow_pos hn0 _).ne', Real.log_pow, Real.log_pow] at h
  have heq : 2 * Real.pi / circlePerimeter n = Real.pi / (n * Real.sin (Real.pi / n)) := by
    unfold circlePerimeter
    ring
  rw [heq] at h
  unfold regularComparison
  linarith

theorem regularComparison_nonneg {n : ℕ} (hn : 3 ≤ n) : 0 ≤ regularComparison n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsin : 0 < n * Real.sin (Real.pi / n) := by
    have h := circlePerimeter_pos hn
    unfold circlePerimeter at h
    nlinarith
  have hsinle := Real.sin_le (show 0 ≤ Real.pi / (n : ℝ) by positivity)
  have hden : n * Real.sin (Real.pi / n) ≤ Real.pi := by
    have h := mul_le_mul_of_nonneg_left hsinle hn0.le
    have heq : (n : ℝ) * (Real.pi / n) = Real.pi := by field_simp
    rwa [heq] at h
  have hratio : 1 ≤ Real.pi / (n * Real.sin (Real.pi / n)) := (one_le_div hsin).mpr hden
  exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hratio)

theorem extremal_log_discriminant_ge (H : ClassicalHullGeometry) {n : ℕ}
    (hn : 3 ≤ n) {z : Points n} (hz : PerimeterExtremal n z) :
    0 ≤ Real.log (discriminant z) - n * Real.log n :=
  (regularComparison_nonneg hn).trans (regularComparison_le_extremal H hn hz)

theorem perimeterExtremal_discriminant_ge (H : ClassicalHullGeometry) {n : ℕ}
    (hn : 3 ≤ n) {z : Points n} (hz : PerimeterExtremal n z) :
    (n : ℝ) ^ n ≤ discriminant z := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  apply (Real.log_le_log_iff (pow_pos hn0 n) (perimeterExtremal_discriminant_pos H hn hz)).mp
  rw [Real.log_pow]
  have h := extremal_log_discriminant_ge H hn hz
  linarith

theorem perimeterExtremal_perm (H : ClassicalHullGeometry) {n : ℕ}
    {z : Points n} (hz : PerimeterExtremal n z) (σ : Equiv.Perm (Fin n)) :
    PerimeterExtremal n (z ∘ σ) := by
  refine ⟨?_, ?_⟩
  · rw [H.perm]
    exact hz.1
  · intro w hw
    rw [discriminant_perm]
    exact hz.2 w hw

/-- The ordinary scalar Taylor coefficient at the origin; no dimension-dependent
or extremal estimate is included in this classical input. -/
structure ClassicalSineExpansion : Prop where
  log_sine : Tendsto (fun x : ℝ => Real.log (x / Real.sin x) / x ^ 2)
    (𝓝[>] (0 : ℝ)) (𝓝 (1 / 6 : ℝ))

theorem regularComparison_tendsto (T : ClassicalSineExpansion)
    {N : ℕ → ℕ} (hN3 : ∀ j, 3 ≤ N j) (hN : Tendsto N atTop atTop) :
    Tendsto (fun j => regularComparison (N j)) atTop (𝓝 (Real.pi ^ 2 / 6)) := by
  have hNR : Tendsto (fun j => (N j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hx0 : Tendsto (fun j => Real.pi / (N j : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop hNR
  have hx : Tendsto (fun j => Real.pi / (N j : ℝ)) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hx0, Filter.Eventually.of_forall ?_⟩
    intro j
    have hn0 : (0 : ℝ) < N j := by exact_mod_cast (show 0 < N j by have := hN3 j; omega)
    exact div_pos Real.pi_pos hn0
  have hcoef : Tendsto (fun j => (1 - 1 / (N j : ℝ)) * Real.pi ^ 2)
      atTop (𝓝 (Real.pi ^ 2)) := by
    have hi : Tendsto (fun j => (1 : ℝ) / N j) atTop (𝓝 (0 : ℝ)) :=
      tendsto_const_nhds.div_atTop hNR
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hi).mul_const (Real.pi ^ 2)
  have h := hcoef.mul (T.log_sine.comp hx)
  convert h using 1
  · funext j
    have hn0 : (N j : ℝ) ≠ 0 := by exact_mod_cast (show N j ≠ 0 by have := hN3 j; omega)
    have hn1 : 1 ≤ N j := by have := hN3 j; omega
    have hp : Real.pi ≠ 0 := Real.pi_ne_zero
    unfold regularComparison exponent
    rw [Nat.cast_mul, Nat.cast_sub hn1, Nat.cast_one]
    have heq : Real.pi / ((N j : ℝ) * Real.sin (Real.pi / N j)) =
        (Real.pi / N j) / Real.sin (Real.pi / N j) := by ring
    rw [heq]
    simp only [Function.comp_apply]
    field_simp
  · congr 1
    ring

end
end Erdos1045.HullGeometry
