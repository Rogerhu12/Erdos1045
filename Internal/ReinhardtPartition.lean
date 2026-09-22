import Erdos1045.ClosedHullGeometry
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

/-!
# The sharp analytic endpoint of the finite normal-fan argument

Integrating one projection on an angular interval gives a chord length.
Concavity of sine then gives the sharp Reinhardt constant. The geometric
construction of the finite normal partition is a separate obligation.
-/

namespace ExteriorReduction.Reinhardt

open Complex Set MeasureTheory
open Erdos1045.Configuration Erdos1045.HullGeometry
open scoped BigOperators

noncomputable section

def width {n : ℕ} (z : Points n) (t : ℝ) : ℝ := support z t + support z (t + Real.pi)

theorem width_continuous {n : ℕ} (z : Points n) : Continuous (width z) :=
  (support_continuous z).add ((support_continuous z).comp (continuous_id.add_const _))

theorem width_integral {n : ℕ} (z : Points n) :
    (∫ t in (0 : ℝ)..(2 * Real.pi), width z t) = 2 * hullPerimeter z := by
  unfold width
  have hc : Continuous (fun t : ℝ => support z (t + Real.pi)) :=
    (support_continuous z).comp (continuous_id.add_const _)
  rw [intervalIntegral.integral_add (f := support z) (g := fun t => support z (t + Real.pi))
    ((support_continuous z).intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  rw [intervalIntegral.integral_comp_add_right]
  have hs := (support_periodic z).intervalIntegral_add_eq 0 Real.pi
  simp only [zero_add] at hs ⊢
  rw [add_comm (2 * Real.pi) Real.pi, ← hs]
  unfold hullPerimeter
  ring

theorem projection_integral_chord (v : ℂ) (a b : ℝ) :
    (∫ t in a..b, (v * Complex.exp (-((t : ℂ) * Complex.I))).re) =
      2 * Real.sin ((b - a) / 2) *
        (v * Complex.exp (-((((a + b) / 2 : ℝ) : ℂ) * Complex.I))).re := by
  rw [projection_integral_interval, point_projection, Real.sin_sub_sin, Real.cos_sub_cos]
  have hm : (b + a) / 2 = (a + b) / 2 := by ring
  have hd : (a - b) / 2 = -((b - a) / 2) := by ring
  rw [hm, hd, Real.sin_neg]
  ring

theorem projection_integral_le_chord {v : ℂ} (hv : ‖v‖ ≤ 1)
    {a b : ℝ} (hab : a ≤ b) (hspan : b - a ≤ 2 * Real.pi) :
    (∫ t in a..b, (v * Complex.exp (-((t : ℂ) * Complex.I))).re) ≤
      2 * Real.sin ((b - a) / 2) := by
  rw [projection_integral_chord]
  have hs : 0 ≤ Real.sin ((b - a) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hp : (v * Complex.exp (-((((a + b) / 2 : ℝ) : ℂ) * Complex.I))).re ≤ 1 := by
    apply (Complex.re_le_norm _).trans
    simpa [norm_mul, Complex.norm_exp] using hv
  nlinarith

theorem sum_sine_le {m : ℕ} (hm : 0 < m) (α : Fin m → ℝ)
    (hα : ∀ i, 0 ≤ α i) (hsum : ∑ i, α i = Real.pi) :
    (∑ i, Real.sin (α i)) ≤ m * Real.sin (Real.pi / m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmem : ∀ i ∈ (Finset.univ : Finset (Fin m)), α i ∈ Icc (0 : ℝ) Real.pi := by
    intro i hi
    refine ⟨hα i, ?_⟩
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => hα j) hi
  have hw : ∑ _i : Fin m, (1 / (m : ℝ)) = 1 := by simp [hm.ne']
  have hj := strictConcaveOn_sin_Icc.concaveOn.le_map_sum
    (t := (Finset.univ : Finset (Fin m))) (w := fun _ => 1 / (m : ℝ))
    (p := α) (fun _ _ => by positivity) hw hmem
  simp only [smul_eq_mul, one_div, ← div_eq_inv_mul] at hj
  rw [← Finset.sum_div, ← Finset.sum_div, hsum] at hj
  simpa only [mul_comm] using (div_le_iff₀ hmR).mp hj

/-- The exact sharp constant for a partition with `2*n` cells. Empty cells
are allowed, so a shorter normal fan can be padded without changing the sum. -/
theorem half_chord_sum_le {n : ℕ} (hn : 0 < n) (δ : Fin (2 * n) → ℝ)
    (hδ : ∀ i, 0 ≤ δ i) (hsum : ∑ i, δ i = 2 * Real.pi) :
    (∑ i, Real.sin (δ i / 2)) ≤ diameterPerimeterBound n := by
  have hs : ∑ i, δ i / 2 = Real.pi := by rw [← Finset.sum_div, hsum]; ring
  have hh := sum_sine_le (by omega : 0 < 2 * n) (fun i => δ i / 2)
    (fun i => div_nonneg (hδ i) (by norm_num)) hs
  simpa [diameterPerimeterBound, Nat.cast_mul, Nat.cast_ofNat] using hh

#print axioms width_integral
#print axioms projection_integral_le_chord
#print axioms half_chord_sum_le

end
end ExteriorReduction.Reinhardt
