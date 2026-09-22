import EventualExact.SupGapEdges
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Relative edge control for actual polar coordinates from a finite radial budget. -/

namespace Erdos1045.EventualExact.RadialEdges

open Complex CyclicAngles GapRigidity FiniteCircleRigidity Filter
open scoped Topology
noncomputable section

def residual {n : ℕ} (a : Angles n) (R : ℕ → ℝ) (c : ℝ) (j : ℕ) : ℂ :=
  ((R j / c - 1 : ℝ) : ℂ) * circlePoints a j

def perturbation {n : ℕ} (a : Angles n) (R : ℕ → ℝ) (c : ℝ) (j : ℕ) : ℂ :=
  circlePerturbation a j + residual a R c j

def edgeError {n : ℕ} (a : Angles n) (ρ : ℝ) : ℝ :=
  5 * Real.pi / 2 * ‖gapDeviation a‖ +
    Real.pi * (12 * Real.sqrt ρ + ρ) * (1 + ‖gapDeviation a‖)

theorem edgeError_nonneg {n : ℕ} (a : Angles n) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    0 ≤ edgeError a ρ := by unfold edgeError; positivity

theorem perturbation_periodic {n : ℕ} (a : Angles n) (hn : 0 < n)
    (R : ℕ → ℝ) (hR : Function.Periodic R n) (c : ℝ) :
    Function.Periodic (perturbation a R c) n := by
  intro j
  simp only [perturbation, residual, circlePerturbation_periodic a hn j,
    circlePoints_periodic a j, hR j]

theorem perturbation_eq {n : ℕ} (a : Angles n) (R : ℕ → ℝ) (c : ℝ) (j : ℕ) :
    LocalPhase.regularRoot n ^ j + perturbation a R c j =
      ((R j / c : ℝ) : ℂ) * circlePoints a j := by
  unfold perturbation residual circlePerturbation
  push_cast
  ring

theorem residual_edge_bound {n : ℕ} (a : Angles n) (R : ℕ → ℝ)
    {c ρ L : ℝ} (hc : 1 / 2 ≤ c) (hρ : 0 ≤ ρ) (hL : 0 ≤ L)
    (hclose : ∀ j, |R j - c| ≤ ρ)
    (hdiff : ∀ j, |R (j + 1) - R j| ≤ L * window a 1 j) (j : ℕ) :
    ‖residual a R c (j + 1) - residual a R c j‖ ≤
      (2 * L + 2 * ρ) * window a 1 j := by
  have hc0 : 0 < c := by linarith
  have hg : 0 ≤ window a 1 j := (window_pos a (by norm_num) j).le
  have hcircle : ‖circlePoints a (j + 1) - circlePoints a j‖ ≤ window a 1 j := by
    have h := circle_lipschitz (a.angle ((j + 1 : ℕ) : ℤ) - a.angle 0)
      (a.angle j - a.angle 0)
    have he : a.angle ((j + 1 : ℕ) : ℤ) - a.angle 0 - (a.angle j - a.angle 0) =
        window a 1 j := by simp [window]
    simpa only [circlePoints, he, abs_of_nonneg hg] using h
  have heq : residual a R c (j + 1) - residual a R c j =
      (((R (j + 1) - R j) / c : ℝ) : ℂ) * circlePoints a (j + 1) +
      (((R j - c) / c : ℝ) : ℂ) * (circlePoints a (j + 1) - circlePoints a j) := by
    unfold residual
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hc0.ne']
    ring
  have hfirst : |(R (j + 1) - R j) / c| ≤ 2 * L * window a 1 j := by
    rw [abs_div, abs_of_pos hc0]
    apply (div_le_iff₀ hc0).mpr
    have hm := mul_le_mul_of_nonneg_right hc (mul_nonneg hL hg)
    nlinarith [hdiff j]
  have hsecond : |(R j - c) / c| ≤ 2 * ρ := by
    rw [abs_div, abs_of_pos hc0]
    apply (div_le_iff₀ hc0).mpr
    have hm := mul_le_mul_of_nonneg_right hc hρ
    nlinarith [hclose j]
  rw [heq]
  calc
    _ ≤ ‖(((R (j + 1) - R j) / c : ℝ) : ℂ) * circlePoints a (j + 1)‖ +
        ‖(((R j - c) / c : ℝ) : ℂ) * (circlePoints a (j + 1) - circlePoints a j)‖ := norm_add_le _ _
    _ = |(R (j + 1) - R j) / c| + |(R j - c) / c| *
        ‖circlePoints a (j + 1) - circlePoints a j‖ := by
      simp only [norm_mul, circlePoints, circle_norm, Complex.norm_real, Real.norm_eq_abs, mul_one]
    _ ≤ 2 * L * window a 1 j + (2 * ρ) * window a 1 j :=
      add_le_add hfirst (mul_le_mul hsecond hcircle (norm_nonneg _) (by positivity))
    _ = _ := by ring

theorem relative_edge_bound {n : ℕ} (a : Angles n) (hn : 2 ≤ n) (R : ℕ → ℝ)
    {c ρ : ℝ} (hc : 1 / 2 ≤ c) (hρ : 0 ≤ ρ)
    (hclose : ∀ j, |R j - c| ≤ ρ)
    (hdiff : ∀ j, |R (j + 1) - R j| ≤ 12 * Real.sqrt ρ * window a 1 j) (j : ℕ) :
    ‖perturbation a R c (j + 1) - perturbation a R c j‖ ≤
      edgeError a ρ * ‖LocalPhase.regularRoot n - 1‖ := by
  have heq : perturbation a R c (j + 1) - perturbation a R c j =
      (circlePerturbation a (j + 1) - circlePerturbation a j) +
        (residual a R c (j + 1) - residual a R c j) := by unfold perturbation; ring
  have hr := residual_edge_bound a R hc hρ (by positivity) hclose hdiff j
  have hw := mul_le_mul_of_nonneg_left (SupGapEdges.window_le_edge a hn j)
    (show 0 ≤ 2 * (12 * Real.sqrt ρ) + 2 * ρ by positivity)
  rw [heq]
  have ht := (norm_add_le _ _).trans (add_le_add (SupGapEdges.circle_edge_bound a hn j) (hr.trans hw))
  calc
    _ ≤ _ := ht
    _ = _ := by unfold edgeError; ring

theorem edgeError_tendsto_zero {N : ℕ → ℕ} (a : ∀ j, Angles (N j)) {ρ : ℕ → ℝ}
    (hg : Tendsto (fun j => ‖gapDeviation (a j)‖) atTop (𝓝 0))
    (hr : Tendsto ρ atTop (𝓝 0)) :
    Tendsto (fun j => edgeError (a j) (ρ j)) atTop (𝓝 0) := by
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hr
  have hconst : Tendsto (fun _j : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have ht := (hg.const_mul (5 * Real.pi / 2)).add
    ((((hs.const_mul 12).add hr).const_mul Real.pi).mul (hconst.add hg))
  simpa [edgeError, Function.comp_def] using ht

end
end Erdos1045.EventualExact.RadialEdges
