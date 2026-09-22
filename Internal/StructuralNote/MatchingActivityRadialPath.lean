import StructuralNote.MatchingActivityRadialFeasible

/-! A one-sided outward path at an actually unsaturated matching edge. -/

namespace StructuralNote.MatchingActivityRadialPath

open Erdos1045 Erdos1045.EventualExact Complex Configuration Filter
open LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open CommonClosureEnergy CommonFiberGeometry MatchingActivityRadialClosure
open MatchingActivityRadialGeometry MatchingActivityRadialIntegration MatchingActivityRadialConstraints
open MatchingActivityRadialFeasible
open scoped Topology ContDiff
noncomputable section

def radiusPath {m : ℕ} (r : Fin m → ℝ) (i : Fin m) (t : ℝ) : Fin m → ℝ :=
  Function.update r i (r i + t)

theorem radiusPath_zero {m : ℕ} (r : Fin m → ℝ) (i : Fin m) : radiusPath r i 0 = r := by
  simp [radiusPath]

theorem radiusPath_contDiff {m : ℕ} (r : Fin m → ℝ) (i : Fin m) : ContDiff ℝ ∞ (radiusPath r i) := by
  apply contDiff_pi.mpr
  intro j
  by_cases hj : j = i
  · subst j
    simp only [radiusPath, Function.update_self]
    fun_prop
  · simp only [radiusPath, Function.update_of_ne hj]
    exact contDiff_const

def outwardPath {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (a : ℂ) (g : (Fin m → ℝ) → ℂ) (i : Fin m) (t : ℝ) : Points (2 * m) :=
  radialConfiguration hm θ σ ν (radiusPath r i t) (g (radiusPath r i t)) a

theorem outwardPath_properties {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (a : ℂ) (g : (Fin m → ℝ) → ℂ) (i : Fin m)
    (hchart : IsFeasibleRadialChart hm θ σ ν r a g)
    (hθ : HalfPeriodic hm (fun j => (θ j : ℂ)))
    (hr : ∀ j, 0 ≤ r j ∧ r j ≤ 1) (hi : r i < 1) :
    outwardPath hm θ σ ν r a g i 0 = radialConfiguration hm θ σ ν r 0 a ∧
    ContDiffAt ℝ ∞ (outwardPath hm θ σ ν r a g i) 0 ∧
    (∀ᶠ t in 𝓝 (0 : ℝ), 0 ≤ t →
      DiameterAtMost 2 (outwardPath hm θ σ ν r a g i t) ∧
      ‖outwardPath hm θ σ ν r a g i t (halfTurn hm (CommonClosureEnergy.halfIndex i)) -
        outwardPath hm θ σ ν r a g i t (CommonClosureEnergy.halfIndex i)‖ = 2 * (r i + t)) := by
  have hp := (radiusPath_contDiff r i).contDiffAt (x := (0 : ℝ))
  have hF := hchart.2.2.2.2.1
  have hF' : ContDiffAt ℝ ∞ (fun r' => radialConfiguration hm θ σ ν r' (g r') a) (radiusPath r i 0) := by
    rw [radiusPath_zero]
    exact hF
  refine ⟨?_, hF'.comp 0 hp, ?_⟩
  · simp only [outwardPath, radiusPath_zero, hchart.2.1]
  have hnear : Tendsto (radiusPath r i) (𝓝 0) (𝓝 r) := by
    simpa only [radiusPath_zero] using hp.continuousAt.tendsto
  have he := hnear.eventually hchart.2.2.2.2.2
  have hz := hnear.eventually hchart.2.2.2.1
  have hi' : (0 : ℝ) < 1 - r i := by linarith
  filter_upwards [he, hz, eventually_lt_nhds hi'] with t ht hz' hlt hnonneg
  have hr' (j : Fin m) : |radiusPath r i t j| ≤ 1 := by
    by_cases hj : j = i
    · subst j
      simp only [radiusPath, Function.update_self]
      exact abs_le.mpr ⟨by linarith [(hr i).1], by linarith⟩
    · simp only [radiusPath, Function.update_of_ne hj]
      exact abs_le.mpr ⟨by linarith [(hr j).1], (hr j).2⟩
  refine ⟨ht hr', ?_⟩
  change ‖radialConfiguration hm θ σ ν (radiusPath r i t) (g (radiusPath r i t)) a (halfTurn hm (CommonClosureEnergy.halfIndex i)) -
    radialConfiguration hm θ σ ν (radiusPath r i t) (g (radiusPath r i t)) a (CommonClosureEnergy.halfIndex i)‖ = _
  rw [matching_distance hm θ σ ν (radiusPath r i t) (g (radiusPath r i t)) a hθ hz',
    radiusFull_halfIndex]
  simp only [radiusPath, Function.update_self]
  rw [abs_of_nonneg (by linarith [(hr i).1])]

end
end StructuralNote.MatchingActivityRadialPath
