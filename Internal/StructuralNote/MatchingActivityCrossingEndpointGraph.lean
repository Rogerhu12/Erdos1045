import StructuralNote.MatchingActivityCrossingVariationGraph

/-! The one-sided feasible crossing-control graph at a lens endpoint. -/

namespace StructuralNote.MatchingActivityCrossingEndpointGraph

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization Filter
open LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open CommonClosureEnergy CommonFiberGeometry CommonTangentialParameters BoxLensLift
open MatchingActivityRadialPair MatchingActivityRadialBounds
open MatchingActivityRadialClosure MatchingActivityRadialGeometry MatchingActivityRadialBase
open MatchingActivityRadialActual MatchingActivityRadialIntegration MatchingActivityNonlocal
open MatchingActivityRadialConstraints CommonFiberSmooth
open MatchingActivityCrossingVariationGraph
open scoped BigOperators Topology ContDiff
noncomputable section

/-- At an endpoint lens coordinate, the affine `sigma` graph remains feasible
in the inward direction `s i * t ≤ 0`. -/
theorem exists_feasible_endpoint_sigma_path {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (s ν r : Fin m → ℝ) (a : ℂ) (i : Fin m)
    (hθ : HalfPeriodic (by omega) (fun j => (θ j : ℂ)))
    (hs : ∀ j, |s j| ≤ 1) (hi : s i = 1 ∨ s i = -1)
    (hr : ∀ j, r j = 1)
    (hsmall : ∀ j, |radialPhase (by omega) θ r j - midpoint m j| + |ν j| ≤ 1 / 4)
    (hzero : closureFamily (parameters (by omega) θ s ν r) 0 = 0)
    (hw : ∀ j, 0 < Lens.width (radialLength (by omega) θ r j) (ν j))
    (hfar : ∀ (j : Fin (2 * m)) (k : Fin (2 * m)),
      k.val ≠ m - 1 → k.val ≠ m → k.val ≠ m + 1 →
      ‖radialConfiguration (by omega) θ s ν r 0 a (cyclicAdvance j k.val) -
        radialConfiguration (by omega) θ s ν r 0 a j‖ < 2) :
    ∃ ξ : ℝ → ℂ,
      ξ 0 = 0 ∧ ContDiffAt ℝ ∞ ξ 0 ∧
      crossingPath (by omega) θ s ν r a ξ i 0 =
        radialConfiguration (by omega) θ s ν r 0 a ∧
      (∀ᶠ t in 𝓝 (0 : ℝ),
        closureFamily (parameters (by omega) θ (sigmaPath s i t) ν r) (ξ t) = 0) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), s i * t ≤ 0 →
        DiameterAtMost 2 (crossingPath (by omega) θ s ν r a ξ i t) ∧
        ∀ j : Fin (2 * m),
          ‖crossingPath (by omega) θ s ν r a ξ i t (halfTurn (by omega) j) -
            crossingPath (by omega) θ s ν r a ξ i t j‖ = 2) := by
  obtain ⟨ξ, hξ0, hξ, hz⟩ := exists_smooth_sigma_root hm θ s ν r i hs hsmall hzero
  refine ⟨ξ, hξ0, hξ, by simp [crossingPath, hξ0], hz, ?_⟩
  have ht0 (j : Fin m) : |heightParameter ν 0 j| < 2 := by
    simp only [heightParameter, map_zero, add_zero]
    have hh := hsmall j
    linarith [abs_nonneg (radialPhase (by omega) θ r j - midpoint m j)]
  have hp : ContDiffAt ℝ ∞ (fun t : ℝ => (sigmaPath s i t, ξ t)) 0 :=
    (sigmaPath_contDiff s i).contDiffAt.prodMk hξ
  have hjoint := radialConfiguration_sigma_contDiffAt (show 0 < m by omega)
    θ s ν r 0 a ht0
  have hjoint' : ContDiffAt ℝ ∞ (fun p : (Fin m → ℝ) × ℂ =>
      radialConfiguration (by omega) θ p.1 ν r p.2 a)
      (sigmaPath s i 0, ξ 0) := by
    simpa only [sigmaPath_zero, hξ0] using hjoint
  have hc : ContDiffAt ℝ ∞ (fun t =>
      radialConfiguration (by omega) θ (sigmaPath s i t) ν r (ξ t) a) 0 :=
    by simpa only [Function.comp_def] using hjoint'.comp 0 hp
  have hsnear : ∀ᶠ t in 𝓝 (0 : ℝ), s i * t ≤ 0 →
      ∀ j, |sigmaPath s i t j| ≤ 1 := by
    have he : ∀ᶠ t in 𝓝 (0 : ℝ), |t| < 1 :=
      continuousAt_id.abs.tendsto.eventually (eventually_lt_nhds (by norm_num))
    filter_upwards [he] with t ht hdir j
    by_cases hj : j = i
    · subst j
      simp only [sigmaPath, Function.update_self]
      rcases hi with hi | hi
      · rw [hi] at hdir ⊢
        have hb := abs_lt.mp ht
        rw [abs_le]
        constructor <;> nlinarith
      · rw [hi] at hdir ⊢
        have hb := abs_lt.mp ht
        rw [abs_le]
        constructor <;> nlinarith
    · simpa only [sigmaPath, Function.update_of_ne hj] using hs j
  have hh (j : Fin m) : ContinuousAt (fun t => heightParameter ν (ξ t) j) 0 := by
    unfold heightParameter
    fun_prop
  have hte : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ j, |heightParameter ν (ξ t) j| < 2 := by
    rw [Filter.eventually_all]
    intro j
    have hb : |heightParameter ν (ξ 0) j| < 2 := by simpa only [hξ0] using ht0 j
    exact (hh j).abs.tendsto.eventually (eventually_lt_nhds hb)
  have hwe : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ j,
      0 < Lens.width (radialLength (by omega) θ r j) (heightParameter ν (ξ t) j) := by
    rw [Filter.eventually_all]
    intro j
    have hcont : ContinuousAt (fun t =>
        Lens.width (radialLength (by omega) θ r j) (heightParameter ν (ξ t) j)) 0 := by
      unfold Lens.width Lens.height
      exact (continuousAt_const.sub ((hh j).pow 2)).sqrt.sub continuousAt_const
    have hb : 0 < Lens.width (radialLength (by omega) θ r j)
        (heightParameter ν (ξ 0) j) := by
      simpa only [hξ0, heightParameter, map_zero, add_zero] using hw j
    exact hcont.tendsto.eventually (eventually_gt_nhds hb)
  have hfe : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ (j : Fin (2 * m)) (k : Fin (2 * m)),
      k.val ≠ m - 1 → k.val ≠ m → k.val ≠ m + 1 →
      ‖crossingPath (by omega) θ s ν r a ξ i t (cyclicAdvance j k.val) -
        crossingPath (by omega) θ s ν r a ξ i t j‖ < 2 := by
    rw [Filter.eventually_all]
    intro j
    rw [Filter.eventually_all]
    intro k
    by_cases he : k.val ≠ m - 1 ∧ k.val ≠ m ∧ k.val ≠ m + 1
    · have h₁ := continuousAt_pi.mp hc.continuousAt (cyclicAdvance j k.val)
      have h₂ := continuousAt_pi.mp hc.continuousAt j
      have hb : ‖crossingPath (by omega) θ s ν r a ξ i 0 (cyclicAdvance j k.val) -
          crossingPath (by omega) θ s ν r a ξ i 0 j‖ < 2 := by
        simpa only [crossingPath, sigmaPath_zero, hξ0] using hfar j k he.1 he.2.1 he.2.2
      exact ((h₁.sub h₂).norm.tendsto.eventually (eventually_lt_nhds hb)).mono
        (fun _ h _ _ _ => h)
    · exact Eventually.of_forall (fun _ h₁ h₂ h₃ => False.elim (he ⟨h₁, h₂, h₃⟩))
  filter_upwards [hz, hsnear, hte, hwe, hfe] with t hz' hs' ht' hw' hfar'
  intro hdir
  have hs'' := hs' hdir
  have ht2 (j : Fin m) : heightParameter ν (ξ t) j ^ 2 ≤ 4 := by
    have hj := ht' j
    nlinarith [(abs_lt.mp hj).1, (abs_lt.mp hj).2]
  have hrabs (j : Fin m) : |r j| ≤ 1 := by rw [hr j]; norm_num
  have hd := diameter_of_nonlocal (show 0 < m by omega) θ (sigmaPath s i t) ν r (ξ t) a
    hθ hz' hs'' ht2 hw' hrabs hfar'
  refine ⟨hd, ?_⟩
  intro j
  change ‖radialConfiguration (by omega) θ (sigmaPath s i t) ν r (ξ t) a
      (halfTurn (by omega) j) -
    radialConfiguration (by omega) θ (sigmaPath s i t) ν r (ξ t) a j‖ = 2
  rw [matching_distance (show 0 < m by omega) θ (sigmaPath s i t) ν r (ξ t) a hθ hz']
  unfold radiusFull
  rw [hr]
  norm_num

end
end StructuralNote.MatchingActivityCrossingEndpointGraph
