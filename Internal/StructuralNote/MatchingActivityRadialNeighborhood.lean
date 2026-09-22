import StructuralNote.MatchingActivityRadialConstraints

/-! All distance constraints persist on the actual radial closure branch. -/

namespace StructuralNote.MatchingActivityRadialNeighborhood

open Erdos1045 Erdos1045.EventualExact Complex Configuration Filter
open LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open CommonClosureEnergy CommonFiberGeometry CommonTangentialParameters
open MatchingActivityRadialClosure MatchingActivityRadialGeometry MatchingActivityRadialIntegration
open MatchingActivityRadialConstraints
open scoped BigOperators Topology ContDiff
noncomputable section

theorem eventually_diameter {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (a : ℂ) (g : (Fin m → ℝ) → ℂ)
    (hθ : HalfPeriodic hm (fun j => (θ j : ℂ))) (hσ : ∀ j, |σ j| ≤ 1)
    (hg0 : g r = 0) (hg : ContDiffAt ℝ ∞ g r)
    (hz : ∀ᶠ r' in 𝓝 r, closureFamily (parameters hm θ σ ν r') (g r') = 0)
    (hpos : ∀ j, 0 < (MatchingActivityRadialPair.pair (halfAngle hm θ j) (r j) (r (nextIndex hm j))).re)
    (ht : ∀ j, |ν j| < 2) (hw : ∀ j, 0 < Lens.width (radialLength hm θ r j) (ν j))
    (hfar : ∀ (j : Fin (2 * m)) (k : Fin (2 * m)), k.val ≠ m - 1 → k.val ≠ m → k.val ≠ m + 1 →
      ‖radialConfiguration hm θ σ ν r 0 a (cyclicAdvance j k.val) - radialConfiguration hm θ σ ν r 0 a j‖ < 2) :
    ContDiffAt ℝ ∞ (fun r' => radialConfiguration hm θ σ ν r' (g r') a) r ∧
    (∀ᶠ r' in 𝓝 r, (∀ j, |r' j| ≤ 1) → DiameterAtMost 2 (radialConfiguration hm θ σ ν r' (g r') a)) := by
  have ht0 (j : Fin m) : |heightParameter ν (g r) j| < 2 := by
    simpa only [hg0, heightParameter, map_zero, add_zero] using ht j
  have hp : ContDiffAt ℝ ∞ (fun r' : Fin m → ℝ => (r', g r')) r := contDiffAt_id.prodMk hg
  have hf := (radialConfiguration_contDiffAt hm θ σ ν r (g r) a hpos ht0).comp r hp
  refine ⟨hf, ?_⟩
  have hd := parameters_contDiffAt hm θ σ ν r hpos
  have hh (j : Fin m) : ContinuousAt (fun r' => heightParameter ν (g r') j) r := by
    unfold heightParameter
    fun_prop
  have hte : ∀ᶠ r' in 𝓝 r, ∀ j, |heightParameter ν (g r') j| < 2 := by
    rw [Filter.eventually_all]
    intro j
    exact (hh j).abs.tendsto.eventually (eventually_lt_nhds (ht0 j))
  have hwe : ∀ᶠ r' in 𝓝 r, ∀ j, 0 < Lens.width (radialLength hm θ r' j) (heightParameter ν (g r') j) := by
    rw [Filter.eventually_all]
    intro j
    have hL := (contDiffAt_pi.mp hd.snd.fst j).continuousAt
    change ContinuousAt (fun r' : Fin m → ℝ => radialLength hm θ r' j) r at hL
    have hcont : ContinuousAt (fun r' => Lens.width (radialLength hm θ r' j) (heightParameter ν (g r') j)) r := by
      unfold Lens.width Lens.height
      exact (continuousAt_const.sub ((hh j).pow 2)).sqrt.sub hL
    have hb : 0 < Lens.width (radialLength hm θ r j) (heightParameter ν (g r) j) := by
      simpa only [hg0, heightParameter, map_zero, add_zero] using hw j
    exact hcont.tendsto.eventually (eventually_gt_nhds hb)
  have hfe : ∀ᶠ r' in 𝓝 r, ∀ (j : Fin (2 * m)) (k : Fin (2 * m)),
      k.val ≠ m - 1 → k.val ≠ m → k.val ≠ m + 1 →
        ‖radialConfiguration hm θ σ ν r' (g r') a (cyclicAdvance j k.val) - radialConfiguration hm θ σ ν r' (g r') a j‖ < 2 := by
    rw [Filter.eventually_all]
    intro j
    rw [Filter.eventually_all]
    intro k
    by_cases he : k.val ≠ m - 1 ∧ k.val ≠ m ∧ k.val ≠ m + 1
    · have h₁ := continuousAt_pi.mp hf.continuousAt (cyclicAdvance j k.val)
      have h₂ := continuousAt_pi.mp hf.continuousAt j
      have hb : ‖radialConfiguration hm θ σ ν r (g r) a (cyclicAdvance j k.val) - radialConfiguration hm θ σ ν r (g r) a j‖ < 2 := by
        rw [hg0]
        exact hfar j k he.1 he.2.1 he.2.2
      exact ((h₁.sub h₂).norm.tendsto.eventually (eventually_lt_nhds hb)).mono (fun _ h _ _ _ => h)
    · exact Eventually.of_forall (fun _ h₁ h₂ h₃ => False.elim (he ⟨h₁, h₂, h₃⟩))
  filter_upwards [hz, hte, hwe, hfe] with r' hz' ht' hw' hf' hr'
  apply diameter_of_nonlocal hm θ σ ν r' (g r') a hθ hz' hσ _ hw' hr' hf'
  intro j
  nlinarith [(abs_lt.mp (ht' j)).1, (abs_lt.mp (ht' j)).2]

end
end StructuralNote.MatchingActivityRadialNeighborhood
