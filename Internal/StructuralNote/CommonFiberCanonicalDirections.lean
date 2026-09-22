import StructuralNote.CommonDomainSegments
import StructuralNote.CommonFiberCanonicalObjective

/-! Every linear gauge direction stays in the strict common domain for a
neighborhood of the base point. -/

namespace StructuralNote.CommonFiberCanonicalDirections

open Erdos1045 Erdos1045.EventualExact Complex Filter
open SchurSpectrum FiniteFourierLift AngularObjectiveCurvature
open CommonTangentialParameters CommonDomainRadius CommonDomainClosure
open CommonFiberSmooth CommonFiberCanonical CommonFiberCanonicalPaths
open CommonFiberCanonicalObjective CommonDomainConvexity
open scoped BigOperators Topology ContDiff
noncomputable section

def Admissible {m : ℕ} (hm : 0 < m) (d : FreeParameters m) : Prop :=
  HalfPeriodic hm (fun j => (d.1 j : ℂ)) ∧ (∑ j, (d.1 j : ℂ)) = 0 ∧ ParameterSpace hm d.2

theorem energy_continuous {n : ℕ} (hn : 0 < n) : Continuous (pairEnergy hn) := by
  have he : pairEnergy hn = fun c : Fin n → ℂ =>
      (∑ i, ∑ j, normSq (c i - c j) /
        normSq (LocalPhase.regularRoot n ^ (i : ℕ) - LocalPhase.regularRoot n ^ (j : ℕ))) / 2 :=
    funext (pairEnergy_eq_chord_sum hn)
  rw [he]
  fun_prop

theorem admissible_affine {m : ℕ} (hm : 0 < m) (x d : FreeParameters m)
    (hx : Admissible hm x) (hd : Admissible hm d) (s : ℝ) :
    Admissible hm (affinePath x d s) := by
  have hθeq : (fun j => ((affinePath x d s).1 j : ℂ)) =
      fun j => (x.1 j : ℂ) + (s : ℂ) * (d.1 j : ℂ) := by
    funext j
    change ((x.1 j + s * d.1 j : ℝ) : ℂ) = _
    simp only [ofReal_add, ofReal_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [hθeq]
    intro j
    dsimp only
    have hxj : (x.1 (FourierMultiplier.halfTurn hm j) : ℂ) = x.1 j := hx.1 j
    have hdj : (d.1 (FourierMultiplier.halfTurn hm j) : ℂ) = d.1 j := hd.1 j
    rw [hxj, hdj]
  · rw [hθeq, Finset.sum_add_distrib, ← Finset.mul_sum, hx.2.1, hd.2.1, mul_zero, add_zero]
  · have hp := parameterSpace_linear hm x.2 d.2 hx.2.2 hd.2.2 1 s
    have he : (fun j => ((1 : ℝ) : ℂ) * x.2 j + (s : ℂ) * d.2 j) = (affinePath x d s).2 := by
      funext j
      change ((1 : ℝ) : ℂ) * x.2 j + (s : ℂ) * d.2 j = x.2 j + s • d.2 j
      simp only [ofReal_one, one_mul, real_smul]
    rwa [he] at hp

theorem affine_domain_near_zero {m : ℕ} (hm : 0 < m) (x d : FreeParameters m)
    (hx : x ∈ domain hm) (hd : Admissible hm d) :
    ∀ᶠ s in 𝓝 (0 : ℝ), affinePath x d s ∈ domain hm := by
  have hc : Continuous (fun s : ℝ =>
      pairEnergy (by omega : 0 < 2 * m) (fun j => ((affinePath x d s).1 j : ℂ)) +
      pairEnergy (by omega : 0 < 2 * m) (affinePath x d s).2) := by
    apply Continuous.add
    · apply (energy_continuous (by omega)).comp
      unfold affinePath
      fun_prop
    · apply (energy_continuous (by omega)).comp
      exact (affinePath_contDiff x d).continuous.snd
  have hlt : (fun s : ℝ =>
      pairEnergy (by omega : 0 < 2 * m) (fun j => ((affinePath x d s).1 j : ℂ)) +
      pairEnergy (by omega : 0 < 2 * m) (affinePath x d s).2) 0 < energyRadius (2 * m) := by
    simpa only [affinePath, zero_smul, add_zero] using hx.2.2.2
  filter_upwards [hc.continuousAt.eventually (gt_mem_nhds hlt)] with s hs
  have hp := admissible_affine hm x d ⟨hx.1, hx.2.1, hx.2.2.1⟩ hd s
  exact ⟨hp.1, hp.2.1, hp.2.2, hs⟩

theorem eventual_direction_contDiffAt : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (σ : Fin m → ℝ) (x d : FreeParameters m),
    (∀ j, |σ j| ≤ 1) → x ∈ domain hm → Admissible hm d →
    ContDiffAt ℝ ∞ (fun s => logProduct hm σ (affinePath x d s)) 0 := by
  filter_upwards [eventual_logProduct_contDiffWithinAt] with m hsmooth
  intro hm σ x d hσ hx hd
  let S : Set ℝ := (affinePath x d) ⁻¹' domain hm
  have hdom : S ∈ 𝓝 (0 : ℝ) := affine_domain_near_zero hm x d hx hd
  have hx' : affinePath x d 0 ∈ domain hm := by simpa only [affinePath, zero_smul, add_zero] using hx
  have hf := hsmooth hm σ (affinePath x d 0) hσ hx'
  have hp := (affinePath_contDiff x d).contDiffAt.contDiffWithinAt (s := S) (x := (0 : ℝ))
  exact (hf.comp 0 hp (fun _ h => h)).contDiffAt hdom

end
end StructuralNote.CommonFiberCanonicalDirections
