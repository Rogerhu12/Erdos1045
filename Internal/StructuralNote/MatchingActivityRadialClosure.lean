import StructuralNote.MatchingActivityRadialBounds
import StructuralNote.CommonFiberSmooth

/-! A smooth closed lens family with independently variable matching radii.
The original tangential heights are fixed; no orthogonal splitting is needed. -/

namespace StructuralNote.MatchingActivityRadialClosure

open Erdos1045 Erdos1045.EventualExact Complex LensClosure Filter
open CommonClosureEnergy CommonFiberSmooth MatchingActivityRadialPair
open scoped BigOperators Topology ContDiff
noncomputable section

def nextIndex {m : ℕ} (hm : 0 < m) (j : Fin m) : Fin m :=
  ⟨(j.val + 1) % m, Nat.mod_lt _ hm⟩

def radialPhase {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (r : Fin m → ℝ) (j : Fin m) : ℝ :=
  phase hm θ j + direction (halfAngle hm θ j) (r j) (r (nextIndex hm j))

def radialLength {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (r : Fin m → ℝ) (j : Fin m) : ℝ :=
  length (halfAngle hm θ j) (r j) (r (nextIndex hm j))

def parameters {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (σ ν r : Fin m → ℝ) : Parameters m :=
  (radialPhase hm θ r, radialLength hm θ r, σ, ν)

theorem parameters_contDiffAt {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ)
    (hpos : ∀ j, 0 < (pair (halfAngle hm θ j) (r j) (r (nextIndex hm j))).re) :
    ContDiffAt ℝ ∞ (parameters hm θ σ ν) r := by
  have hc (j : Fin m) : ContDiff ℝ ∞ (fun r : Fin m → ℝ => (r j, r (nextIndex hm j))) := by fun_prop
  have hα : ContDiffAt ℝ ∞ (radialPhase hm θ) r := by
    apply contDiffAt_pi.mpr
    intro j
    have hh : ContDiffAt ℝ ∞ (fun r' : Fin m → ℝ => direction (halfAngle hm θ j) (r' j) (r' (nextIndex hm j))) r := by
      exact ContDiffAt.comp (f := fun r' : Fin m → ℝ => (r' j, r' (nextIndex hm j)))
        (g := fun p : ℝ × ℝ => direction (halfAngle hm θ j) p.1 p.2) r
        (direction_contDiffAt (halfAngle hm θ j) (r j, r (nextIndex hm j)) (hpos j)) (hc j).contDiffAt
    exact contDiffAt_const.add hh
  have hL : ContDiffAt ℝ ∞ (radialLength hm θ) r := by
    apply contDiffAt_pi.mpr
    intro j
    change ContDiffAt ℝ ∞ (fun r' : Fin m → ℝ => length (halfAngle hm θ j) (r' j) (r' (nextIndex hm j))) r
    exact ContDiffAt.comp (f := fun r' : Fin m → ℝ => (r' j, r' (nextIndex hm j)))
      (g := fun p : ℝ × ℝ => length (halfAngle hm θ j) p.1 p.2) r
      (length_contDiffAt (halfAngle hm θ j) (r j, r (nextIndex hm j)) (hpos j)) (hc j).contDiffAt
  exact hα.prodMk (hL.prodMk (contDiffAt_const.prodMk contDiffAt_const))

/-- All matching radii are independent local parameters of the exact closure
equation, including at a base point where some are less than one. -/
theorem exists_smooth_radial_root {m : ℕ} (hm : 2 ≤ m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (hσ : ∀ j, |σ j| ≤ 1)
    (hpos : ∀ j, 0 < (pair (halfAngle (by omega) θ j) (r j) (r (nextIndex (by omega) j))).re)
    (hsmall : ∀ j, |radialPhase (by omega) θ r j - midpoint m j| + |ν j| ≤ 1 / 4)
    (hzero : closureFamily (parameters (by omega) θ σ ν r) 0 = 0) :
    ∃ g : (Fin m → ℝ) → ℂ, g r = 0 ∧ ContDiffAt ℝ ∞ g r ∧
      (∀ᶠ r' in 𝓝 r, closureFamily (parameters (by omega) θ σ ν r') (g r') = 0) := by
  have hs (j : Fin m) : |(parameters (by omega) θ σ ν r).1 j - midpoint m j| +
      |heightParameter (parameters (by omega) θ σ ν r).2.2.2 0 j| ≤ 1 / 4 := by
    simpa only [parameters, heightParameter, map_zero, add_zero] using hsmall j
  obtain ⟨g, hgr, hg, hge, _⟩ := exists_smooth_closure_root hm
    (parameters (by omega) θ σ ν r) 0 hσ hs hzero
  have hd := parameters_contDiffAt (by omega) θ σ ν r hpos
  refine ⟨fun r' => g (parameters (by omega) θ σ ν r'), hgr, hg.comp r hd, ?_⟩
  exact hd.continuousAt.eventually hge

def radialIncrement {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (ξ : ℂ) (j : Fin m) : ℂ :=
  increment (radialPhase hm θ r j) (radialLength hm θ r j) (σ j) (heightParameter ν ξ j)

def radialCenter {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (ξ : ℂ) : Fin (2 * m) → ℂ :=
  FiniteFourierLift.integral (BoxLensLift.repeatHalf hm (radialIncrement hm θ σ ν r ξ))

theorem radialCenter_contDiffAt {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (ξ : ℂ)
    (hpos : ∀ j, 0 < (pair (halfAngle hm θ j) (r j) (r (nextIndex hm j))).re)
    (ht : ∀ j, |heightParameter ν ξ j| < 2) :
    ContDiffAt ℝ ∞ (fun p : (Fin m → ℝ) × ℂ => radialCenter hm θ σ ν p.1 p.2) (r, ξ) := by
  have hp := parameters_contDiffAt hm θ σ ν r hpos
  have hdata : ContDiffAt ℝ ∞ (fun p : (Fin m → ℝ) × ℂ => (parameters hm θ σ ν p.1, p.2)) (r, ξ) :=
    (hp.comp (r, ξ) contDiffAt_fst).prodMk contDiffAt_snd
  have hinc (j : Fin m) : ContDiffAt ℝ ∞
      (fun p : (Fin m → ℝ) × ℂ => radialIncrement hm θ σ ν p.1 p.2 j) (r, ξ) := by
    have ht' : ContDiffAt ℝ ∞ (fun p : (Fin m → ℝ) × ℂ => heightParameter ν p.2 j) (r, ξ) := by
      unfold heightParameter
      fun_prop
    have hh : ContDiffAt ℝ ∞ (fun p : (Fin m → ℝ) × ℂ => Lens.height (heightParameter ν p.2 j)) (r, ξ) := by
      unfold Lens.height
      exact (contDiffAt_const.sub (ht'.pow 2)).sqrt (by
        have hx := ht j
        have hsq : heightParameter ν ξ j ^ 2 < 4 := by nlinarith [(abs_lt.mp hx).1, (abs_lt.mp hx).2]
        dsimp
        linarith)
    have hpar : ContDiffAt ℝ ∞ (fun p : (Fin m → ℝ) × ℂ => parameters hm θ σ ν p.1) (r, ξ) :=
      hp.comp (r, ξ) contDiffAt_fst
    have hα := contDiffAt_pi.mp hpar.fst j
    have hL := contDiffAt_pi.mp hpar.snd.fst j
    change ContDiffAt ℝ ∞ (fun p : (Fin m → ℝ) × ℂ => radialPhase hm θ p.1 j) (r, ξ) at hα
    change ContDiffAt ℝ ∞ (fun p : (Fin m → ℝ) × ℂ => radialLength hm θ p.1 j) (r, ξ) at hL
    have hcast : ContDiff ℝ ∞ (Complex.ofReal : ℝ → ℂ) := Complex.ofRealCLM.contDiff
    unfold radialIncrement increment unit Lens.width
    fun_prop
  have hr : ContDiffAt ℝ ∞ (fun p : (Fin m → ℝ) × ℂ =>
      BoxLensLift.repeatHalf hm (radialIncrement hm θ σ ν p.1 p.2)) (r, ξ) := by
    apply contDiffAt_pi.mpr
    intro j
    exact hinc ⟨j.val % m, Nat.mod_lt _ hm⟩
  exact (integral_contDiff (2 * m)).contDiffAt.comp (r, ξ) hr

end
end StructuralNote.MatchingActivityRadialClosure
