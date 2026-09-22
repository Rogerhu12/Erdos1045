import StructuralNote.MatchingActivityRadialPath
import StructuralNote.ClosedSourceIntegration

/-! The derivative of the actual outward radial path, with its implicit
closure correction retained. -/

namespace StructuralNote.MatchingActivityRadialVelocity

open Erdos1045 Erdos1045.EventualExact Complex Configuration Filter
open LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open CommonClosureEnergy CommonFiberGeometry MatchingActivityRadialClosure
open MatchingActivityRadialGeometry MatchingActivityRadialIntegration MatchingActivityRadialConstraints
open MatchingActivityRadialFeasible MatchingActivityRadialPath MatchingActivityRadialPair
open LensIncrementDerivatives LensClosurePathDerivatives ClosedSourceIntegration
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 400000

def radiusVelocity {m : ℕ} (i j : Fin m) : ℝ := if j = i then 1 else 0

theorem radiusPath_hasDerivAt {m : ℕ} (r : Fin m → ℝ) (i j : Fin m) :
    HasDerivAt (fun t => radiusPath r i t j) (radiusVelocity i j) 0 := by
  by_cases hj : j = i
  · subst j
    simp only [radiusPath, Function.update_self, radiusVelocity, if_true]
    exact (hasDerivAt_id 0).const_add (r i)
  · simp only [radiusPath, Function.update_of_ne hj, radiusVelocity, if_neg hj]
    exact hasDerivAt_const 0 _

def pairVelocity {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (i j : Fin m) : ℂ :=
  pair (halfAngle hm θ j) (radiusVelocity i j) (radiusVelocity i (nextIndex hm j))

def phaseVelocity {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (r : Fin m → ℝ) (i j : Fin m) : ℝ :=
  (pairVelocity hm θ i j / pair (halfAngle hm θ j) (r j) (r (nextIndex hm j))).im

def lengthVelocity {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (r : Fin m → ℝ) (i j : Fin m) : ℝ :=
  radialLength hm θ r j * (pairVelocity hm θ i j / pair (halfAngle hm θ j) (r j) (r (nextIndex hm j))).re

theorem radialPhase_hasDerivAt {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (r : Fin m → ℝ) (i j : Fin m)
    (hpos : 0 < (pair (halfAngle hm θ j) (r j) (r (nextIndex hm j))).re) :
    HasDerivAt (fun t => radialPhase hm θ (radiusPath r i t) j) (phaseVelocity hm θ r i j) 0 := by
  have hp : 0 < (pair (halfAngle hm θ j) (radiusPath r i 0 j) (radiusPath r i 0 (nextIndex hm j))).re := by
    simpa only [radiusPath_zero] using hpos
  have hd := (direction_path_hasDerivAt (halfAngle hm θ j) (radiusPath_hasDerivAt r i j)
    (radiusPath_hasDerivAt r i (nextIndex hm j)) hp).const_add (phase hm θ j)
  simpa only [radialPhase, phaseVelocity, pairVelocity, radiusPath_zero] using hd

theorem radialLength_hasDerivAt {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (r : Fin m → ℝ) (i j : Fin m)
    (hpos : 0 < (pair (halfAngle hm θ j) (r j) (r (nextIndex hm j))).re) :
    HasDerivAt (fun t => radialLength hm θ (radiusPath r i t) j) (lengthVelocity hm θ r i j) 0 := by
  have hp : 0 < (pair (halfAngle hm θ j) (radiusPath r i 0 j) (radiusPath r i 0 (nextIndex hm j))).re := by
    simpa only [radiusPath_zero] using hpos
  have hd := length_path_hasDerivAt (halfAngle hm θ j) (radiusPath_hasDerivAt r i j)
    (radiusPath_hasDerivAt r i (nextIndex hm j)) hp
  simpa only [radialLength, lengthVelocity, pairVelocity, radiusPath_zero] using hd

def directSource {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (i j : Fin m) : ℂ :=
  incrementVelocity (radialPhase hm θ r j) (radialLength hm θ r j) (σ j) (ν j)
    (phaseVelocity hm θ r i j) (lengthVelocity hm θ r i j) 0

def closureSpeed {m : ℕ} (r : Fin m → ℝ) (g : (Fin m → ℝ) → ℂ) (i : Fin m) : ℂ :=
  deriv (fun t => g (radiusPath r i t)) 0

theorem closureSpeed_hasDerivAt {m : ℕ} (r : Fin m → ℝ) (g : (Fin m → ℝ) → ℂ) (i : Fin m)
    (hg : ContDiffAt ℝ ∞ g r) :
    HasDerivAt (fun t => g (radiusPath r i t)) (closureSpeed r g i) 0 := by
  have hg' : ContDiffAt ℝ ∞ g (radiusPath r i 0) := by simpa only [radiusPath_zero] using hg
  exact ((hg'.comp 0 (radiusPath_contDiff r i).contDiffAt).differentiableAt (by norm_num)).hasDerivAt

theorem actual_closure_derivative {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (a : ℂ) (g : (Fin m → ℝ) → ℂ) (i : Fin m)
    (hchart : IsFeasibleRadialChart hm θ σ ν r a g)
    (hpos : ∀ j, 0 < (pair (halfAngle hm θ j) (r j) (r (nextIndex hm j))).re)
    (ht : ∀ j, ν j ^ 2 < 4) :
    closureDerivative (radialPhase hm θ r) σ ν 0 (closureSpeed r g i) = -∑ j, directSource hm θ σ ν r i j := by
  have hξ := closureSpeed_hasDerivAt r g i hchart.2.2.1
  have ht' (j : Fin m) : heightParameter ν (g (radiusPath r i 0)) j ^ 2 < 4 := by
    simpa only [radiusPath_zero, hchart.2.1, heightParameter, map_zero, add_zero] using ht j
  have hz : ∀ᶠ t in 𝓝 (0 : ℝ), closure (radialPhase hm θ (radiusPath r i t))
      (radialLength hm θ (radiusPath r i t)) σ ν (g (radiusPath r i t)) = 0 := by
    have hnear : Tendsto (radiusPath r i) (𝓝 0) (𝓝 r) := by
      simpa only [radiusPath_zero] using (radiusPath_contDiff r i).continuous.continuousAt.tendsto (x := 0)
    exact hnear.eventually hchart.2.2.2.1
  have he := closure_path_derivative_eq σ (phaseVelocity hm θ r i) (lengthVelocity hm θ r i) (fun _ => 0)
    (fun j => radialPhase_hasDerivAt hm θ r i j (hpos j)) (fun j => radialLength_hasDerivAt hm θ r i j (hpos j))
    (fun j => hasDerivAt_const 0 (ν j)) hξ ht' hz
  simpa only [radiusPath_zero, hchart.2.1, heightParameter, map_zero, add_zero, directSource] using he

def centerVelocity {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (g : (Fin m → ℝ) → ℂ) (i : Fin m) : Fin (2 * m) → ℂ :=
  integrateCorrected hm (radialPhase hm θ r) σ ν 0 (closureSpeed r g i) (directSource hm θ σ ν r i)

theorem radialCenter_hasDerivAt {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (a : ℂ) (g : (Fin m → ℝ) → ℂ) (i : Fin m)
    (hchart : IsFeasibleRadialChart hm θ σ ν r a g)
    (hpos : ∀ j, 0 < (pair (halfAngle hm θ j) (r j) (r (nextIndex hm j))).re)
    (ht : ∀ j, ν j ^ 2 < 4) (j : Fin (2 * m)) :
    HasDerivAt (fun t => radialCenter hm θ σ ν (radiusPath r i t) (g (radiusPath r i t)) j)
      (centerVelocity hm θ σ ν r g i j) 0 := by
  have hξ := closureSpeed_hasDerivAt r g i hchart.2.2.1
  have hd (k : Fin m) : HasDerivAt (fun t => radialIncrement hm θ σ ν (radiusPath r i t) (g (radiusPath r i t)) k)
      (corrected (radialPhase hm θ r) σ ν 0 (closureSpeed r g i) (directSource hm θ σ ν r i) k) 0 := by
    have ht' : heightParameter ν (g (radiusPath r i 0)) k ^ 2 < 4 := by
      simpa only [radiusPath_zero, hchart.2.1, heightParameter, map_zero, add_zero] using ht k
    have he := increment_hasDerivAt (σ k) (radialPhase_hasDerivAt hm θ r i k (hpos k))
      (radialLength_hasDerivAt hm θ r i k (hpos k))
      (heightParameter_hasDerivAt (ν := fun _ : ℝ => ν) (ν' := fun _ => 0)
        (fun j => hasDerivAt_const 0 (ν j)) hξ k) ht'
    apply he.congr_deriv
    simp only [radiusPath_zero, hchart.2.1, heightParameter, map_zero, add_zero, zero_add, corrected, directSource]
    simpa only [zero_add] using velocity_split (radialPhase hm θ r k) (radialLength hm θ r k)
      (σ k) (ν k) (phaseVelocity hm θ r i k) (lengthVelocity hm θ r i k) 0
      (harmonicFunctional (midpoint m k) (closureSpeed r g i))
  exact integral_hasDerivAt (repeatHalf_hasDerivAt hm hd) j

theorem closureSpeed_bound {m : ℕ} (hm : 2 ≤ m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (a : ℂ) (g : (Fin m → ℝ) → ℂ) (i : Fin m)
    (hchart : IsFeasibleRadialChart (by omega) θ σ ν r a g)
    (hpos : ∀ j, 0 < (pair (halfAngle (by omega) θ j) (r j) (r (nextIndex (by omega) j))).re)
    (hsmall : ∀ j, |radialPhase (by omega) θ r j - midpoint m j| + |ν j| ≤ 1 / 4) :
    ‖closureSpeed r g i‖ ≤ (4 / m : ℝ) * ∑ j, ‖directSource (by omega) θ σ ν r i j‖ := by
  have ht (j : Fin m) : ν j ^ 2 < 4 := by
    have hh := hsmall j
    have ha := abs_le.mp (show |ν j| ≤ 1 / 4 by linarith [abs_nonneg (radialPhase (by omega) θ r j - midpoint m j)])
    nlinarith
  apply correction_bound hm _ _ _ _ _ _ hchart.1 _ (actual_closure_derivative (by omega) θ σ ν r a g i hchart hpos ht)
  intro j
  simpa only [heightParameter, map_zero, add_zero] using hsmall j

end
end StructuralNote.MatchingActivityRadialVelocity
