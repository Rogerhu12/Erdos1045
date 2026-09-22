import StructuralNote.MatchingActivityRadialActual

/-! Integration of the unsaturated radial increments and exact recovery of
the original center, including its translation. -/

namespace StructuralNote.MatchingActivityRadialIntegration

open Erdos1045 Erdos1045.EventualExact Complex Configuration Filter
open LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open CommonClosureEnergy CommonFiberGeometry CommonTangentialParameters BoxLensLift
open MatchingActivityRadialClosure MatchingActivityRadialGeometry
open scoped BigOperators Topology ContDiff
noncomputable section

theorem radialCenter_difference {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (ξ : ℂ)
    (hz : closureFamily (parameters hm θ σ ν r) ξ = 0) :
    difference (by omega) (radialCenter hm θ σ ν r ξ) =
      BoxLensLift.repeatHalf hm (radialIncrement hm θ σ ν r ξ) := by
  apply difference_integral
  rw [BoxLensLift.repeatHalf_sum]
  change (2 : ℂ) * closureFamily (parameters hm θ σ ν r) ξ = 0
  rw [hz, mul_zero]

theorem radialCenter_halfPeriodic {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (ξ : ℂ)
    (hz : closureFamily (parameters hm θ σ ν r) ξ = 0) :
    HalfPeriodic hm (radialCenter hm θ σ ν r ξ) := by
  have he : (fun j => radialCenter hm θ σ ν r ξ (halfTurn hm j)) = radialCenter hm θ σ ν r ξ := by
    apply integral_unique (by omega)
    · have hs := Equiv.sum_comp (Equiv.ofBijective (halfTurn hm) (halfTurn_involutive hm).bijective)
        (radialCenter hm θ σ ν r ξ)
      exact hs.trans (integral_mean_zero (by omega) _)
    · funext j
      change radialCenter hm θ σ ν r ξ (halfTurn hm (successor _ j)) -
        radialCenter hm θ σ ν r ξ (halfTurn hm j) = _
      rw [halfTurn_successor]
      change difference (by omega) (radialCenter hm θ σ ν r ξ) (halfTurn hm j) = _
      rw [radialCenter_difference hm θ σ ν r ξ hz]
      exact BoxLensLift.repeatHalf_halfTurn hm _ j
  exact fun j => congrFun he j

def average {n : ℕ} (c : Fin n → ℂ) : ℂ := (∑ j, c j) / (n : ℂ)

theorem sub_average_sum {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) :
    (∑ j, (c j - average c)) = 0 := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, average, mul_div_cancel₀ _ hn0, sub_self]

theorem radialCenter_base {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (c : Fin (2 * m) → ℂ) (hc : HalfPeriodic hm c)
    (hi : ∀ j, difference (by omega) c (CommonClosureEnergy.halfIndex j) = radialIncrement hm θ σ ν r 0 j) :
    ∀ j, radialCenter hm θ σ ν r 0 j + average c = c j := by
  have hd : difference (by omega) (fun j => c j - average c) =
      BoxLensLift.repeatHalf hm (radialIncrement hm θ σ ν r 0) := by
    funext j
    have hh : difference (by omega) (fun j => c j - average c) j = difference (by omega) c j := by
      unfold difference
      ring
    rw [hh]
    obtain ⟨k, hj | hj⟩ := half_decomposition hm j
    · rw [hj, repeatHalf_halfIndex]
      exact hi k
    · rw [hj, difference_halfPeriodic hm c hc, BoxLensLift.repeatHalf_halfTurn,
        repeatHalf_halfIndex]
      exact hi k
  have he := integral_unique (by omega : 0 < 2 * m)
    (BoxLensLift.repeatHalf hm (radialIncrement hm θ σ ν r 0))
    (fun j => c j - average c) (sub_average_sum (by omega) c) hd
  intro j
  have hh := congrFun he j
  change c j - average c = radialCenter hm θ σ ν r 0 j at hh
  rw [← hh]
  ring

def radialConfiguration {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (ξ a : ℂ) (j : Fin (2 * m)) : ℂ :=
  vertices hm θ r (radialCenter hm θ σ ν r ξ) j + a

theorem radialConfiguration_base {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (c : Fin (2 * m) → ℂ) (hc : HalfPeriodic hm c)
    (hi : ∀ j, difference (by omega) c (CommonClosureEnergy.halfIndex j) = radialIncrement hm θ σ ν r 0 j) :
    radialConfiguration hm θ σ ν r 0 (average c) = vertices hm θ r c := by
  funext j
  dsimp only [radialConfiguration, vertices]
  rw [add_assoc, radialCenter_base hm θ σ ν r c hc hi]

theorem radialConfiguration_contDiffAt {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (ξ a : ℂ)
    (hpos : ∀ j, 0 < (MatchingActivityRadialPair.pair (halfAngle hm θ j) (r j) (r (nextIndex hm j))).re)
    (ht : ∀ j, |heightParameter ν ξ j| < 2) :
    ContDiffAt ℝ ∞ (fun p : (Fin m → ℝ) × ℂ => radialConfiguration hm θ σ ν p.1 p.2 a) (r, ξ) := by
  have hc := radialCenter_contDiffAt hm θ σ ν r ξ hpos ht
  have hcast : ContDiff ℝ ∞ (Complex.ofReal : ℝ → ℂ) := Complex.ofRealCLM.contDiff
  apply contDiffAt_pi.mpr
  intro j
  have hcj := contDiffAt_pi.mp hc j
  unfold radialConfiguration vertices radiusFull
  fun_prop

end
end StructuralNote.MatchingActivityRadialIntegration
