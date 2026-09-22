import StructuralNote.CommonFiberNonlocalChain
import StructuralNote.CommonFiberNonlocalSizes

/-! Every point of the literal common domain has all diameter constraints.
Nonlocal constraints are strict; adjacent constraints retain their exact signs. -/

namespace StructuralNote.CommonFiberNonlocalFeasibility

open Erdos1045 Erdos1045.EventualExact Complex
open LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open CommonClosureEnergy CommonTangentialParameters CommonDomainClosure
open CommonFiberGeometry CommonFiberNonlocalFrames CommonFiberNonlocalProjection
open CommonFiberNonlocalChain CommonFiberAdjacent
noncomputable section

theorem periodize_diameter_half {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (hθ : HalfPeriodic hm (fun j => (θ j : ℂ))) (j : ℕ) :
    periodize (by omega) (diameterVector θ) (j + m) = -periodize (by omega) (diameterVector θ) j := by
  have he : (⟨(j + m) % (2 * m), Nat.mod_lt _ (by omega)⟩ : Fin (2 * m)) =
      halfTurn hm ⟨j % (2 * m), Nat.mod_lt _ (by omega)⟩ := by
    apply Fin.ext
    simp only [halfTurn, Nat.mod_add_mod]
  change diameterVector θ ⟨(j + m) % (2 * m), _⟩ = _
  rw [he, diameterVector_halfTurn hm θ hθ]
  rfl

theorem forward_strict {m k : ℕ} (hm : 8 ≤ m) (hk : 2 ≤ k) (hkm : k ≤ m)
    (θ : Fin (2 * m) → ℝ) (c : Fin (2 * m) → ℂ)
    (hhalf : HalfPeriodic (by omega) (fun j => (θ j : ℂ))) (hc : HalfPeriodic (by omega) c)
    (hθ : ∀ i, |θ i| ≤ 1 / (1000 * (2 * m : ℝ)))
    (hstep : ∀ i, ‖difference (by omega) c i‖ ≤ 1 / (1000 * (2 * m : ℝ)))
    (hrad : ∀ i, |radial (meanFrame (by omega) θ i) (difference (by omega) c i)| ≤ 10 / (2 * m : ℝ) ^ 2)
    (j : Fin (2 * m)) :
    ‖(diameterVector θ (cyclicAdvance j (m + k)) + c (cyclicAdvance j (m + k))) -
      (diameterVector θ j + c j)‖ < 2 := by
  have hs (i : Fin (2 * m)) : ‖difference (by omega) (fun i => -c i) i‖ ≤ 1 / (1000 * (2 * m : ℝ)) := by
    simpa only [difference, neg_sub_neg, norm_sub_rev] using hstep i
  have hr (i : Fin (2 * m)) : |radial (meanFrame (by omega) θ i)
      (difference (by omega) (fun i => -c i) i)| ≤ 10 / (2 * m : ℝ) ^ 2 := by
    have he : difference (by omega) (fun i => -c i) i = -difference (by omega) c i := by unfold difference; ring
    simpa only [he, radial, mul_neg, Complex.neg_re, abs_neg] using hrad i
  have hb := chain_pair_strict (by omega : 16 ≤ 2 * m) hk (by omega) θ (fun i => -c i)
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hθ)
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hs)
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hr) j.val
  have hp := AntipodalLog.periodize_half_periodic (by omega) c hc
  change ‖(periodize (by omega) (diameterVector θ) (j.val + (m + k)) +
      periodize (by omega) c (j.val + (m + k))) - (diameterVector θ j + c j)‖ < 2
  rw [show j.val + (m + k) = (j.val + k) + m by omega,
    periodize_diameter_half (by omega) θ hhalf, hp]
  have he : -periodize (by omega) (diameterVector θ) (j.val + k) + periodize (by omega) c (j.val + k) -
      (diameterVector θ j + c j) =
      -(periodize (by omega) (diameterVector θ) j.val + periodize (by omega) (diameterVector θ) (j.val + k) +
        (periodize (by omega) (fun i => -c i) (j.val + k) - periodize (by omega) (fun i => -c i) j.val)) := by
    simp only [periodize_fin]
    change -periodize (by omega) (diameterVector θ) (j.val + k) + periodize (by omega) c (j.val + k) -
      (diameterVector θ j + c j) = -(diameterVector θ j + periodize (by omega) (diameterVector θ) (j.val + k) +
        (-periodize (by omega) c (j.val + k) - -c j))
    ring
  rw [he, norm_neg]
  exact hb

theorem adjacent_next {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ)
    (ha : AdjacentGeometry hm θ v σ ξ) (j : Fin (2 * m)) :
    ‖configuration hm θ v σ ξ (cyclicAdvance j (m + 1)) - configuration hm θ v σ ξ j‖ ≤ 2 := by
  have he : cyclicAdvance j (m + 1) = halfTurn hm (successor (by omega) j) := by
    apply Fin.ext
    simp only [cyclicAdvance, halfTurn, successor, Nat.mod_add_mod]
    congr 1
    omega
  rw [he, norm_sub_rev]
  obtain ⟨k, hj | hj⟩ := half_decomposition hm j
  · rw [hj]
    exact (ha.2 k).2.1
  · rw [hj, ← halfTurn_successor, halfTurn_involutive hm]
    have he : configuration hm θ v σ ξ (halfTurn hm (BoxLensLift.halfIndex k)) -
        configuration hm θ v σ ξ (successor (by omega) (BoxLensLift.halfIndex k)) =
        -(configuration hm θ v σ ξ (successor (by omega) (BoxLensLift.halfIndex k)) -
          configuration hm θ v σ ξ (halfTurn hm (BoxLensLift.halfIndex k))) := by ring
    rw [he, norm_neg]
    exact (ha.2 k).1

theorem offset_bound {m r : ℕ} (hm : 8 ≤ m) (hr : r < 2 * m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ)
    (hhalf : HalfPeriodic (by omega) (fun j => (θ j : ℂ)))
    (hz : closure (phase (by omega) θ) (fun j => 2 * Real.cos (halfAngle (by omega) θ j)) σ (coordinates (by omega) v) ξ = 0)
    (ha : AdjacentGeometry (by omega) θ v σ ξ)
    (hθ : ∀ i, |θ i| ≤ 1 / (1000 * (2 * m : ℝ)))
    (hstep : ∀ i, ‖difference (by omega) (center (by omega) θ v σ ξ) i‖ ≤ 1 / (1000 * (2 * m : ℝ)))
    (hrad : ∀ i, |radial (meanFrame (by omega) θ i) (difference (by omega) (center (by omega) θ v σ ξ) i)| ≤ 10 / (2 * m : ℝ) ^ 2)
    (j : Fin (2 * m)) :
    ‖configuration (by omega) θ v σ ξ (cyclicAdvance j r) - configuration (by omega) θ v σ ξ j‖ ≤ 2 := by
  by_cases hprev : r = m - 1
  · subst r
    have hh := adjacent_next (by omega) θ v σ ξ ha (cyclicAdvance j (m - 1))
    rwa [NonlocalFeasibility.advance_back_forward (by omega : 1 ≤ m), norm_sub_rev] at hh
  by_cases hmatch : r = m
  · subst r
    change ‖configuration (by omega) θ v σ ξ (halfTurn (by omega) j) - configuration (by omega) θ v σ ξ j‖ ≤ 2
    rw [norm_sub_rev, ha.1 j]
  by_cases hnext : r = m + 1
  · subst r
    exact adjacent_next (by omega) θ v σ ξ ha j
  have hc := center_halfPeriodic (by omega) θ v σ ξ hz
  by_cases hrm : r ≤ m
  · have hh := forward_strict hm (show 2 ≤ m - r by omega) (show m - r ≤ m by omega)
      θ (center (by omega) θ v σ ξ) hhalf hc hθ hstep hrad (cyclicAdvance j (m - (m - r)))
    change ‖configuration (by omega) θ v σ ξ (cyclicAdvance (cyclicAdvance j (m - (m - r))) (m + (m - r))) -
      configuration (by omega) θ v σ ξ (cyclicAdvance j (m - (m - r)))‖ < 2 at hh
    rw [NonlocalFeasibility.advance_back_forward (show m - r ≤ m by omega), Nat.sub_sub_self hrm, norm_sub_rev] at hh
    exact hh.le
  · have hh := forward_strict hm (show 2 ≤ r - m by omega) (show r - m ≤ m by omega)
      θ (center (by omega) θ v σ ξ) hhalf hc hθ hstep hrad j
    change ‖configuration (by omega) θ v σ ξ (cyclicAdvance j (m + (r - m))) - configuration (by omega) θ v σ ξ j‖ < 2 at hh
    rw [Nat.add_sub_of_le (show m ≤ r by omega)] at hh
    exact hh.le

theorem cyclicAdvance_forwardDistance {n : ℕ} (i j : Fin n) :
    cyclicAdvance i (cyclicForwardDistance i j) = j := by
  apply Fin.ext
  simp only [cyclicAdvance, cyclicForwardDistance, Nat.add_mod_mod]
  rw [show i.val + (j.val + n - i.val) = j.val + n by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]

/-- All pair constraints follow from the actual common domain. The only root
input is the small closed root already supplied by the closure theorem. -/
theorem eventual_actual_diameter : ∃ N : ℕ, ∀ (m : ℕ) (hm : N + 128 ≤ m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ),
    InDomain (by omega) θ v → (∀ j, |σ j| ≤ 1) → ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2 →
    closure (phase (by omega) θ) (fun j => 2 * Real.cos (halfAngle (by omega) θ j)) σ (coordinates (by omega) v) ξ = 0 →
    Configuration.DiameterAtMost 2 (configuration (by omega) θ v σ ξ) := by
  obtain ⟨N, hN⟩ := CommonFiberNonlocalSizes.eventual_domain_sizes
  refine ⟨N, ?_⟩
  intro m hm θ v σ ξ hdom hσ hξ hz i j
  obtain ⟨hθ, hstep, hrad, ha⟩ := hN m hm θ v σ ξ hdom hσ hξ hz
  have hh := offset_bound (by omega) (Nat.mod_lt (i.val + 2 * m - j.val) (by omega))
    θ v σ ξ hdom.1 hz ha hθ hstep hrad j
  change ‖configuration (by omega) θ v σ ξ (cyclicAdvance j (cyclicForwardDistance j i)) -
    configuration (by omega) θ v σ ξ j‖ ≤ 2 at hh
  rwa [cyclicAdvance_forwardDistance] at hh

/-- The constructed root simultaneously realizes closure and every distance
constraint, uniformly for all bounded words on the common energy domain. -/
theorem eventual_feasible_fiber : ∃ N : ℕ, ∀ (m : ℕ) (hm : N + 128 ≤ m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ),
    InDomain (by omega) θ v → (∀ j, |σ j| ≤ 1) →
    ∃ ξ : ℂ, ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2 ∧
      closure (phase (by omega) θ) (fun j => 2 * Real.cos (halfAngle (by omega) θ j)) σ (coordinates (by omega) v) ξ = 0 ∧
      Configuration.DiameterAtMost 2 (configuration (by omega) θ v σ ξ) := by
  obtain ⟨Nd, hd⟩ := eventual_actual_diameter
  obtain ⟨Nr, hr⟩ := eventual_common_domain_root
  refine ⟨Nd + Nr, ?_⟩
  intro m hm θ v σ hdom hσ
  obtain ⟨ξ, hξ, _⟩ := hr m (by omega) θ v σ hdom hσ
  exact ⟨ξ, hξ.1, hξ.2, hd m (by omega) θ v σ ξ hdom hσ hξ.1 hξ.2⟩

end
end StructuralNote.CommonFiberNonlocalFeasibility
