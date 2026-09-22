import StructuralNote.MatchingActivityRadialVelocity

/-! The direct source of a single radial variation has exactly two possible
nonzero entries, so the closure correction has order 1/m. -/

namespace StructuralNote.MatchingActivityRadialSource

open Erdos1045 Erdos1045.EventualExact Complex Configuration Filter
open LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open CommonClosureEnergy CommonFiberGeometry MatchingActivityRadialClosure MatchingActivityRadialPair
open MatchingActivityRadialBounds MatchingActivityRadialVelocity MatchingActivityRadialFeasible
open LensIncrementDerivatives LensClosurePathDerivatives ClosedSourceIntegration
open scoped BigOperators
noncomputable section

theorem nextIndex_ne {m : ℕ} (hm : 2 ≤ m) (j : Fin m) : nextIndex (by omega) j ≠ j := by
  intro h
  have hh := congrArg Fin.val h
  change (j.val + 1) % m = j.val at hh
  by_cases hj : j.val + 1 < m
  · rw [Nat.mod_eq_of_lt hj] at hh
    omega
  · have he : j.val + 1 = m := by omega
    rw [he, Nat.mod_self] at hh
    omega

theorem nextIndex_sum {m : ℕ} (hm : 2 ≤ m) (f : Fin m → ℝ) :
    (∑ j, f (nextIndex (by omega) j)) = ∑ j, f j := by
  have he (j : Fin m) : nextIndex (by omega) j = finRotate m j := by
    let : NeZero m := ⟨by omega⟩
    rw [finRotate_apply]
    apply Fin.ext
    change (j.val + 1) % m = (j.val + 1 % m) % m
    rw [Nat.mod_eq_of_lt (by omega : 1 < m)]
  simp_rw [he]
  exact Equiv.sum_comp (finRotate m) f

theorem radiusVelocity_sum {m : ℕ} (i : Fin m) : (∑ j, radiusVelocity i j) = 1 := by
  simp [radiusVelocity]

theorem directSource_zero {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (i j : Fin m) (hj : j ≠ i) (hn : nextIndex hm j ≠ i) :
    directSource hm θ σ ν r i j = 0 := by
  simp [directSource, phaseVelocity, lengthVelocity, pairVelocity, radiusVelocity, hj, hn,
    pair, incrementVelocity, bodyVelocity]

theorem directSource_point_bound {m : ℕ} (hm : 2 ≤ m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (i j : Fin m)
    (hpos : 1 ≤ (pair (halfAngle (by omega) θ j) (r j) (r (nextIndex (by omega) j))).re)
    (hr : ∀ k, |r k| ≤ 1) (hφ : |halfAngle (by omega) θ j| ≤ 1 / 4)
    (hσ : |σ j| ≤ 1) (hν : |ν j| ≤ 1)
    (hb : ‖body (radialLength (by omega) θ r j) (σ j) (ν j)‖ ≤ 1) :
    ‖directSource (by omega) θ σ ν r i j‖ ≤ 2 * (radiusVelocity i j + radiusVelocity i (nextIndex (by omega) j)) := by
  have hd := individual_derivative_bounds hpos (hr j) (hr (nextIndex (by omega) j))
  dsimp only [pair] at hd
  have hvel := velocity_residual_bound (α := radialPhase (by omega) θ r j)
    (μ := midpoint m j) (L := radialLength (by omega) θ r j) (a := phaseVelocity (by omega) θ r i j)
    (l := lengthVelocity (by omega) θ r i j) (u := 0) hσ hν
  simp only [ofReal_zero, zero_mul, sub_zero, abs_zero, add_zero] at hvel
  by_cases hj : j = i
  · have hn : nextIndex (by omega) j ≠ i := by simpa only [← hj] using nextIndex_ne hm j
    have hα : |phaseVelocity (by omega) θ r i j| ≤ 1 / 2 := by
      simp only [phaseVelocity, pairVelocity, radiusVelocity, if_pos hj, if_neg hn, pair, ofReal_one, one_mul, ofReal_zero, zero_mul, add_zero]
      linarith [hd.2.2.1]
    have hL : |lengthVelocity (by omega) θ r i j| ≤ 1 := by
      simpa only [lengthVelocity, radialLength, pairVelocity, radiusVelocity, if_pos hj, if_neg hn, pair, ofReal_one, one_mul, ofReal_zero, zero_mul, add_zero] using hd.1
    change ‖directSource (by omega) θ σ ν r i j‖ ≤ _ at hvel
    simp only [radiusVelocity, if_pos hj, if_neg hn, add_zero, mul_one]
    nlinarith [norm_nonneg (body (radialLength (by omega) θ r j) (σ j) (ν j))]
  · by_cases hn : nextIndex (by omega) j = i
    · have hα : |phaseVelocity (by omega) θ r i j| ≤ 1 / 2 := by
        simp only [phaseVelocity, pairVelocity, radiusVelocity, if_neg hj, if_pos hn, pair, ofReal_one, one_mul, ofReal_zero, zero_mul, zero_add]
        linarith [hd.2.2.2]
      have hL : |lengthVelocity (by omega) θ r i j| ≤ 1 := by
        simpa only [lengthVelocity, radialLength, pairVelocity, radiusVelocity, if_neg hj, if_pos hn, pair, ofReal_one, one_mul, ofReal_zero, zero_mul, zero_add] using hd.2.1
      change ‖directSource (by omega) θ σ ν r i j‖ ≤ _ at hvel
      simp only [radiusVelocity, if_neg hj, if_pos hn, zero_add, mul_one]
      nlinarith [norm_nonneg (body (radialLength (by omega) θ r j) (σ j) (ν j))]
    · rw [directSource_zero (by omega) θ σ ν r i j hj hn]
      simp only [norm_zero, radiusVelocity, if_neg hj, if_neg hn, add_zero, mul_zero, le_refl]

theorem directSource_sum_bound {m : ℕ} (hm : 2 ≤ m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (i : Fin m)
    (hpos : ∀ j, 1 ≤ (pair (halfAngle (by omega) θ j) (r j) (r (nextIndex (by omega) j))).re)
    (hr : ∀ k, |r k| ≤ 1) (hφ : ∀ j, |halfAngle (by omega) θ j| ≤ 1 / 4)
    (hσ : ∀ j, |σ j| ≤ 1) (hν : ∀ j, |ν j| ≤ 1)
    (hb : ∀ j, ‖body (radialLength (by omega) θ r j) (σ j) (ν j)‖ ≤ 1) :
    (∑ j, ‖directSource (by omega) θ σ ν r i j‖) ≤ 4 := by
  have he := Finset.sum_le_sum (s := Finset.univ) (fun j _ => directSource_point_bound hm θ σ ν r i j
    (hpos j) hr (hφ j) (hσ j) (hν j) (hb j))
  simpa only [← Finset.mul_sum, Finset.sum_add_distrib, nextIndex_sum hm, radiusVelocity_sum,
    show (2 : ℝ) * (1 + 1) = 4 by norm_num] using he

theorem actual_closureSpeed_le {m : ℕ} (hm : 2 ≤ m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (a : ℂ) (g : (Fin m → ℝ) → ℂ) (i : Fin m)
    (hchart : IsFeasibleRadialChart (by omega) θ σ ν r a g)
    (hpos : ∀ j, 1 ≤ (pair (halfAngle (by omega) θ j) (r j) (r (nextIndex (by omega) j))).re)
    (hr : ∀ j, |r j| ≤ 1) (hφ : ∀ j, |halfAngle (by omega) θ j| ≤ 1 / 4)
    (hsmall : ∀ j, |radialPhase (by omega) θ r j - midpoint m j| + |ν j| ≤ 1 / 4)
    (hb : ∀ j, ‖body (radialLength (by omega) θ r j) (σ j) (ν j)‖ ≤ 1) :
    ‖closureSpeed r g i‖ ≤ 16 / (m : ℝ) := by
  have hp (j : Fin m) : 0 < (pair (halfAngle (by omega) θ j) (r j) (r (nextIndex (by omega) j))).re := lt_of_lt_of_le (by norm_num) (hpos j)
  have hν (j : Fin m) : |ν j| ≤ 1 := by linarith [hsmall j, abs_nonneg (radialPhase (by omega) θ r j - midpoint m j)]
  have hs := directSource_sum_bound hm θ σ ν r i hpos hr hφ hchart.1 hν hb
  have he := closureSpeed_bound hm θ σ ν r a g i hchart hp hsmall
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  calc
    _ ≤ (4 / m : ℝ) * ∑ j, ‖directSource (by omega) θ σ ν r i j‖ := he
    _ ≤ (4 / m : ℝ) * 4 := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

theorem centerVelocity_variation_bound {m : ℕ} (hm : 2 ≤ m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (a : ℂ) (g : (Fin m → ℝ) → ℂ) (i : Fin m)
    (hchart : IsFeasibleRadialChart (by omega) θ σ ν r a g)
    (hpos : ∀ j, 1 ≤ (pair (halfAngle (by omega) θ j) (r j) (r (nextIndex (by omega) j))).re)
    (hr : ∀ j, |r j| ≤ 1) (hφ : ∀ j, |halfAngle (by omega) θ j| ≤ 1 / 4)
    (hsmall : ∀ j, |radialPhase (by omega) θ r j - midpoint m j| + |ν j| ≤ 1 / 4)
    (hb : ∀ j, ‖body (radialLength (by omega) θ r j) (σ j) (ν j)‖ ≤ 1) :
    (∑ j, ‖difference (by omega) (centerVelocity (by omega) θ σ ν r g i) j‖) ≤ 72 ∧
      ∀ j, ‖centerVelocity (by omega) θ σ ν r g i j‖ ≤ 144 := by
  have hp (j : Fin m) : 0 < (pair (halfAngle (by omega) θ j) (r j) (r (nextIndex (by omega) j))).re := lt_of_lt_of_le (by norm_num) (hpos j)
  have hν (j : Fin m) : |ν j| ≤ 1 / 4 := by linarith [hsmall j, abs_nonneg (radialPhase (by omega) θ r j - midpoint m j)]
  have ht (j : Fin m) : ν j ^ 2 < 4 := by nlinarith [(abs_le.mp (hν j)).1, (abs_le.mp (hν j)).2]
  have he := actual_closure_derivative (by omega) θ σ ν r a g i hchart hp ht
  have hs := directSource_sum_bound hm θ σ ν r i hpos hr hφ hchart.1 (fun j => (hν j).trans (by norm_num)) hb
  have hsmall' (j : Fin m) : |radialPhase (by omega) θ r j - midpoint m j| + |heightParameter ν 0 j| ≤ 1 / 4 := by
    simpa only [heightParameter, map_zero, add_zero] using hsmall j
  have hc := corrected_source_l1 hm _ _ _ _ _ _ hchart.1 hsmall' he
  have hd := integrateCorrected_difference (by omega) _ _ _ _ _ _ he
  have htv : (∑ j, ‖difference (by omega) (centerVelocity (by omega) θ σ ν r g i) j‖) ≤ 72 := by
    unfold centerVelocity
    rw [hd, repeatHalf_map_sum (by omega) _ (fun z => ‖z‖)]
    change 2 * (∑ j, ‖corrected (radialPhase (by omega) θ r) σ ν 0 (closureSpeed r g i) (directSource (by omega) θ σ ν r i) j‖) ≤ 72
    change (∑ j, ‖corrected (radialPhase (by omega) θ r) σ ν 0 (closureSpeed r g i) (directSource (by omega) θ σ ν r i) j‖) ≤ _ at hc
    linarith
  refine ⟨htv, ?_⟩
  intro j
  have hh := SchurLiftBounds.finite_integral_norm_bound (by omega) (centerVelocity (by omega) θ σ ν r g i)
    (integral_mean_zero (by omega) _) j
  linarith

end
end StructuralNote.MatchingActivityRadialSource
