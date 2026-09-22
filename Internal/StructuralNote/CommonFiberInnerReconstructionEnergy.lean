import EventualExact.AngularObjectiveCurvature
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.MeanValue

/-! A mean-value estimate for the actual pair-energy seminorm, retaining the
sum before applying the derivative bound. -/

namespace StructuralNote.CommonFiberInnerReconstruction

open Erdos1045 Erdos1045.EventualExact Complex SchurSpectrum AngularObjectiveCurvature
open scoped BigOperators
noncomputable section

def energyVector {n : ℕ} (c : Fin n → ℂ) : EuclideanSpace ℂ (Fin n × Fin n) :=
  WithLp.toLp 2 (fun p => (c p.1 - c p.2) /
    (LocalPhase.regularRoot n ^ (p.1 : ℕ) - LocalPhase.regularRoot n ^ (p.2 : ℕ)))

theorem energyVector_norm_sq {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) :
    ‖energyVector c‖ ^ 2 = 2 * pairEnergy hn c := by
  rw [EuclideanSpace.norm_sq_eq, pairEnergy_eq_chord_sum]
  simp only [energyVector, ← Complex.normSq_eq_norm_sq,
    normSq_div, Fintype.sum_prod_type]
  ring

theorem energyVector_sub {n : ℕ} (c d : Fin n → ℂ) :
    energyVector (c - d) = energyVector c - energyVector d := by
  ext p
  change (c p.1 - d p.1 - (c p.2 - d p.2)) / _ = (c p.1 - c p.2) / _ - (d p.1 - d p.2) / _
  ring

theorem energyVector_hasDerivAt {n : ℕ} {c : ℝ → Fin n → ℂ} {c' : Fin n → ℂ} {x : ℝ}
    (hc : ∀ j, HasDerivAt (fun t => c t j) (c' j) x) :
    HasDerivAt (fun t => energyVector (c t)) (energyVector c') x := by
  have hp : HasDerivAt (fun (t : ℝ) (p : Fin n × Fin n) => (c t p.1 - c t p.2) /
      (LocalPhase.regularRoot n ^ (p.1 : ℕ) - LocalPhase.regularRoot n ^ (p.2 : ℕ)))
      (fun p => (c' p.1 - c' p.2) /
      (LocalPhase.regularRoot n ^ (p.1 : ℕ) - LocalPhase.regularRoot n ^ (p.2 : ℕ))) x :=
    hasDerivAt_pi.mpr (fun p => ((hc p.1).sub (hc p.2)).div_const _)
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n × Fin n => ℂ)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x hp

theorem energy_mean_value {n : ℕ} (hn : 0 < n) (c c' : ℝ → Fin n → ℂ) {M : ℝ}
    (hM : 0 ≤ M) (hc : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ j, HasDerivAt (fun s => c s j) (c' t j) t)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, pairEnergy hn (c' t) ≤ M) :
    pairEnergy hn (c 1 - c 0) ≤ M := by
  have hv := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht => (energyVector_hasDerivAt (hc t ht)).hasDerivWithinAt)
    (C := Real.sqrt (2 * M)) (fun t ht => ?_)
  · rw [← energyVector_sub] at hv
    have hs := pow_le_pow_left₀ (norm_nonneg _) hv 2
    rw [energyVector_norm_sq hn, Real.sq_sqrt (by positivity)] at hs
    linarith
  · apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
    rw [energyVector_norm_sq hn]
    exact mul_le_mul_of_nonneg_left (hbound t ⟨ht.1, ht.2.le⟩) (by norm_num)

end
end StructuralNote.CommonFiberInnerReconstruction
