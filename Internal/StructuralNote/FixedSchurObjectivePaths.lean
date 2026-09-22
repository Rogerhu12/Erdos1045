import StructuralNote.FixedSchurObjectiveSmooth
import StructuralNote.FixedSchurConfigurationDerivatives
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Smooth affine paths and translation of their genuine second derivatives. -/

namespace StructuralNote.FixedSchurObjectivePaths

open Complex Filter Erdos1045.EventualExact
open FixedSchurEquationSmooth FixedSchurChart FixedSchurObjective
open FixedSchurObjectiveSmooth FixedSchurConfigurationDerivatives FixedSchurChosenPath
open CommonFiberCanonicalPaths CommonFiberCanonicalDirections
open scoped Topology ContDiff

noncomputable section

def objective {m : ℕ} (hm : 0 < m) (s : FiniteBox.SignPattern hm)
    (x : SchurParameters m) : ℝ := F (configuration hm s x.1 x.2)

theorem affine_shift {m : ℕ} (x d : SchurParameters m) (t r : ℝ) :
    affinePath (affinePath x d t) d r = affinePath x d (r + t) := by
  unfold affinePath
  module

theorem deriv2_translate (f : ℝ → ℝ) (t : ℝ) :
    deriv (deriv (fun r => f (r + t))) 0 = deriv (deriv f) t := by
  have he : deriv (fun r => f (r + t)) = (fun r => deriv f (r + t)) :=
    funext (fun r => deriv_comp_add_const f t r)
  rw [he, deriv_comp_add_const, zero_add]

theorem affine_deriv2_shift {m : ℕ} (hm : 0 < m) (s : FiniteBox.SignPattern hm)
    (x d : SchurParameters m) (t : ℝ) :
    deriv (deriv (fun r => objective hm s (affinePath (affinePath x d t) d r))) 0 =
      deriv (deriv (fun r => objective hm s (affinePath x d r))) t := by
  simp only [affine_shift]
  exact deriv2_translate (fun r => objective hm s (affinePath x d r)) t

theorem eventual_objective_contDiffWithinAt : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega)) (x : SchurParameters m),
      x ∈ FixedSchurChartSmooth.domain (by omega) →
      ContDiffWithinAt ℝ ∞ (objective (by omega) s) (FixedSchurChartSmooth.domain (by omega)) x := by
  filter_upwards [eventual_actual_objective_contDiffWithinAt] with m h
  exact h

theorem eventual_objective_direction_contDiffAt : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega)) (x d : SchurParameters m),
      x ∈ FixedSchurChartSmooth.domain (by omega) → Admissible (by omega) d →
      ContDiffAt ℝ ∞ (fun t => objective (by omega) s (affinePath x d t)) 0 := by
  filter_upwards [eventual_objective_contDiffWithinAt] with m hsmooth
  intro hm s x d hx hd
  let S : Set ℝ := (affinePath x d) ⁻¹' FixedSchurChartSmooth.domain (by omega)
  have hdom : S ∈ 𝓝 (0 : ℝ) := affine_domain_near_zero (by omega) x d hx hd
  have hx' : affinePath x d 0 ∈ FixedSchurChartSmooth.domain (by omega) := by
    simpa only [affinePath, zero_smul, add_zero] using hx
  have hf := hsmooth hm s (affinePath x d 0) hx'
  have hp := (affinePath_contDiff x d).contDiffAt.contDiffWithinAt (s := S) (x := (0 : ℝ))
  exact (hf.comp 0 hp (fun _ h => h)).contDiffAt hdom

theorem eventual_affine_deriv2_eq : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega)) (x d : SchurParameters m) (t : ℝ),
      affinePath x d t ∈ FixedSchurChartSmooth.domain (by omega) → Admissible (by omega) d →
      deriv (deriv (fun r => objective (by omega) s (affinePath x d r))) t =
        LogDiscriminantSecondDerivative.second
          (configuration (by omega) s (affinePath x d t).1 (affinePath x d t).2)
          (velocityPath (by omega) s (affinePath x d t).1 d.1 (affinePath x d t).2 d.2 0)
          (acceleration (by omega) s (affinePath x d t).1 d.1 (affinePath x d t).2 d.2) := by
  filter_upwards [eventual_actual_log_second_derivative] with m hsecond
  intro hm s x d t hx hd
  rw [← affine_deriv2_shift (by omega) s x d t]
  exact (hsecond hm s _ _ _ _ hx hd).deriv

end
end StructuralNote.FixedSchurObjectivePaths
