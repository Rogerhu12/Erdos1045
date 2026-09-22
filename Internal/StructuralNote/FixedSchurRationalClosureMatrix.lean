import StructuralNote.FixedSchurRationalWindowClosureDerivative
import StructuralNote.RationalStationarySystem
import StructuralNote.BorderedHessian
import Mathlib.Analysis.Calculus.Deriv.Pi

/-! The actual rational closure derivative as the two-row matrix in the
stationary system, including its full row rank on the literal window. -/

namespace StructuralNote.FixedSchurRationalClosureMatrix

open Complex Filter Erdos1045.EventualExact
open Matrix
open RationalExpressions RationalConfigurationPolynomials RationalStationarySystem
open FixedSchurRationalWindowDomain FixedSchurRationalWindowClosureDerivative
open CommonDomainRadius
open scoped BigOperators Topology

noncomputable section

theorem linear_eq_sum_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : (ι → ℝ) →L[ℝ] ℝ) (x : ι → ℝ) :
    T x = ∑ i, T (Pi.single i 1) * x i := by
  have he : x = ∑ i, x i • Pi.single i (1 : ℝ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  calc
    T x = T (∑ i, x i • Pi.single i (1 : ℝ)) := congrArg T he
    _ = ∑ i, T (Pi.single i 1) * x i := by simp [mul_comm]

def component (k : Fin 2) : ℂ →L[ℝ] ℝ := if k.val = 0 then reCLM else imCLM

theorem component_eval {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool)
    (k : Fin 2) (X : Vars m → ℝ) :
    (closureCoordinate hm σ k).eval X = component k (RationalConfiguration.closure hm (sign σ) X) := by
  fin_cases k
  · exact closureReal_eval hm σ X
  · exact closureImag_eval hm σ X

def closureMatrix {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (X : Vars m → ℝ) :
    Matrix (Fin 2) (Vars m) ℝ := fun k i =>
      deriv (fun t => (closureCoordinate hm σ k).eval (Function.update X i t)) (X i)

theorem closureMatrix_entry {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool)
    (X : Vars m → ℝ) (k : Fin 2) (i : Vars m) :
    closureMatrix hm σ X k i = component k (closureFDeriv hm (sign σ) X (Pi.single i 1)) := by
  have hF := (component k).hasFDerivAt.comp X (closure_hasFDerivAt hm (sign σ) X)
  have hF' : HasFDerivAt (fun Z => (closureCoordinate hm σ k).eval Z)
      ((component k).comp (closureFDeriv hm (sign σ) X)) X := by
    simpa only [Function.comp_def, component_eval] using hF
  have hu := hasDerivAt_update X i (X i)
  have hF'' : HasFDerivAt (fun Z => (closureCoordinate hm σ k).eval Z)
      ((component k).comp (closureFDeriv hm (sign σ) X)) (Function.update X i (X i)) := by
    simpa only [Function.update_eq_self] using hF'
  exact (hF''.comp_hasDerivAt (X i) hu).deriv

theorem closureMatrix_mulVec {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool)
    (X v : Vars m → ℝ) (k : Fin 2) :
    (closureMatrix hm σ X *ᵥ v) k = component k (closureFDeriv hm (sign σ) X v) := by
  rw [Matrix.mulVec, dotProduct]
  simp only [closureMatrix_entry]
  exact (linear_eq_sum_basis ((component k).comp (closureFDeriv hm (sign σ) X)) v).symm

theorem closureMatrix_surjective {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool)
    (X : Vars m → ℝ) (hfull : Function.Surjective (closureFDeriv hm (sign σ) X)) :
    Function.Surjective (closureMatrix hm σ X).mulVec := by
  intro w
  obtain ⟨v, hv⟩ := hfull (⟨w 0, w 1⟩ : ℂ)
  refine ⟨v, ?_⟩
  funext k
  rw [closureMatrix_mulVec, hv]
  fin_cases k <;> rfl

def halfWord {m : ℕ} {hm : 0 < m} (s : FiniteBox.SignPattern hm) : Fin m → Bool :=
  fun j => s.val ⟨j.val, by omega⟩

theorem sign_halfWord {m : ℕ} {hm : 0 < m} (s : FiniteBox.SignPattern hm) :
    sign (halfWord s) = rationalSign s := by
  funext j
  rfl

theorem eventual_selectedWindow_closureMatrix_surjective : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 8 ≤ m) (s : FiniteBox.SignPattern (by omega)) (X : Vars m → ℝ),
      selectedWindowEnergy (by omega) s X <
        (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
      RationalConfiguration.closure (by omega) (rationalSign s) X = 0 →
      Function.Surjective (closureMatrix (by omega) (halfWord s) X).mulVec := by
  filter_upwards [eventual_selectedWindow_closure_hasFDerivAt_surjective] with m hfull
  intro hm s X hwindow hclosure
  apply closureMatrix_surjective
  rw [sign_halfWord]
  exact (hfull hm s X hwindow hclosure).2

end
end StructuralNote.FixedSchurRationalClosureMatrix
