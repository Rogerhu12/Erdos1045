import StructuralNote.RationalExpressions
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Explicit coordinate derivatives of polynomial fractions. The denominator
conditions are precisely those needed for real differentiation. -/

namespace StructuralNote.RationalExpressions

open MvPolynomial
noncomputable section

variable {ι : Type*} [DecidableEq ι]

theorem hasDerivAt_aeval_update (p : MvPolynomial ι Coeff) (x : ι → ℝ) (i : ι) :
    HasDerivAt (fun t => aeval (Function.update x i t) p)
      (aeval x (pderiv i p)) (x i) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using hasDerivAt_const (x i) (c : ℝ)
  | add p q hp hq => simpa only [map_add] using hp.fun_add hq
  | mul_X p j hp =>
    have hj : HasDerivAt (fun t => Function.update x i t j)
        (if j = i then 1 else 0) (x i) := by
      by_cases he : j = i
      · subst j
        simpa using hasDerivAt_id' (x i)
      · simpa [Function.update_of_ne he, he] using hasDerivAt_const (x i) (x j)
    by_cases he : i = j <;>
      simpa [pderiv_mul, Pi.single_apply, apply_ite, eq_comm, he, mul_comm, add_comm] using hp.fun_mul hj

namespace Expression

def coordinateDerivative (i : ι) (f : Expression ι) : Expression ι :=
  ⟨pderiv i f.numerator * f.denominator - f.numerator * pderiv i f.denominator,
    f.denominator * f.denominator⟩

omit [DecidableEq ι] in
theorem valid_coordinateDerivative {f : Expression ι} {x : ι → ℝ} (hf : f.Valid x) (i : ι) :
    (coordinateDerivative i f).Valid x := by
  change aeval x (f.denominator * f.denominator) ≠ 0
  rw [map_mul]
  exact mul_ne_zero hf hf

theorem hasDerivAt_update {f : Expression ι} {x : ι → ℝ} (hf : f.Valid x) (i : ι) :
    HasDerivAt (fun t => f.eval (Function.update x i t)) ((coordinateDerivative i f).eval x) (x i) := by
  have h := (hasDerivAt_aeval_update f.numerator x i).fun_div
    (hasDerivAt_aeval_update f.denominator x i) (by simpa only [Function.update_eq_self] using
      (show aeval x f.denominator ≠ 0 from hf))
  simpa only [eval, coordinateDerivative, map_sub, map_mul, pow_two, Function.update_eq_self] using h

theorem deriv_update {f : Expression ι} {x : ι → ℝ} (hf : f.Valid x) (i : ι) :
    deriv (fun t => f.eval (Function.update x i t)) (x i) = (coordinateDerivative i f).eval x :=
  (hasDerivAt_update hf i).deriv

theorem hasDerivAt_log_update {f : Expression ι} {x : ι → ℝ}
    (hf : f.Valid x) (hn : f.eval x ≠ 0) (i : ι) :
    HasDerivAt (fun t => Real.log (f.eval (Function.update x i t)))
      ((coordinateDerivative i f / f).eval x) (x i) := by
  simpa only [eval_div, Function.update_eq_self] using (hasDerivAt_update hf i).log
    (by simpa only [Function.update_eq_self] using hn)

def rename {κ : Type*} (f : Expression ι) (r : ι → κ) : Expression κ :=
  ⟨MvPolynomial.rename r f.numerator, MvPolynomial.rename r f.denominator⟩

omit [DecidableEq ι] in
theorem eval_rename {κ : Type*} (f : Expression ι) (r : ι → κ) (x : κ → ℝ) :
    (f.rename r).eval x = f.eval (x ∘ r) := by
  simp [rename, eval, aeval_rename]

omit [DecidableEq ι] in
theorem valid_rename {κ : Type*} {f : Expression ι} (r : ι → κ) (x : κ → ℝ)
    (hf : f.Valid (x ∘ r)) : (f.rename r).Valid x := by
  simpa [rename, Valid, aeval_rename] using hf

end Expression
end
end StructuralNote.RationalExpressions

