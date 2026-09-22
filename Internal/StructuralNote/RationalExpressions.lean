import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic

/-! Explicit polynomial numerators and denominators over the field of real
algebraic numbers. Evaluation identities retain the exact nonzero conditions. -/

namespace StructuralNote.RationalExpressions

open MvPolynomial
open scoped BigOperators
noncomputable section

abbrev Coeff := algebraicClosure ℚ ℝ

structure Expression (ι : Type*) where
  numerator : MvPolynomial ι Coeff
  denominator : MvPolynomial ι Coeff

namespace Expression

variable {ι : Type*}

def eval (f : Expression ι) (x : ι → ℝ) : ℝ := aeval x f.numerator / aeval x f.denominator

def Valid (f : Expression ι) (x : ι → ℝ) : Prop := aeval x f.denominator ≠ 0

def polynomial (p : MvPolynomial ι Coeff) : Expression ι := ⟨p, 1⟩
def constant (c : Coeff) : Expression ι := polynomial (C c)
def var (i : ι) : Expression ι := polynomial (X i)

instance : Zero (Expression ι) := ⟨constant 0⟩
instance : One (Expression ι) := ⟨constant 1⟩
instance : Add (Expression ι) := ⟨fun f g =>
  ⟨f.numerator * g.denominator + g.numerator * f.denominator, f.denominator * g.denominator⟩⟩
instance : Neg (Expression ι) := ⟨fun f => ⟨-f.numerator, f.denominator⟩⟩
instance : Sub (Expression ι) := ⟨fun f g => f + -g⟩
instance : Mul (Expression ι) := ⟨fun f g =>
  ⟨f.numerator * g.numerator, f.denominator * g.denominator⟩⟩
instance : Inv (Expression ι) := ⟨fun f => ⟨f.denominator, f.numerator⟩⟩
instance : Div (Expression ι) := ⟨fun f g => f * g⁻¹⟩

@[simp] theorem eval_polynomial (p : MvPolynomial ι Coeff) (x : ι → ℝ) :
    (polynomial p).eval x = aeval x p := by simp [eval, polynomial]
@[simp] theorem eval_constant (c : Coeff) (x : ι → ℝ) :
    (constant c).eval x = (c : ℝ) := by simp [constant]
@[simp] theorem eval_variable (i : ι) (x : ι → ℝ) : (var i).eval x = x i := by simp [var]
@[simp] theorem eval_zero (x : ι → ℝ) : (0 : Expression ι).eval x = 0 := by
  change (constant 0).eval x = 0
  simp
@[simp] theorem eval_one (x : ι → ℝ) : (1 : Expression ι).eval x = 1 := by
  change (constant 1).eval x = 1
  simp

theorem valid_polynomial (p : MvPolynomial ι Coeff) (x : ι → ℝ) : (polynomial p).Valid x := by
  simp [Valid, polynomial]
theorem valid_constant (c : Coeff) (x : ι → ℝ) : (constant c).Valid x := valid_polynomial _ _
theorem valid_variable (i : ι) (x : ι → ℝ) : (var i).Valid x := valid_polynomial _ _
theorem valid_zero (x : ι → ℝ) : (0 : Expression ι).Valid x := valid_constant _ _
theorem valid_one (x : ι → ℝ) : (1 : Expression ι).Valid x := valid_constant _ _

theorem Valid.add {f g : Expression ι} {x : ι → ℝ} (hf : f.Valid x) (hg : g.Valid x) :
    (f + g).Valid x := by
  change aeval x (f.denominator * g.denominator) ≠ 0
  rw [map_mul]
  exact mul_ne_zero hf hg
theorem Valid.neg {f : Expression ι} {x : ι → ℝ} (hf : f.Valid x) : (-f).Valid x := hf
theorem Valid.sub {f g : Expression ι} {x : ι → ℝ} (hf : f.Valid x) (hg : g.Valid x) :
    (f - g).Valid x := hf.add hg.neg
theorem Valid.mul {f g : Expression ι} {x : ι → ℝ} (hf : f.Valid x) (hg : g.Valid x) :
    (f * g).Valid x := by
  change aeval x (f.denominator * g.denominator) ≠ 0
  rw [map_mul]
  exact mul_ne_zero hf hg

theorem eval_add {f g : Expression ι} {x : ι → ℝ} (hf : f.Valid x) (hg : g.Valid x) :
    (f + g).eval x = f.eval x + g.eval x := by
  change aeval x (f.numerator * g.denominator + g.numerator * f.denominator) /
    aeval x (f.denominator * g.denominator) = _
  simp only [map_mul, map_add]
  simpa only [eval, mul_comm] using (div_add_div (aeval x f.numerator) (aeval x g.numerator) hf hg).symm
@[simp] theorem eval_neg (f : Expression ι) (x : ι → ℝ) : (-f).eval x = -f.eval x := by
  change aeval x (-f.numerator) / aeval x f.denominator = -f.eval x
  rw [map_neg, neg_div]
  rfl
theorem eval_sub {f g : Expression ι} {x : ι → ℝ} (hf : f.Valid x) (hg : g.Valid x) :
    (f - g).eval x = f.eval x - g.eval x := by
  change (f + -g).eval x = _
  rw [eval_add hf hg.neg, eval_neg, sub_eq_add_neg]
@[simp] theorem eval_mul (f g : Expression ι) (x : ι → ℝ) :
    (f * g).eval x = f.eval x * g.eval x := by
  change aeval x (f.numerator * g.numerator) / aeval x (f.denominator * g.denominator) =
    (aeval x f.numerator / aeval x f.denominator) * (aeval x g.numerator / aeval x g.denominator)
  rw [map_mul, map_mul, div_mul_div_comm]
@[simp] theorem eval_inv (f : Expression ι) (x : ι → ℝ) : f⁻¹.eval x = (f.eval x)⁻¹ := by
  change aeval x f.denominator / aeval x f.numerator = (aeval x f.numerator / aeval x f.denominator)⁻¹
  rw [inv_div]
@[simp] theorem eval_div (f g : Expression ι) (x : ι → ℝ) :
    (f / g).eval x = f.eval x / g.eval x := by
  change (f * g⁻¹).eval x = _
  rw [eval_mul, eval_inv, div_eq_mul_inv]

theorem eval_eq_zero_iff {f : Expression ι} {x : ι → ℝ} (hf : f.Valid x) :
    f.eval x = 0 ↔ aeval x f.numerator = 0 := by
  rw [eval, div_eq_zero_iff, or_iff_left hf]

theorem Valid.inv {f : Expression ι} {x : ι → ℝ} (hf : f.Valid x) (h : f.eval x ≠ 0) :
    f⁻¹.Valid x := by
  exact fun he => h ((eval_eq_zero_iff hf).2 he)
theorem Valid.div {f g : Expression ι} {x : ι → ℝ} (hf : f.Valid x) (hg : g.Valid x)
    (h : g.eval x ≠ 0) : (f / g).Valid x := hf.mul (hg.inv h)

def sumList : List (Expression ι) → Expression ι
  | [] => 0
  | f :: fs => f + sumList fs

theorem valid_sumList (fs : List (Expression ι)) (x : ι → ℝ)
    (h : ∀ f ∈ fs, f.Valid x) : (sumList fs).Valid x := by
  induction fs with
  | nil => exact valid_zero x
  | cons f fs ih => exact (h f (by simp)).add (ih (fun g hg => h g (by simp [hg])))

theorem eval_sumList (fs : List (Expression ι)) (x : ι → ℝ)
    (h : ∀ f ∈ fs, f.Valid x) : (sumList fs).eval x = (fs.map (fun f => f.eval x)).sum := by
  induction fs with
  | nil => exact eval_zero x
  | cons f fs ih =>
    have hs : ∀ g ∈ fs, g.Valid x := fun g hg => h g (by simp [hg])
    rw [sumList, eval_add (h f (by simp)) (valid_sumList fs x hs), ih hs]
    rfl

def sum {α : Type*} (s : Finset α) (f : α → Expression ι) : Expression ι := sumList (s.toList.map f)

theorem valid_sum {α : Type*} (s : Finset α) (f : α → Expression ι) (x : ι → ℝ)
    (h : ∀ a ∈ s, (f a).Valid x) : (sum s f).Valid x := by
  apply valid_sumList
  simpa using h

theorem eval_sum {α : Type*} (s : Finset α) (f : α → Expression ι) (x : ι → ℝ)
    (h : ∀ a ∈ s, (f a).Valid x) : (sum s f).eval x = ∑ a ∈ s, (f a).eval x := by
  rw [sum, eval_sumList _ x (by simpa using h)]
  simp

end Expression
end
end StructuralNote.RationalExpressions
