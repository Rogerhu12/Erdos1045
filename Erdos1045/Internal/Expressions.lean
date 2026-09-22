import Erdos1045.Statement
import StructuralNote.RationalComplexExpressions
import StructuralNote.RationalExpressionDerivatives

open StructuralNote

/-! Structural identification of the independent rational-expression syntax. -/

namespace Erdos1045.Statement.Algebraic

noncomputable section

namespace Expression

variable {ι κ : Type*}

def toInternal (f : Expression ι) : RationalExpressions.Expression ι :=
  ⟨f.numerator, f.denominator⟩

@[simp] theorem toInternal_numerator (f : Expression ι) :
    f.toInternal.numerator = f.numerator := rfl

@[simp] theorem toInternal_denominator (f : Expression ι) :
    f.toInternal.denominator = f.denominator := rfl

@[simp] theorem toInternal_eval (f : Expression ι) (x : ι → ℝ) :
    f.toInternal.eval x = f.eval x := rfl

@[simp] theorem toInternal_constant (c : Coeff) :
    (constant c : Expression ι).toInternal = RationalExpressions.Expression.constant c := rfl

@[simp] theorem toInternal_var (i : ι) :
    (var i).toInternal = RationalExpressions.Expression.var i := rfl

@[simp] theorem toInternal_zero :
    (0 : Expression ι).toInternal = 0 := rfl

@[simp] theorem toInternal_one :
    (1 : Expression ι).toInternal = 1 := rfl

@[simp] theorem toInternal_add (f g : Expression ι) :
    (f + g).toInternal = f.toInternal + g.toInternal := rfl

@[simp] theorem toInternal_neg (f : Expression ι) :
    (-f).toInternal = -f.toInternal := rfl

@[simp] theorem toInternal_sub (f g : Expression ι) :
    (f - g).toInternal = f.toInternal - g.toInternal := rfl

@[simp] theorem toInternal_mul (f g : Expression ι) :
    (f * g).toInternal = f.toInternal * g.toInternal := rfl

@[simp] theorem toInternal_inv (f : Expression ι) :
    f⁻¹.toInternal = f.toInternal⁻¹ := rfl

@[simp] theorem toInternal_div (f g : Expression ι) :
    (f / g).toInternal = f.toInternal / g.toInternal := rfl

@[simp] theorem toInternal_sumList (fs : List (Expression ι)) :
    (sumList fs).toInternal = RationalExpressions.Expression.sumList (fs.map toInternal) := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simpa only [sumList, List.map_cons, RationalExpressions.Expression.sumList,
      toInternal_add] using congrArg (fun t => f.toInternal + t) ih

@[simp] theorem toInternal_sum {α : Type*} (s : Finset α) (f : α → Expression ι) :
    (sum s f).toInternal = RationalExpressions.Expression.sum s (fun a => (f a).toInternal) := by
  simp only [sum, RationalExpressions.Expression.sum, toInternal_sumList, List.map_map,
    Function.comp_def]

@[simp] theorem toInternal_derivative [DecidableEq ι] (i : ι) (f : Expression ι) :
    (coordinateDerivative i f).toInternal =
      RationalExpressions.Expression.coordinateDerivative i f.toInternal := rfl

@[simp] theorem toInternal_rename (f : Expression ι) (r : ι → κ) :
    (f.rename r).toInternal = f.toInternal.rename r := rfl

end Expression

namespace ComplexExpression

variable {ι : Type*}

def toInternal (f : ComplexExpression ι) : RationalExpressions.ComplexExpression ι :=
  ⟨f.re.toInternal, f.im.toInternal⟩

@[simp] theorem toInternal_re (f : ComplexExpression ι) :
    f.re.toInternal = f.toInternal.re := rfl

@[simp] theorem toInternal_im (f : ComplexExpression ι) :
    f.im.toInternal = f.toInternal.im := rfl

@[simp] theorem toInternal_ofReal (f : Expression ι) :
    (ofReal f).toInternal = RationalExpressions.ComplexExpression.ofReal f.toInternal := rfl

@[simp] theorem toInternal_zero :
    (0 : ComplexExpression ι).toInternal = 0 := rfl

@[simp] theorem toInternal_add (f g : ComplexExpression ι) :
    (f + g).toInternal = f.toInternal + g.toInternal := rfl

@[simp] theorem toInternal_neg (f : ComplexExpression ι) :
    (-f).toInternal = -f.toInternal := rfl

@[simp] theorem toInternal_sub (f g : ComplexExpression ι) :
    (f - g).toInternal = f.toInternal - g.toInternal := rfl

@[simp] theorem toInternal_mul (f g : ComplexExpression ι) :
    (f * g).toInternal = f.toInternal * g.toInternal := rfl

@[simp] theorem toInternal_sum {α : Type*} (s : Finset α) (f : α → ComplexExpression ι) :
    (sum s f).toInternal = RationalExpressions.ComplexExpression.sum s
      (fun a => (f a).toInternal) := by
  unfold toInternal sum RationalExpressions.ComplexExpression.sum
  congr 1 <;> apply Expression.toInternal_sum

@[simp] theorem toInternal_squareNorm (f : ComplexExpression ι) :
    f.squareNorm.toInternal = f.toInternal.squareNorm := rfl

@[simp] theorem toInternal_rotation (t : Expression ι) :
    (rotation t).toInternal = RationalExpressions.ComplexExpression.rotation t.toInternal := rfl

@[simp] theorem cosine_eq (q : ℚ) :
    cosine q = RationalExpressions.ComplexExpression.cosine q := rfl

@[simp] theorem sine_eq (q : ℚ) :
    sine q = RationalExpressions.ComplexExpression.sine q := rfl

@[simp] theorem toInternal_unit (q : ℚ) :
    (unit q : ComplexExpression ι).toInternal = RationalExpressions.ComplexExpression.unit q := rfl

end ComplexExpression

end
end Erdos1045.Statement.Algebraic
