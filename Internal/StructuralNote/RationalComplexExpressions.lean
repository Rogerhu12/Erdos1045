import StructuralNote.RationalExpressions
import StructuralNote.RationalConfiguration

/-! Complex rational expressions as two explicit real polynomial fractions. -/

namespace StructuralNote.RationalExpressions

open Complex
open scoped BigOperators
noncomputable section

structure ComplexExpression (ι : Type*) where
  re : Expression ι
  im : Expression ι

namespace ComplexExpression

variable {ι : Type*}

def eval (f : ComplexExpression ι) (x : ι → ℝ) : ℂ := ⟨f.re.eval x, f.im.eval x⟩
def Valid (f : ComplexExpression ι) (x : ι → ℝ) : Prop := f.re.Valid x ∧ f.im.Valid x
def ofReal (f : Expression ι) : ComplexExpression ι := ⟨f, 0⟩

instance : Zero (ComplexExpression ι) := ⟨ofReal 0⟩
instance : Add (ComplexExpression ι) := ⟨fun f g => ⟨f.re + g.re, f.im + g.im⟩⟩
instance : Neg (ComplexExpression ι) := ⟨fun f => ⟨-f.re, -f.im⟩⟩
instance : Sub (ComplexExpression ι) := ⟨fun f g => f + -g⟩
instance : Mul (ComplexExpression ι) := ⟨fun f g =>
  ⟨f.re * g.re - f.im * g.im, f.re * g.im + f.im * g.re⟩⟩

theorem valid_ofReal {f : Expression ι} {x : ι → ℝ} (hf : f.Valid x) : (ofReal f).Valid x :=
  ⟨hf, Expression.valid_zero x⟩
theorem valid_zero (x : ι → ℝ) : (0 : ComplexExpression ι).Valid x := valid_ofReal (Expression.valid_zero x)
theorem Valid.add {f g : ComplexExpression ι} {x : ι → ℝ} (hf : f.Valid x) (hg : g.Valid x) :
    (f + g).Valid x := ⟨hf.1.add hg.1, hf.2.add hg.2⟩
theorem Valid.neg {f : ComplexExpression ι} {x : ι → ℝ} (hf : f.Valid x) : (-f).Valid x :=
  ⟨hf.1.neg, hf.2.neg⟩
theorem Valid.sub {f g : ComplexExpression ι} {x : ι → ℝ} (hf : f.Valid x) (hg : g.Valid x) :
    (f - g).Valid x := hf.add hg.neg
theorem Valid.mul {f g : ComplexExpression ι} {x : ι → ℝ} (hf : f.Valid x) (hg : g.Valid x) :
    (f * g).Valid x := ⟨(hf.1.mul hg.1).sub (hf.2.mul hg.2),
      (hf.1.mul hg.2).add (hf.2.mul hg.1)⟩

@[simp] theorem eval_ofReal (f : Expression ι) (x : ι → ℝ) : (ofReal f).eval x = (f.eval x : ℂ) := by
  apply Complex.ext <;> simp [eval, ofReal]
@[simp] theorem eval_zero (x : ι → ℝ) : (0 : ComplexExpression ι).eval x = 0 := by
  change (ofReal 0).eval x = 0
  simp
theorem eval_add {f g : ComplexExpression ι} {x : ι → ℝ} (hf : f.Valid x) (hg : g.Valid x) :
    (f + g).eval x = f.eval x + g.eval x := by
  apply Complex.ext
  · exact Expression.eval_add hf.1 hg.1
  · exact Expression.eval_add hf.2 hg.2
@[simp] theorem eval_neg (f : ComplexExpression ι) (x : ι → ℝ) : (-f).eval x = -f.eval x := by
  apply Complex.ext <;> apply Expression.eval_neg
theorem eval_sub {f g : ComplexExpression ι} {x : ι → ℝ} (hf : f.Valid x) (hg : g.Valid x) :
    (f - g).eval x = f.eval x - g.eval x := by
  change (f + -g).eval x = _
  rw [eval_add hf hg.neg, eval_neg, sub_eq_add_neg]
theorem eval_mul {f g : ComplexExpression ι} {x : ι → ℝ} (hf : f.Valid x) (hg : g.Valid x) :
    (f * g).eval x = f.eval x * g.eval x := by
  apply Complex.ext
  · exact (Expression.eval_sub (hf.1.mul hg.1) (hf.2.mul hg.2)).trans (by simp [eval])
  · exact (Expression.eval_add (hf.1.mul hg.2) (hf.2.mul hg.1)).trans (by simp [eval])

def sum {α : Type*} (s : Finset α) (f : α → ComplexExpression ι) : ComplexExpression ι :=
  ⟨Expression.sum s (fun a => (f a).re), Expression.sum s (fun a => (f a).im)⟩
theorem valid_sum {α : Type*} (s : Finset α) (f : α → ComplexExpression ι) (x : ι → ℝ)
    (h : ∀ a ∈ s, (f a).Valid x) : (sum s f).Valid x :=
  ⟨Expression.valid_sum s _ x (fun a ha => (h a ha).1),
    Expression.valid_sum s _ x (fun a ha => (h a ha).2)⟩
theorem eval_sum {α : Type*} (s : Finset α) (f : α → ComplexExpression ι) (x : ι → ℝ)
    (h : ∀ a ∈ s, (f a).Valid x) : (sum s f).eval x = ∑ a ∈ s, (f a).eval x := by
  apply Complex.ext
  · simpa only [eval, sum, Complex.re_sum] using Expression.eval_sum s (fun a => (f a).re) x (fun a ha => (h a ha).1)
  · simpa only [eval, sum, Complex.im_sum] using Expression.eval_sum s (fun a => (f a).im) x (fun a ha => (h a ha).2)

def squareNorm (f : ComplexExpression ι) : Expression ι := f.re * f.re + f.im * f.im
theorem valid_squareNorm {f : ComplexExpression ι} {x : ι → ℝ} (hf : f.Valid x) :
    f.squareNorm.Valid x := (hf.1.mul hf.1).add (hf.2.mul hf.2)
theorem eval_squareNorm {f : ComplexExpression ι} {x : ι → ℝ} (hf : f.Valid x) :
    f.squareNorm.eval x = Complex.normSq (f.eval x) := by
  rw [squareNorm, Expression.eval_add (hf.1.mul hf.1) (hf.2.mul hf.2)]
  simp [eval, Complex.normSq_apply]

def rotation (t : Expression ι) : ComplexExpression ι :=
  ⟨(1 - t * t) / (1 + t * t),
    (Expression.constant 2 * t) / (1 + t * t)⟩

theorem rotation_denominator_pos {t : Expression ι} {x : ι → ℝ} (ht : t.Valid x) :
    0 < (1 + t * t).eval x := by
  rw [Expression.eval_add (Expression.valid_one x) (ht.mul ht)]
  simp only [Expression.eval_one, Expression.eval_mul]
  nlinarith [sq_nonneg (t.eval x)]

theorem valid_rotation {t : Expression ι} {x : ι → ℝ} (ht : t.Valid x) : (rotation t).Valid x := by
  have hd := (Expression.valid_one x).add (ht.mul ht)
  have hn := (rotation_denominator_pos ht).ne'
  exact ⟨((Expression.valid_one x).sub (ht.mul ht)).div hd hn,
    ((Expression.valid_constant 2 x).mul ht).div hd hn⟩

theorem eval_rotation {t : Expression ι} {x : ι → ℝ} (ht : t.Valid x) :
    (rotation t).eval x = StructuralNote.RationalChart.rotation (t.eval x) := by
  have ha := Expression.eval_add (Expression.valid_one x) (ht.mul ht)
  have hs := Expression.eval_sub (Expression.valid_one x) (ht.mul ht)
  have htwo : ((2 : Coeff) : ℝ) = 2 := rfl
  apply Complex.ext <;>
    norm_num [rotation, eval, Expression.eval_div, ha, hs, htwo, StructuralNote.RationalChart.rotation, pow_two]

def cosine (q : ℚ) : Coeff := ⟨Real.cos ((q : ℝ) * Real.pi),
  mem_algebraicClosure_iff.mpr (RationalConfiguration.rational_pi_coefficients_algebraic q).1⟩
def sine (q : ℚ) : Coeff := ⟨Real.sin ((q : ℝ) * Real.pi),
  mem_algebraicClosure_iff.mpr (RationalConfiguration.rational_pi_coefficients_algebraic q).2⟩
def unit (q : ℚ) : ComplexExpression ι := ⟨Expression.constant (cosine q), Expression.constant (sine q)⟩

theorem valid_unit (q : ℚ) (x : ι → ℝ) : (unit q).Valid x :=
  ⟨Expression.valid_constant _ _, Expression.valid_constant _ _⟩
theorem eval_unit (q : ℚ) (x : ι → ℝ) :
    (unit q).eval x = Erdos1045.EventualExact.LensClosure.unit ((q : ℝ) * Real.pi) := by
  apply Complex.ext <;>
    simp [unit, eval, cosine, sine, Erdos1045.EventualExact.LensClosure.unit_re,
      Erdos1045.EventualExact.LensClosure.unit_im]

end ComplexExpression
end
end StructuralNote.RationalExpressions
