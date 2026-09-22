import StructuralNote.RationalComplexExpressions
import StructuralNote.FixedSchurRationalWindowEnergy

/-! Algebraic coefficients of the finite Fourier lift. -/

namespace StructuralNote.FixedSchurAlgebraicData

open Complex Erdos1045 Erdos1045.EventualExact
open FourierMultiplier FiniteFourierLift SchurLift
open scoped BigOperators
noncomputable section

theorem algebraic_div {x y : ℝ} (hx : IsAlgebraic ℚ x) (hy : IsAlgebraic ℚ y) :
    IsAlgebraic ℚ (x / y) := by
  rw [div_eq_mul_inv]
  exact hx.mul (IsAlgebraic.inv_iff.mpr hy)

def AlgebraicParts (z : ℂ) : Prop := IsAlgebraic ℚ z.re ∧ IsAlgebraic ℚ z.im

theorem AlgebraicParts.real {x : ℝ} (hx : IsAlgebraic ℚ x) : AlgebraicParts (x : ℂ) :=
  ⟨hx, isAlgebraic_zero⟩

theorem AlgebraicParts.add {z w : ℂ} (hz : AlgebraicParts z) (hw : AlgebraicParts w) :
    AlgebraicParts (z + w) := ⟨hz.1.add hw.1, hz.2.add hw.2⟩

theorem AlgebraicParts.sub {z w : ℂ} (hz : AlgebraicParts z) (hw : AlgebraicParts w) :
    AlgebraicParts (z - w) := ⟨hz.1.sub hw.1, hz.2.sub hw.2⟩

theorem AlgebraicParts.mul {z w : ℂ} (hz : AlgebraicParts z) (hw : AlgebraicParts w) :
    AlgebraicParts (z * w) :=
  ⟨(hz.1.mul hw.1).sub (hz.2.mul hw.2), (hz.1.mul hw.2).add (hz.2.mul hw.1)⟩

theorem AlgebraicParts.conj {z : ℂ} (hz : AlgebraicParts z) :
    AlgebraicParts ((starRingEnd ℂ) z) := ⟨hz.1, hz.2.neg⟩

theorem AlgebraicParts.inv {z : ℂ} (hz : AlgebraicParts z) : AlgebraicParts z⁻¹ := by
  have hn : IsAlgebraic ℚ (normSq z) := (hz.1.mul hz.1).add (hz.2.mul hz.2)
  exact ⟨by simpa only [inv_re] using algebraic_div hz.1 hn,
    by simpa only [inv_im] using algebraic_div hz.2.neg hn⟩

theorem AlgebraicParts.div {z w : ℂ} (hz : AlgebraicParts z) (hw : AlgebraicParts w) :
    AlgebraicParts (z / w) := by rw [div_eq_mul_inv]; exact hz.mul hw.inv

theorem AlgebraicParts.pow {z : ℂ} (hz : AlgebraicParts z) (k : ℕ) :
    AlgebraicParts (z ^ k) := by
  induction k with
  | zero => simpa using (AlgebraicParts.real (isAlgebraic_one : IsAlgebraic ℚ (1 : ℝ)))
  | succ k ih => rw [pow_succ]; exact ih.mul hz

theorem algebraicParts_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (hf : ∀ i ∈ s, AlgebraicParts (f i)) : AlgebraicParts (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (AlgebraicParts.real (isAlgebraic_zero : IsAlgebraic ℚ (0 : ℝ)))
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (by simp)).add (ih (fun j hj => hf j (by simp [hj])))

theorem algebraicParts_unit (q : ℚ) :
    AlgebraicParts (LensClosure.unit ((q : ℝ) * Real.pi)) := by
  simpa only [AlgebraicParts, LensClosure.unit_re, LensClosure.unit_im] using
    RationalConfiguration.rational_pi_coefficients_algebraic q

theorem algebraicParts_root (n : ℕ) : AlgebraicParts (LocalPhase.regularRoot n) := by
  have he : ((2 / (n : ℚ) : ℚ) : ℝ) * Real.pi = 2 * Real.pi / n := by push_cast; ring
  simpa only [LensClosure.unit, he, LocalPhase.regularRoot] using algebraicParts_unit (2 / n)

theorem algebraicParts_frame (n : ℕ) (j : Fin n) : AlgebraicParts (frame n j) := by
  have he : (((1 : ℚ) / n : ℚ) : ℝ) * Real.pi = 1 * Real.pi / n := by push_cast; ring
  have hp : AlgebraicParts (LocalPhase.phase n 1) := by
    simpa only [LensClosure.unit, he, LocalPhase.phase, Nat.cast_one] using
      algebraicParts_unit (1 / n)
  exact hp.mul ((algebraicParts_root n).pow (j.val * 1))

theorem firstCoefficient_algebraic {n : ℕ} (q : Fin n → ℝ)
    (hq : ∀ j, IsAlgebraic ℚ (q j)) : AlgebraicParts (firstCoefficient q) := by
  apply AlgebraicParts.div
  · exact algebraicParts_sum _ _ (fun j _ => (AlgebraicParts.real (hq j)).mul
      (algebraicParts_frame n j).conj)
  · exact AlgebraicParts.real (isAlgebraic_natCast n)

theorem J_algebraic {n : ℕ} (q : Fin n → ℝ)
    (hq : ∀ j, IsAlgebraic ℚ (q j)) (j : Fin n) : IsAlgebraic ℚ (EdgeCoordinates.J q j) :=
  (isAlgebraic_natCast 2).mul ((firstCoefficient_algebraic q hq).mul
    (algebraicParts_frame n j)).2

theorem epsilon_algebraic (n : ℕ) : IsAlgebraic ℚ (FixedSchurData.epsilon n) := by
  have hs := (RationalConfiguration.rational_pi_coefficients_algebraic (1 / n)).2
  have he : (((1 : ℚ) / n : ℚ) : ℝ) * Real.pi = Real.pi / n := by push_cast; ring
  rw [he] at hs
  exact algebraic_div ((isAlgebraic_natCast 2).mul hs) (isAlgebraic_natCast n)

theorem canonicalLift_algebraic {n : ℕ} (q : Fin n → ℝ)
    (hq : ∀ j, IsAlgebraic ℚ (q j)) (j : Fin n) : AlgebraicParts (canonicalLift q j) := by
  have hd (j : Fin n) : AlgebraicParts (increment q j) := by
    rw [increment_polynomial]
    exact (AlgebraicParts.real (epsilon_algebraic n)).mul
      (((algebraicParts_frame n j).mul (AlgebraicParts.real (hq j))).add
        ((firstCoefficient_algebraic q hq).mul ((algebraicParts_frame n j).pow 2)) |>.sub
          (firstCoefficient_algebraic q hq).conj)
  have hc (p : Fin n) : AlgebraicParts (coefficient (increment q) p) :=
    (algebraicParts_sum _ _ (fun k _ => (hd k).mul
      ((algebraicParts_root n).pow (k.val * p.val)).conj)).div
        (AlgebraicParts.real (isAlgebraic_natCast n))
  apply algebraicParts_sum
  intro p _
  apply AlgebraicParts.mul
  · unfold integralCoefficients
    split_ifs
    · exact AlgebraicParts.real isAlgebraic_zero
    · exact (hc p).div (((algebraicParts_root n).pow p.val).sub
        (AlgebraicParts.real isAlgebraic_one))
  · exact (algebraicParts_root n).pow (j.val * p.val)

end
end StructuralNote.FixedSchurAlgebraicData
