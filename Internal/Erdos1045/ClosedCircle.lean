import Erdos1045.CircleMatrix
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Analysis.Complex.Trigonometric

open scoped BigOperators

namespace Erdos1045.CircleMatrix

open Configuration MatrixDefect
noncomputable section

theorem vandermonde_detSq {n : ℕ} (z : Points n) :
    detSq (vandermonde z) = discriminant z := by
  change Complex.normSq (Matrix.vandermonde z).det = _
  rw [Matrix.det_vandermonde]
  simp only [map_prod]
  calc
    (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, Complex.normSq (z j - z i)) =
        ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ‖z j - z i‖ * ‖z i - z j‖ := by
      apply Finset.prod_congr rfl
      intro i hi
      apply Finset.prod_congr rfl
      intro j hj
      rw [Complex.normSq_eq_norm_sq, norm_sub_rev (z i) (z j), pow_two]
    _ = ∏ i : Fin n, ∏ j ∈ {i}ᶜ, ‖z j - z i‖ :=
      Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag (fun i j => ‖z i - z j‖)
    _ = discriminant z := by
      unfold discriminant
      apply Finset.prod_congr rfl
      intro i hi
      have hs : ({i}ᶜ : Finset (Fin n)) = Finset.univ.erase i := by ext j; simp
      rw [hs]
      apply Finset.prod_congr rfl
      intro j hj
      exact norm_sub_rev _ _

theorem circlePoint_chord (s t : ℝ) :
    ‖circlePoint t - circlePoint s‖ = |2 * Real.sin ((t - s) / 2)| := by
  have hfactor : circlePoint t - circlePoint s =
      circlePoint s * (Complex.exp (Complex.I * ((t - s : ℝ) : ℂ)) - 1) := by
    unfold circlePoint
    rw [mul_sub, ← Complex.exp_add]
    have he : (s : ℂ) * Complex.I + Complex.I * ((t - s : ℝ) : ℂ) =
        (t : ℂ) * Complex.I := by push_cast; ring
    rw [he, mul_one]
  rw [hfactor, norm_mul, circlePoint, Complex.norm_exp_ofReal_mul_I, one_mul,
    Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs]

/-- The two formerly external circle identities, now proved from mathlib. -/
theorem classicalCircleIdentities : ClassicalCircleIdentities :=
  ⟨fun _ z => vandermonde_detSq z, circlePoint_chord⟩

end
end Erdos1045.CircleMatrix
