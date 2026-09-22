import Erdos1045.ExteriorClassical
import Erdos1045.ClosedCircle
import Mathlib.LinearAlgebra.Lagrange

namespace Erdos1045.ExteriorClassical

open scoped BigOperators
open Configuration CircleMatrix MatrixDefect
noncomputable section

theorem lagrange_power_sum {n : ℕ} (z : Points n) (hz : Function.Injective z)
    (x : ℂ) (k : Fin n) :
    (∑ j : Fin n, (Lagrange.basis Finset.univ z j).eval x * z j ^ (k : ℕ)) =
      x ^ (k : ℕ) := by
  have hP : (Polynomial.X ^ (k : ℕ) : Polynomial ℂ).degree <
      ((Finset.univ : Finset (Fin n)).card : WithBot ℕ) := by
    simp
  have h := (Lagrange.eq_interpolate (s := Finset.univ) (v := z) hz.injOn hP).symm
  have he := congrArg (fun p : Polynomial ℂ => p.eval x) h
  simpa [Lagrange.interpolate_apply, Polynomial.eval_finsetSum, mul_comm] using he

theorem vandermonde_replace_det {n : ℕ} (z : Points n) (hz : Function.Injective z)
    (i : Fin n) (x : ℂ) :
    (vandermonde (Function.update z i x)).det =
      (Lagrange.basis Finset.univ z i).eval x * (vandermonde z).det := by
  have hrow : (fun k : Fin n => x ^ (k : ℕ)) =
      ∑ j : Fin n, (Lagrange.basis Finset.univ z j).eval x • (vandermonde z) j := by
    funext k
    simpa [vandermonde] using (lagrange_power_sum z hz x k).symm
  have hmat : vandermonde (Function.update z i x) =
      (vandermonde z).updateRow i (fun k => x ^ (k : ℕ)) := by
    ext j k
    by_cases h : j = i
    · subst j
      simp [vandermonde]
    · change (Function.update z i x j) ^ (k : ℕ) =
        (Function.update (fun j k : Fin n => z j ^ (k : ℕ)) i
          (fun k => x ^ (k : ℕ)) j) k
      rw [Function.update_of_ne h, Function.update_of_ne h]
  rw [hmat, hrow, Matrix.det_updateRow_sum]
  rfl

/-- Fekete's bounded interpolation polynomials follow from the actual
single-node determinant comparison, with no separate analytic input. -/
theorem fekete_interpolation_proved (n : ℕ) (_hn : 2 ≤ n) (z : Points n)
    (hz : Function.Injective z) (hf : Fekete z) :
    ∃ p : Fin n → Polynomial ℂ,
      (∀ i, (p i).natDegree ≤ n - 1) ∧
      (∀ i j, (p i).eval (z j) = if i = j then 1 else 0) ∧
      ∀ i x, x ∈ hull z → ‖(p i).eval x‖ ≤ 1 := by
  refine ⟨fun i => Lagrange.basis Finset.univ z i, ?_, ?_, ?_⟩
  · intro i
    simp [Lagrange.natDegree_basis hz.injOn (Finset.mem_univ i)]
  · intro i j
    by_cases h : i = j
    · subst j
      simp [Lagrange.eval_basis_self hz.injOn]
    · simp [h, Lagrange.eval_basis_of_ne h (Finset.mem_univ j)]
  · intro i x hx
    have hsub : Set.range (Function.update z i x) ⊆ hull z := by
      rintro y ⟨j, rfl⟩
      by_cases h : j = i
      · subst j
        simpa using hx
      · simpa [Function.update_of_ne h, hull] using
          (subset_convexHull ℝ (Set.range z) (Set.mem_range_self j))
    have hbound := hf (Function.update z i x) hsub
    rw [← vandermonde_detSq, ← vandermonde_detSq, detSq,
      vandermonde_replace_det z hz i x, map_mul] at hbound
    simp only [detSq] at hbound
    have hpositive : 0 < Complex.normSq (vandermonde z).det := by
      change 0 < detSq (vandermonde z)
      rw [vandermonde_detSq]
      exact discriminant_pos z hz
    have hsq : Complex.normSq ((Lagrange.basis Finset.univ z i).eval x) ≤ 1 := by
      nlinarith
    rw [Complex.normSq_eq_norm_sq] at hsq
    nlinarith [norm_nonneg ((Lagrange.basis Finset.univ z i).eval x)]

end
end Erdos1045.ExteriorClassical
