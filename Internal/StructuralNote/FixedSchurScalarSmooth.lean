import StructuralNote.FixedSchurScalarRoot

/-! Smoothness of the positive scalar Schur branch on its open radicand domain. -/

namespace StructuralNote.FixedSchurScalarSmooth

open StructuralNote.FixedSchurScalarRoot
open scoped ContDiff
noncomputable section

private theorem sign_sq {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : σ ^ 2 = 1 := by
  rcases hσ with rfl | rfl <;> norm_num

theorem rootValue_hasDerivAt {σ ε X Y p : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hε : ε ≠ 0) (hz : |Y + σ * ε * p| < 2) :
    HasDerivAt (fun t : ℝ => rootValue σ ε X Y t)
      (-(Y + σ * ε * p) / Real.sqrt (4 - (Y + σ * ε * p) ^ 2)) p := by
  have hrad : 0 < 4 - (Y + σ * ε * p) ^ 2 := by
    have hz' := abs_lt.mp hz
    nlinarith
  have hσsq := sign_sq hσ
  have hzfun : HasDerivAt (fun t : ℝ => Y + σ * ε * t) (σ * ε) p := by
    have h := (hasDerivAt_const p Y).add
      ((hasDerivAt_id p).const_mul (σ * ε))
    exact (h.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun t => by
        simp only [Pi.add_apply, id_eq]))).congr_deriv (by ring)
  have hradfun : HasDerivAt (fun t : ℝ => 4 - (Y + σ * ε * t) ^ 2)
      (-2 * (Y + σ * ε * p) * (σ * ε)) p := by
    have h := ((hzfun.pow 2).const_mul (-1)).const_add 4
    exact (h.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun t => by
        simp only [Pi.pow_apply]
        ring))).congr_deriv (by ring)
  have hsqrt := hradfun.sqrt (ne_of_gt hrad)
  have hroot := (hsqrt.sub_const X).const_mul (σ / ε)
  have hsqrtpos : 0 < Real.sqrt (4 - (Y + σ * ε * p) ^ 2) := Real.sqrt_pos.mpr hrad
  apply (hroot.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun t => by
        unfold rootValue
        rfl))).congr_deriv
  · field_simp [hε, ne_of_gt hsqrtpos]
    rw [hσsq]
    ring

theorem rootValue_contDiffAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ∞ω} {σ ε : ℝ} {X Y p : E → ℝ} {x : E}
    (hX : ContDiffAt ℝ k X x) (hY : ContDiffAt ℝ k Y x)
    (hp : ContDiffAt ℝ k p x)
    (hrad : 0 < 4 - (Y x + σ * ε * p x) ^ 2) :
    ContDiffAt ℝ k (fun y => rootValue σ ε (X y) (Y y) (p y)) x := by
  have hzfun : ContDiffAt ℝ k (fun y => Y y + σ * ε * p y) x := by
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
      hY.add (hp.const_smul (σ * ε))
  have hsqrt : ContDiffAt ℝ k
      (fun y => Real.sqrt (4 - (Y y + σ * ε * p y) ^ 2)) x := by
    apply (contDiffAt_const.sub (hzfun.pow 2)).sqrt
    exact ne_of_gt hrad
  simpa only [rootValue, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using
    (hsqrt.sub hX).const_smul (σ / ε)

end
end StructuralNote.FixedSchurScalarSmooth
