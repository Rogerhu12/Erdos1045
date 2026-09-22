import StructuralNote.FixedDualClassificationParseval

/-! Parseval for the actual bilinear integral, rather than just its square
mass. This is the bridge required for a singular convolution kernel. -/

namespace StructuralNote.FixedDualClassificationPairing

open Real Complex MeasureTheory Set AddCircle
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section

theorem hasSum_prod_fourierCoeff {T : ℝ} [Fact (0 < T)]
    (f g : Lp ℂ 2 (@haarAddCircle T _)) :
    HasSum (fun i => conj (fourierCoeff f i) * fourierCoeff g i)
      (∫ t, conj (f t) * g t ∂haarAddCircle) := by
  simp_rw [mul_comm (conj _)]
  refine HasSum.congr_fun (fourierBasis.hasSum_inner_mul_inner f g) (fun i => ?_)
  simp only [← fourierBasis_repr, HilbertBasis.repr_apply_apply, inner_conj_symm,
    mul_comm (inner ℂ f _)]

theorem hasSum_prod_fourierCoeffOn {a b : ℝ} {f g : ℝ → ℂ} (hab : a < b)
    (hf : MemLp f 2 (volume.restrict (Ioc a b)))
    (hg : MemLp g 2 (volume.restrict (Ioc a b))) :
    HasSum (fun i => conj (fourierCoeffOn hab f i) * fourierCoeffOn hab g i)
      ((b - a)⁻¹ • ∫ x in a..b, conj (f x) * g x) := by
  have := Fact.mk (by linarith : 0 < b - a)
  rw [← add_sub_cancel a b] at hf hg
  have hfl := hf.memLp_liftIoc.haarAddCircle
  have hgl := hg.memLp_liftIoc.haarAddCircle
  convert hasSum_prod_fourierCoeff hfl.toLp hgl.toLp using 1
  · funext i
    simp only [fourierCoeff_congr_ae hfl.coeFn_toLp,
      fourierCoeff_congr_ae hgl.coeFn_toLp, fourierCoeff_liftIoc_eq, add_sub_cancel]
  · nth_rw 2 [← add_sub_cancel a b]
    rw [← AddCircle.integral_liftIoc_eq_intervalIntegral]
    rw [← AddCircle.integral_haarAddCircle]
    apply integral_congr_ae
    filter_upwards [hfl.coeFn_toLp, hgl.coeFn_toLp] with x hfx hgx
    simp only [hfx, hgx]
    rfl

end
end StructuralNote.FixedDualClassificationPairing
