import AnalyticLaurentModel
import GeometricFaberKernel

/-! The analytic model gives the actual exterior derivative and kernel. -/

namespace ExteriorReduction

open Complex Set Metric
noncomputable section

theorem hasDerivAt_laurentExterior {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (A : ℂ)
    {w : ℂ} (hw : w ∈ exteriorDisk) :
    HasDerivAt (fun v => A + v * q v⁻¹) (derivativeNumerator q w⁻¹) w := by
  have hw0 : w ≠ 0 := by
    intro he
    have : (1 : ℝ) < 0 := by simpa [exteriorDisk, he] using hw
    norm_num at this
  have hcomp := (hq w⁻¹ (inv_mem_disk_of_exterior hw)).differentiableAt.hasDerivAt.comp w
    (hasDerivAt_inv hw0)
  convert! ((hasDerivAt_id w).mul hcomp).const_add A using 1
  dsimp [derivativeNumerator]
  field_simp
  ring

theorem deriv_laurentExterior {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (A : ℂ)
    {w : ℂ} (hw : w ∈ exteriorDisk) :
    deriv (fun v => A + v * q v⁻¹) w = derivativeNumerator q w⁻¹ :=
  (hasDerivAt_laurentExterior hq A hw).deriv

theorem geometricKernel_eq_exterior {q : ℂ → ℂ} (A x : ℂ)
    {w : ℂ} (hw : w ≠ 0) :
    geometricKernel q A x w⁻¹ =
      w * derivativeNumerator q w⁻¹ / (A + w * q w⁻¹ - x) := by
  unfold geometricKernel
  have he : q w⁻¹ + (A - x) * w⁻¹ = (A + w * q w⁻¹ - x) / w := by
    field_simp
    ring
  rw [he]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

theorem geometricKernel_eq_exterior_derivative {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (A x : ℂ)
    {w : ℂ} (hw : w ∈ exteriorDisk) :
    geometricKernel q A x w⁻¹ =
      w * deriv (fun v => A + v * q v⁻¹) w / (A + w * q w⁻¹ - x) := by
  rw [deriv_laurentExterior hq A hw]
  apply geometricKernel_eq_exterior
  intro he
  have : (1 : ℝ) < 0 := by simpa [exteriorDisk, he] using hw
  norm_num at this

#print axioms hasDerivAt_laurentExterior
#print axioms geometricKernel_eq_exterior_derivative

end
end ExteriorReduction
