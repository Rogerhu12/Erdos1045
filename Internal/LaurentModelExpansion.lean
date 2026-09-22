import FaberKernelGenerating

/-!
# Actual exterior Laurent expansion

The coefficients are canonical Taylor derivatives of the removable model q.
The leading and constant terms are removed explicitly; no boundary convergence
is asserted or used.
-/

namespace ExteriorReduction

open Complex Metric
open FaberKernel
open scoped BigOperators

noncomputable section

def modelLaurentCoefficient (q : ℂ → ℂ) (m : ℕ) : ℂ :=
  if m = 0 then 0 else taylorCoefficients q (m + 1)

@[simp] theorem modelLaurentCoefficient_zero (q : ℂ → ℂ) :
    modelLaurentCoefficient q 0 = 0 := by simp [modelLaurentCoefficient]

@[simp] theorem modelLaurentCoefficient_succ (q : ℂ → ℂ) (m : ℕ) :
    modelLaurentCoefficient q (m + 1) = taylorCoefficients q (m + 2) := by
  simp [modelLaurentCoefficient, Nat.add_assoc]

theorem modelLaurentCoefficient_normalized (q : ℂ → ℂ) (m : ℕ) :
    modelLaurentCoefficient q m / q 0 = laurentCoefficients (taylorCoefficients q) m := by
  simp only [modelLaurentCoefficient, laurentCoefficients, taylorCoefficients_zero]
  split_ifs <;> simp

/-- The absolutely convergent Laurent tail at every exterior point. -/
theorem model_laurent_hasSum {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) {w : ℂ} (hw : w ∈ exteriorDisk) :
    HasSum (fun m => modelLaurentCoefficient q m * (w⁻¹) ^ m)
      (w * q w⁻¹ - q 0 * w - deriv q 0) := by
  have hwne : w ≠ 0 := norm_ne_zero_iff.mp (lt_trans zero_lt_one hw).ne'
  have hs := canonical_taylor_hasSum hq.differentiableOn (inv_mem_disk_of_exterior hw)
  have ht : HasSum (fun n => taylorCoefficients q (n + 2) * (w⁻¹) ^ (n + 2))
      (q w⁻¹ - (q 0 + deriv q 0 * w⁻¹)) := by
    simpa [Finset.sum_range_succ] using (hasSum_nat_add_iff' 2).mpr hs
  have he (n : ℕ) :
      w * (taylorCoefficients q (n + 2) * (w⁻¹) ^ (n + 2)) =
        modelLaurentCoefficient q (n + 1) * (w⁻¹) ^ (n + 1) := by
    rw [modelLaurentCoefficient_succ, show n + 2 = (n + 1) + 1 by omega, pow_succ]
    calc
      _ = taylorCoefficients q (n + 1 + 1) * (w * w⁻¹) * (w⁻¹) ^ (n + 1) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hwne, mul_one]
  have hv : w * (q w⁻¹ - (q 0 + deriv q 0 * w⁻¹)) =
      w * q w⁻¹ - q 0 * w - deriv q 0 := by
    field_simp
    ring
  have hshift : HasSum (fun n => modelLaurentCoefficient q (n + 1) * (w⁻¹) ^ (n + 1))
      (w * q w⁻¹ - q 0 * w - deriv q 0) := by
    simpa only [he, hv] using ht.mul_left w
  apply (hasSum_nat_add_iff' 1).mp
  simpa only [Finset.sum_range_one, modelLaurentCoefficient_zero, zero_mul, sub_zero] using hshift

theorem model_laurent_norm_summable {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) {w : ℂ} (hw : w ∈ exteriorDisk) :
    Summable (fun m => ‖modelLaurentCoefficient q m * (w⁻¹) ^ m‖) :=
  (model_laurent_hasSum hq hw).summable.norm

/-- The leading coefficient is q(0), the constant term is A+q'(0), and the
remaining Laurent coefficients are the actual Taylor coefficients above. -/
theorem model_laurent_expansion {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (A : ℂ) {w : ℂ} (hw : w ∈ exteriorDisk) :
    A + w * q w⁻¹ = q 0 * w + (A + deriv q 0) +
      ∑' m, modelLaurentCoefficient q m * (w⁻¹) ^ m := by
  rw [(model_laurent_hasSum hq hw).tsum_eq]
  ring

#print axioms model_laurent_hasSum
#print axioms model_laurent_expansion
#print axioms modelLaurentCoefficient_normalized

end
end ExteriorReduction
