import AnalyticLaurentModel
import FaberKernelCoefficients
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Actual scalar Taylor series for the differentiated exterior kernel

The numerator coefficients are derived by differentiation of the analytic
Laurent model. Neither kernel series is a hypothesis at the final interface.
-/

namespace ExteriorReduction.FaberKernel

open Complex Filter Metric
open scoped Topology BigOperators

noncomputable section

theorem scalarize_series {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : HasFPowerSeriesAt f p 0) :
    HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ p.coeff) 0 := by
  rw [hasFPowerSeriesAt_iff] at hp ⊢
  simpa only [FormalMultilinearSeries.coeff_ofScalars] using hp

theorem scalar_derivative_series {q : ℂ → ℂ} {a : ℕ → ℂ}
    (hq : HasFPowerSeriesAt q (FormalMultilinearSeries.ofScalars ℂ a) 0) :
    HasFPowerSeriesAt (deriv q)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => (n + 1 : ℕ) * a (n + 1))) 0 := by
  obtain ⟨r, hr⟩ := hq
  have hs := scalarize_series
    ((ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).comp_hasFPowerSeriesOnBall hr.fderiv).hasFPowerSeriesAt
  convert hs using 1
  · rfl
  · congr 1
    funext n
    change ((n + 1 : ℕ) : ℂ) * a (n + 1) =
      (FormalMultilinearSeries.ofScalars ℂ a).derivSeries.coeff n 1
    simp only [FormalMultilinearSeries.derivSeries_coeff_one,
      FormalMultilinearSeries.coeff_ofScalars, nsmul_eq_mul]

def linearCoefficients (t : ℂ) (n : ℕ) : ℂ := if n = 1 then t else 0

theorem scalar_linear_series (t : ℂ) :
    HasFPowerSeriesAt (fun z : ℂ => t * z)
      (FormalMultilinearSeries.ofScalars ℂ (linearCoefficients t)) 0 := by
  rw [hasFPowerSeriesAt_iff]
  refine Filter.Eventually.of_forall fun z => ?_
  simpa +contextual [linearCoefficients, mul_ite, mul_comm] using hasSum_ite_eq (1 : ℕ) (t * z)

theorem scalar_add_series {f g : ℂ → ℂ} {a b : ℕ → ℂ}
    (hf : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ a) 0)
    (hg : HasFPowerSeriesAt g (FormalMultilinearSeries.ofScalars ℂ b) 0) :
    HasFPowerSeriesAt (fun z => f z + g z)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => a n + b n)) 0 := by
  simpa only [← FormalMultilinearSeries.ofScalars_add, Pi.add_def] using hf.add hg

theorem scalar_sub_series {f g : ℂ → ℂ} {a b : ℕ → ℂ}
    (hf : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ a) 0)
    (hg : HasFPowerSeriesAt g (FormalMultilinearSeries.ofScalars ℂ b) 0) :
    HasFPowerSeriesAt (fun z => f z - g z)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => a n - b n)) 0 := by
  simpa only [← FormalMultilinearSeries.ofScalars_sub, Pi.sub_def] using hf.sub hg

theorem scalar_div_series {f : ℂ → ℂ} {a : ℕ → ℂ}
    (hf : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ a) 0) (c : ℂ) :
    HasFPowerSeriesAt (fun z => f z / c)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => a n / c)) 0 := by
  simpa only [← FormalMultilinearSeries.ofScalars_smul, Pi.smul_def, smul_eq_mul,
    div_eq_mul_inv, mul_comm] using hf.const_smul (c := c⁻¹)

theorem convolution_linear_succ (t : ℂ) (a : ℕ → ℂ) (n : ℕ) :
    convolution (linearCoefficients t) a (n + 1) = t * a n := by
  simp [convolution, linearCoefficients, ite_mul]

def laurentCoefficients (a : ℕ → ℂ) (m : ℕ) : ℂ :=
  if m = 0 then 0 else a (m + 1) / a 0

@[simp] theorem laurentCoefficients_zero (a : ℕ → ℂ) : laurentCoefficients a 0 = 0 := by
  simp [laurentCoefficients]

@[simp] theorem laurentCoefficients_succ (a : ℕ → ℂ) (m : ℕ) :
    laurentCoefficients a (m + 1) = a (m + 2) / a 0 := by
  simp [laurentCoefficients, Nat.add_assoc]

def laurentVariable (a : ℕ → ℂ) (A x : ℂ) : ℂ := (x - A - a 1) / a 0

def kernelDenominator (q : ℂ → ℂ) (A x z : ℂ) : ℂ :=
  (q z + (A - x) * z) / q 0

theorem scalar_constant_coefficient {q : ℂ → ℂ} {a : ℕ → ℂ}
    (hq : HasFPowerSeriesAt q (FormalMultilinearSeries.ofScalars ℂ a) 0) : a 0 = q 0 := by
  simpa using hq.coeff_zero (fun _ => 1)

theorem kernel_denominator_series {q : ℂ → ℂ} {a : ℕ → ℂ}
    (hq : HasFPowerSeriesAt q (FormalMultilinearSeries.ofScalars ℂ a) 0)
    (hq0 : q 0 ≠ 0) (A x : ℂ) :
    HasFPowerSeriesAt (kernelDenominator q A x)
      (FormalMultilinearSeries.ofScalars ℂ
        (denominatorCoefficients (laurentCoefficients a) (laurentVariable a A x))) 0 := by
  have hzero := scalar_constant_coefficient hq
  have hs := scalar_div_series (scalar_add_series hq (scalar_linear_series (A - x))) (q 0)
  convert hs using 1
  · rfl
  · congr 1
    funext n
    match n with
    | 0 => simp [denominatorCoefficients, linearCoefficients, hzero, hq0]
    | 1 =>
      simp only [denominatorCoefficients, linearCoefficients, ite_true, laurentVariable, hzero]
      ring
    | n + 2 =>
      simp [denominatorCoefficients, laurentCoefficients, linearCoefficients, hzero,
        show n + 2 ≠ 1 by omega, Nat.add_assoc]

theorem kernel_numerator_series {q : ℂ → ℂ} {a : ℕ → ℂ}
    (hq : HasFPowerSeriesAt q (FormalMultilinearSeries.ofScalars ℂ a) 0)
    (hq0 : q 0 ≠ 0) :
    HasFPowerSeriesAt (modelDerivative q)
      (FormalMultilinearSeries.ofScalars ℂ (numeratorCoefficients (laurentCoefficients a))) 0 := by
  have hid : HasFPowerSeriesAt (fun z : ℂ => z)
      (FormalMultilinearSeries.ofScalars ℂ (linearCoefficients 1)) 0 := by
    simpa only [one_mul] using scalar_linear_series 1
  have hs := scalar_div_series
    (scalar_sub_series hq (scalar_series_product hid (scalar_derivative_series hq))) (q 0)
  have hzero := scalar_constant_coefficient hq
  convert hs using 1
  · rfl
  · congr 1
    funext n
    match n with
    | 0 => simp [numeratorCoefficients, convolution_zero, linearCoefficients, hzero, hq0]
    | 1 => simp [numeratorCoefficients, convolution_linear_succ]
    | n + 2 =>
      rw [show n + 2 = (n + 1) + 1 by omega, convolution_linear_succ]
      simp only [numeratorCoefficients, laurentCoefficients_succ, one_mul, hzero]
      push_cast
      ring

/-- The scalar coefficients are canonical derivatives, independent of any choice
of analytic power-series witness. -/
def taylorCoefficients (q : ℂ → ℂ) (n : ℕ) : ℂ := iteratedDeriv n q 0 / n.factorial

@[simp] theorem taylorCoefficients_zero (q : ℂ → ℂ) : taylorCoefficients q 0 = q 0 := by
  simp [taylorCoefficients]

@[simp] theorem taylorCoefficients_one (q : ℂ → ℂ) : taylorCoefficients q 1 = deriv q 0 := by
  simp [taylorCoefficients]

theorem taylorCoefficients_series {q : ℂ → ℂ} (hq : AnalyticAt ℂ q 0) :
    HasFPowerSeriesAt q (FormalMultilinearSeries.ofScalars ℂ (taylorCoefficients q)) 0 :=
  hq.hasFPowerSeriesAt

/-- The Faber bound now needs only the actual analytic Laurent model and the
holomorphic positive-real-part quotient kernel. Its two series are proved above. -/
theorem faber_bound_of_laurent_kernel {q : ℂ → ℂ} (hq : AnalyticAt ℂ q 0)
    (hq0 : q 0 ≠ 0) (A x : ℂ)
    (hhol : DifferentiableOn ℂ
      (fun z => modelDerivative q z / kernelDenominator q A x z) (ball 0 1))
    (hpos : ∀ z ∈ ball (0 : ℂ) 1,
      0 ≤ (modelDerivative q z / kernelDenominator q A x z).re)
    (k : ℕ) (hk : k ≠ 0) :
    ‖value (laurentCoefficients (taylorCoefficients q))
      (laurentVariable (taylorCoefficients q) A x) k‖ ≤ 2 := by
  exact faber_bound_of_positive_quotient _ _
    (kernel_denominator_series (taylorCoefficients_series hq) hq0 A x)
    (kernel_numerator_series (taylorCoefficients_series hq) hq0) hhol hpos k hk

theorem kernel_quotient_eq {q : ℂ → ℂ} (hq0 : q 0 ≠ 0) (A x z : ℂ) :
    modelDerivative q z / kernelDenominator q A x z =
      derivativeNumerator q z / (q z + (A - x) * z) := by
  simp only [modelDerivative, kernelDenominator]
  field_simp

/-- A public version with no formal-series or kernel-holomorphicity assumptions:
ordinary holomorphicity of q and exclusion of zeros of the displayed denominator
give the holomorphic kernel; positivity is its remaining geometric property. -/
theorem faber_bound_of_positive_laurent_model {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (A x : ℂ)
    (hne : ∀ z ∈ ball (0 : ℂ) 1, q z + (A - x) * z ≠ 0)
    (hpos : ∀ z ∈ ball (0 : ℂ) 1,
      0 ≤ (derivativeNumerator q z / (q z + (A - x) * z)).re)
    (k : ℕ) (hk : k ≠ 0) :
    ‖value (laurentCoefficients (taylorCoefficients q))
      (laurentVariable (taylorCoefficients q) A x) k‖ ≤ 2 := by
  have hq0 : q 0 ≠ 0 := by simpa using hne 0 (by simp)
  have hquot : DifferentiableOn ℂ
      (fun z => derivativeNumerator q z / (q z + (A - x) * z)) (ball 0 1) :=
    ((derivativeNumerator_analytic hq).div
      (hq.add (analyticOnNhd_const.mul analyticOnNhd_id)) hne).differentiableOn
  apply faber_bound_of_laurent_kernel (hq 0 (by simp)) hq0 A x
    (by simpa only [kernel_quotient_eq hq0] using hquot)
    (by simpa only [kernel_quotient_eq hq0] using hpos) k hk

#print axioms scalar_derivative_series
#print axioms kernel_denominator_series
#print axioms kernel_numerator_series
#print axioms faber_bound_of_laurent_kernel
#print axioms faber_bound_of_positive_laurent_model

end
end ExteriorReduction.FaberKernel
