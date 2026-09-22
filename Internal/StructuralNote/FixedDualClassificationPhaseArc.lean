import StructuralNote.FixedDualClassificationArc
import StructuralNote.FixedDualClassificationCircleShift
import StructuralNote.FixedDualClassificationCoefficientBound
import StructuralNote.FixedDualClassificationStepPotential

/-! Exact phase transport for the third Fourier coefficient of a measurable
antiperiodic circle profile.  The moment signs below follow the convention
`fourierCoeff = integral against exp (- I * p * t)`: the imaginary part is
the negative sine moment. -/

namespace StructuralNote.FixedDualClassificationPhaseArc

open Real Set MeasureTheory AddCircle
open FixedDualClassificationStep FixedDualClassificationFunctional
open FixedDualClassificationOddSpectrum FixedDualClassificationCircleShift
open FixedDualClassificationArc FixedDualClassificationCoefficientBound
open scoped ComplexConjugate
noncomputable section

local instance period_pos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

def thirdCoefficient (F : Torus → ℝ) : ℂ :=
  fourierCoeff (fun x : Torus => (F x : ℂ)) 3

def thirdPhase (F : Torus → ℝ) (θ : ℝ) : ℝ :=
  3 * θ + (thirdCoefficient F).arg

private theorem local_interval_integrable {f : ℝ → ℝ} (hf : Measurable f)
    (hbox : ∀ u ∈ Icc 0 Real.pi, |f u| ≤ Real.pi / 2) :
    IntervalIntegrable f volume 0 Real.pi := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le pi_pos.le]
  have hunit : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc 0 Real.pi) volume :=
    continuous_const.integrableOn_Icc
  have hbound : ∀ᵐ u ∂volume.restrict (Icc 0 Real.pi),
      ‖f u‖ ≤ Real.pi / 2 := by
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with u hu
    simpa only [Real.norm_eq_abs] using hbox u hu
  change Integrable f (volume.restrict (Icc 0 Real.pi))
  simpa only [mul_one] using hunit.bdd_mul hf.aestronglyMeasurable hbound

private theorem oddCoefficient_one_re {f : ℝ → ℝ} (hf : Measurable f)
    (hbox : ∀ u ∈ Icc 0 Real.pi, |f u| ≤ Real.pi / 2) :
    (oddCoefficient f (1 : ℤ)).re = cosineMoment f := by
  rw [oddCoefficient_integral]
  have hfreq : -(2 * ((1 : ℤ) : ℝ) + 1) = (-3 : ℝ) := by norm_num
  rw [hfreq]
  have hfi := local_interval_integrable hf hbox
  have hfc : IntervalIntegrable (fun u : ℝ => (f u : ℂ)) volume 0 Real.pi :=
    ⟨hfi.1.ofReal, hfi.2.ofReal⟩
  have hi := hfc.mul_continuousOn
    (oscillation_continuous (-(3 : ℝ))).continuousOn
  have hre := intervalIntegral.intervalIntegral_re hi
  have hre' :
      (∫ u in 0..Real.pi, (f u : ℂ) * oscillation (-3) u).re =
        ∫ u in 0..Real.pi, f u * cos (3 * u) := by
    calc
      (∫ u in 0..Real.pi, (f u : ℂ) * oscillation (-3) u).re =
          ∫ u in 0..Real.pi, ((f u : ℂ) * oscillation (-3) u).re := hre.symm
      _ = ∫ u in 0..Real.pi, f u * cos (3 * u) := by
        apply intervalIntegral.integral_congr
        intro u hu
        simp only [oscillation, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero,
          Complex.exp_ofReal_mul_I_re]
        rw [show (-3 : ℝ) * u = -(3 * u) by ring, cos_neg]
  rw [Complex.div_ofReal_re, hre']
  exact (by rfl : (∫ u in 0..Real.pi, f u * cos (3 * u)) / Real.pi = cosineMoment f)

private theorem oddCoefficient_one_im {f : ℝ → ℝ} (hf : Measurable f)
    (hbox : ∀ u ∈ Icc 0 Real.pi, |f u| ≤ Real.pi / 2) :
    (oddCoefficient f (1 : ℤ)).im = -sineMoment f := by
  rw [oddCoefficient_integral]
  have hfreq : -(2 * ((1 : ℤ) : ℝ) + 1) = (-3 : ℝ) := by norm_num
  rw [hfreq]
  have hfi := local_interval_integrable hf hbox
  have hfc : IntervalIntegrable (fun u : ℝ => (f u : ℂ)) volume 0 Real.pi :=
    ⟨hfi.1.ofReal, hfi.2.ofReal⟩
  have hi := hfc.mul_continuousOn
    (oscillation_continuous (-(3 : ℝ))).continuousOn
  have him := intervalIntegral.intervalIntegral_im hi
  have him' :
      (∫ u in 0..Real.pi, (f u : ℂ) * oscillation (-3) u).im =
        ∫ u in 0..Real.pi, -(f u * sin (3 * u)) := by
    calc
      (∫ u in 0..Real.pi, (f u : ℂ) * oscillation (-3) u).im =
          ∫ u in 0..Real.pi, ((f u : ℂ) * oscillation (-3) u).im := him.symm
      _ = ∫ u in 0..Real.pi, -(f u * sin (3 * u)) := by
        apply intervalIntegral.integral_congr
        intro u hu
        simp only [oscillation, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, add_zero,
          Complex.exp_ofReal_mul_I_im]
        rw [show (-3 : ℝ) * u = -(3 * u) by ring, sin_neg]
        ring
  rw [Complex.div_ofReal_im, him']
  rw [intervalIntegral.integral_neg]
  unfold sineMoment
  ring

theorem reflected_third_moments {F : Torus → ℝ} (hF : Measurable F)
    (hbox : ∀ x, |F x| ≤ Real.pi / 2)
    (hanti : ∀ x, F (x + (Real.pi : ℝ)) = -F x) (θ : ℝ) :
    cosineMoment (reflected F θ) =
        ‖thirdCoefficient F‖ * cos (thirdPhase F θ) ∧
      sineMoment (reflected F θ) =
        ‖thirdCoefficient F‖ * sin (thirdPhase F θ) := by
  have hbox' : ∀ u ∈ Icc 0 Real.pi, |reflected F θ u| ≤ Real.pi / 2 := by
    intro u hu
    exact reflected_bound hbox θ u
  have hmeas : Measurable (reflected F θ) := reflected_measurable hF θ
  have hcoeff := reflected_oddCoefficient hF hbox hanti θ (1 : ℤ)
  have hcoeff' : oddCoefficient (reflected F θ) (1 : ℤ) =
      oscillation (-3) θ * conj (thirdCoefficient F) := by
    norm_num [thirdCoefficient] at hcoeff ⊢
    exact hcoeff
  have hre := oddCoefficient_one_re hmeas hbox'
  have him := oddCoefficient_one_im hmeas hbox'
  have hc : thirdCoefficient F =
      (‖thirdCoefficient F‖ : ℂ) * oscillation (1 : ℝ) (thirdCoefficient F).arg := by
    unfold oscillation
    symm
    simpa only [one_mul] using Complex.norm_mul_exp_arg_mul_I (thirdCoefficient F)
  have hphase : oscillation (-3) θ * conj (thirdCoefficient F) =
      (‖thirdCoefficient F‖ : ℂ) * oscillation (-1) (thirdPhase F θ) := by
    conv_lhs => rw [hc]
    have hconj : conj (oscillation (1 : ℝ) (thirdCoefficient F).arg) =
        oscillation (-1) (thirdCoefficient F).arg := by
      symm
      exact oscillation_neg (1 : ℝ) (thirdCoefficient F).arg
    rw [map_mul, Complex.conj_ofReal, hconj]
    unfold oscillation thirdPhase
    calc
      _ = (‖thirdCoefficient F‖ : ℂ) *
          (Complex.exp (((-3 * θ : ℝ) : ℂ) * Complex.I) *
            Complex.exp (((-1 * (thirdCoefficient F).arg : ℝ) : ℂ) *
              Complex.I)) := by ring
      _ = (‖thirdCoefficient F‖ : ℂ) *
          Complex.exp (((( -3 * θ : ℝ) : ℂ) * Complex.I) +
            (((-1 * (thirdCoefficient F).arg : ℝ) : ℂ) * Complex.I)) := by
        rw [← Complex.exp_add]
      _ = (‖thirdCoefficient F‖ : ℂ) *
          Complex.exp (((-1 * (3 * θ + (thirdCoefficient F).arg) : ℝ) : ℂ) *
            Complex.I) := by
        congr 2
        push_cast
        ring
  have hphase' := hcoeff'.trans hphase
  constructor
  · have hr := congrArg Complex.re hphase'
    calc
      cosineMoment (reflected F θ) = (oddCoefficient (reflected F θ) (1 : ℤ)).re := hre.symm
      _ = ((‖thirdCoefficient F‖ : ℂ) * oscillation (-1) (thirdPhase F θ)).re := hr
      _ = ‖thirdCoefficient F‖ * cos (thirdPhase F θ) := by
        simp only [oscillation, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero,
          Complex.exp_ofReal_mul_I_re, neg_one_mul, cos_neg]
  · have hi := congrArg Complex.im hphase'
    calc
      sineMoment (reflected F θ) = -(oddCoefficient (reflected F θ) (1 : ℤ)).im := by
        linarith [him]
      _ = -((‖thirdCoefficient F‖ : ℂ) * oscillation (-1) (thirdPhase F θ)).im := by
        rw [hi]
      _ = ‖thirdCoefficient F‖ * sin (thirdPhase F θ) := by
        simp only [oscillation, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, add_zero,
          Complex.exp_ofReal_mul_I_im, neg_one_mul, sin_neg]
        ring

end
end StructuralNote.FixedDualClassificationPhaseArc
