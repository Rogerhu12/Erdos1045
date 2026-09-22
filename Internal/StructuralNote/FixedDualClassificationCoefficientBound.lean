import StructuralNote.FixedDualClassificationCosineNorm

/-! Sharp bounds for actual Fourier coefficients of bounded real profiles. -/

namespace StructuralNote.FixedDualClassificationCoefficientBound

open Real MeasureTheory Set
open FixedDualClassificationStep FixedDualClassificationCosineNorm
open FixedDualClassificationMultiplierLimit
open Erdos1045.EventualExact Erdos1045.EventualExact.FiniteBox
noncomputable section

def coefficient (f : ℝ → ℝ) (p : ℤ) : ℂ :=
  (∫ t in 0..2 * Real.pi, (f t : ℂ) * oscillation (-p) t) / (2 * Real.pi)

theorem bounded_intervalIntegrable {f : ℝ → ℝ} (hf : Measurable f)
    {A : ℝ} (hbox : ∀ t, |f t| ≤ A) (a b : ℝ) :
    IntervalIntegrable f volume a b := by
  constructor <;> exact (memLp_one_iff_integrable.mp
    (MemLp.of_bound hf.aestronglyMeasurable A
      (Filter.Eventually.of_forall (fun t => by simpa only [Real.norm_eq_abs] using hbox t))))

theorem coefficient_phase {f : ℝ → ℝ} (hf : Measurable f)
    {A : ℝ} (hbox : ∀ t, |f t| ≤ A) (p : ℤ) (θ : ℝ) :
    (oscillation (-1) θ * coefficient f p).re =
      (∫ t in 0..2 * Real.pi, f t * cos ((p : ℝ) * t + θ)) / (2 * Real.pi) := by
  have hir := bounded_intervalIntegrable hf hbox 0 (2 * Real.pi)
  have hic : IntervalIntegrable (fun t => (f t : ℂ)) volume 0 (2 * Real.pi) :=
    ⟨hir.1.ofReal, hir.2.ofReal⟩
  have hi := hic.mul_continuousOn
    (oscillation_continuous (-(p : ℝ))).continuousOn
  have hie := hi.const_mul (oscillation (-1) θ)
  have hre := intervalIntegral.intervalIntegral_re hie
  change (∫ t in 0..2 * Real.pi,
      (oscillation (-1) θ * ((f t : ℂ) * oscillation (-p) t)).re) =
    (∫ t in 0..2 * Real.pi, oscillation (-1) θ * ((f t : ℂ) * oscillation (-p) t)).re at hre
  rw [coefficient, ← mul_div_assoc, ← intervalIntegral.integral_const_mul,
    ← Complex.ofReal_ofNat 2, ← Complex.ofReal_mul,
    Complex.div_ofReal_re, ← hre]
  congr 2
  funext t
  have he : oscillation (-1) θ * ((f t : ℂ) * oscillation (-(p : ℝ)) t) =
      (f t : ℂ) * oscillation (-1) ((p : ℝ) * t + θ) := by
    unfold oscillation
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [he]
  simp only [oscillation, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re, neg_one_mul, cos_neg]

theorem coefficient_norm_le {f : ℝ → ℝ} (hf : Measurable f)
    {A : ℝ} (hbox : ∀ t, |f t| ≤ A) {p : ℕ} (hp : 0 < p) :
    ‖coefficient f p‖ ≤ 2 * A / Real.pi := by
  have h := coefficient_phase hf hbox (p : ℤ) (coefficient f p).arg
  rw [phase_align, Complex.ofReal_re] at h
  rw [h]
  have hc : Continuous (fun t : ℝ => cos ((p : ℝ) * t + (coefficient f p).arg)) := by fun_prop
  have hi := (bounded_intervalIntegrable hf hbox 0 (2 * Real.pi)).mul_continuousOn hc.continuousOn
  have hib : IntervalIntegrable (fun t => A * |cos ((p : ℝ) * t + (coefficient f p).arg)|)
      volume 0 (2 * Real.pi) := (hc.abs.intervalIntegrable 0 (2 * Real.pi)).const_mul A
  have hb := intervalIntegral.integral_mono_on (by positivity : (0 : ℝ) ≤ 2 * Real.pi) hi hib
    (fun t _ => (le_abs_self (f t * cos ((p : ℝ) * t + (coefficient f p).arg))).trans
      (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hbox t) (abs_nonneg _)))
  rw [intervalIntegral.integral_const_mul, abs_cos_integral_affine hp] at hb
  calc
    _ ≤ (A * 4) / (2 * Real.pi) := div_le_div_of_nonneg_right hb (by positivity)
    _ = _ := by ring

theorem stepProfile_normalized_bound {m : ℕ} (hm : 0 < m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ Q hm) (t : ℝ) :
    |stepProfile q (profileScale (2 * m)) t| ≤ Real.pi / 2 := by
  have hA := amplitude_pos (n := 2 * m) (by omega)
  have hs : 0 ≤ profileScale (2 * m) := by unfold profileScale; positivity
  have h := stepProfile_bound q (profileScale (2 * m)) (amplitude (2 * m)) hA.le hq.2 t
  rw [abs_of_nonneg hs, profileScale, div_mul_cancel₀ _ hA.ne'] at h
  exact h

theorem normalized_coefficient_le_one {m : ℕ} (hm : 0 < m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ Q hm) {p : ℕ} (hp : 0 < p) :
    ‖profileCoefficient (stepProfile q (profileScale (2 * m))) p‖ ≤ 1 := by
  rw [profileCoefficient_eq_interval (by omega)]
  have h := coefficient_norm_le (stepProfile_measurable q (profileScale (2 * m)))
    (stepProfile_normalized_bound hm q hq) hp
  simpa only [coefficient, show 2 * (Real.pi / 2) / Real.pi = 1 by field_simp] using h

end
end StructuralNote.FixedDualClassificationCoefficientBound
