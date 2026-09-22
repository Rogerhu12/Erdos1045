import StructuralNote.MatchingActivityNonlocal
import StructuralNote.LensIncrementDerivatives
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! Smooth length and direction of the sum of two unsaturated semidiameters. -/

namespace StructuralNote.MatchingActivityRadialPair

open Erdos1045 Erdos1045.EventualExact Complex LensClosure Filter CommonFiberGeometry
open scoped Topology ContDiff
noncomputable section

def pair (φ r₀ r₁ : ℝ) : ℂ := (r₀ : ℂ) * unit (-φ) + (r₁ : ℂ) * unit φ

def length (φ r₀ r₁ : ℝ) : ℝ := ‖pair φ r₀ r₁‖

def direction (φ r₀ r₁ : ℝ) : ℝ := (pair φ r₀ r₁).arg

theorem pair_re (φ r₀ r₁ : ℝ) : (pair φ r₀ r₁).re = (r₀ + r₁) * Real.cos φ := by
  simp only [pair, add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, unit_re, Real.cos_neg]
  ring

theorem pair_im (φ r₀ r₁ : ℝ) : (pair φ r₀ r₁).im = (r₁ - r₀) * Real.sin φ := by
  simp only [pair, add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, unit_im, Real.sin_neg]
  ring

theorem length_sq (φ r₀ r₁ : ℝ) : length φ r₀ r₁ ^ 2 =
    (r₀ + r₁) ^ 2 * Real.cos φ ^ 2 + (r₁ - r₀) ^ 2 * Real.sin φ ^ 2 := by
  rw [length, ← normSq_eq_norm_sq, normSq_apply, pair_re, pair_im]
  ring

theorem length_direction (φ r₀ r₁ : ℝ) :
    (length φ r₀ r₁ : ℂ) * unit (direction φ r₀ r₁) = pair φ r₀ r₁ :=
  norm_mul_exp_arg_mul_I _

theorem rotated_length_direction (α φ r₀ r₁ : ℝ) :
    (length φ r₀ r₁ : ℂ) * unit (α + direction φ r₀ r₁) =
      (r₀ : ℂ) * unit (α - φ) + (r₁ : ℂ) * unit (α + φ) := by
  rw [unit_add, show (length φ r₀ r₁ : ℂ) * (unit α * unit (direction φ r₀ r₁)) =
    unit α * ((length φ r₀ r₁ : ℂ) * unit (direction φ r₀ r₁)) by ring, length_direction]
  simp only [pair, sub_eq_add_neg, unit_add]
  ring

theorem length_pos {φ r₀ r₁ : ℝ} (h : 0 < (pair φ r₀ r₁).re) : 0 < length φ r₀ r₁ := by
  exact h.trans_le (re_le_norm _)

theorem pair_path_hasDerivAt {r₀ r₁ : ℝ → ℝ} {x a b : ℝ} (φ : ℝ)
    (h₀ : HasDerivAt r₀ a x) (h₁ : HasDerivAt r₁ b x) :
    HasDerivAt (fun s => pair φ (r₀ s) (r₁ s)) (pair φ a b) x :=
  (h₀.ofReal_comp.mul_const (unit (-φ))).add (h₁.ofReal_comp.mul_const (unit φ))

theorem argument_path_hasDerivAt {f : ℝ → ℂ} {x : ℝ} {v : ℂ}
    (hf : HasDerivAt f v x) (hpos : 0 < (f x).re) :
    HasDerivAt (fun s => (f s).arg) (v / f x).im x := by
  have hh := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x
    (hf.clog_real (mem_slitPlane_iff.mpr (Or.inl hpos)))
  change HasDerivAt (fun s => (f s).log.im) (v / f x).im x at hh
  simpa only [log_im] using hh

theorem norm_path_hasDerivAt {f : ℝ → ℂ} {x : ℝ} {v : ℂ}
    (hf : HasDerivAt f v x) (hpos : 0 < (f x).re) :
    HasDerivAt (fun s => ‖f s‖) (‖f x‖ * (v / f x).re) x := by
  have hx : f x ≠ 0 := by intro hz; simp only [hz, zero_re, lt_self_iff_false] at hpos
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
    (hf.clog_real (mem_slitPlane_iff.mpr (Or.inl hpos)))
  change HasDerivAt (fun s => (f s).log.re) (v / f x).re x at hre
  have hlog := hre.exp
  have he : ∀ᶠ s in 𝓝 x, ‖f s‖ = Real.exp (f s).log.re := by
    filter_upwards [hf.continuousAt.eventually_ne hx] with s hs
    rw [log_re, Real.exp_log (norm_pos_iff.mpr hs)]
  have hder : Real.exp (f x).log.re * (v / f x).re = ‖f x‖ * (v / f x).re := by
    rw [log_re, Real.exp_log (norm_pos_iff.mpr hx)]
  exact (hlog.congr_deriv hder).congr_of_eventuallyEq he

theorem direction_path_hasDerivAt {r₀ r₁ : ℝ → ℝ} {x a b : ℝ} (φ : ℝ)
    (h₀ : HasDerivAt r₀ a x) (h₁ : HasDerivAt r₁ b x)
    (hpos : 0 < (pair φ (r₀ x) (r₁ x)).re) :
    HasDerivAt (fun s => direction φ (r₀ s) (r₁ s))
      (pair φ a b / pair φ (r₀ x) (r₁ x)).im x :=
  argument_path_hasDerivAt (pair_path_hasDerivAt φ h₀ h₁) hpos

theorem length_path_hasDerivAt {r₀ r₁ : ℝ → ℝ} {x a b : ℝ} (φ : ℝ)
    (h₀ : HasDerivAt r₀ a x) (h₁ : HasDerivAt r₁ b x)
    (hpos : 0 < (pair φ (r₀ x) (r₁ x)).re) :
    HasDerivAt (fun s => length φ (r₀ s) (r₁ s))
      (length φ (r₀ x) (r₁ x) * (pair φ a b / pair φ (r₀ x) (r₁ x)).re) x :=
  norm_path_hasDerivAt (pair_path_hasDerivAt φ h₀ h₁) hpos

theorem pair_contDiff (φ : ℝ) : ContDiff ℝ ∞ (fun p : ℝ × ℝ => pair φ p.1 p.2) := by
  unfold pair
  have hcast : ContDiff ℝ ∞ (Complex.ofReal : ℝ → ℂ) := Complex.ofRealCLM.contDiff
  fun_prop

theorem direction_contDiffAt (φ : ℝ) (p : ℝ × ℝ) (hpos : 0 < (pair φ p.1 p.2).re) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => direction φ p.1 p.2) p := by
  have hh : ContDiffAt ℝ ∞ Complex.log (pair φ p.1 p.2) :=
    (Complex.contDiffAt_log (mem_slitPlane_iff.mpr (Or.inl hpos))).restrict_scalars ℝ
  have hc := Complex.imCLM.contDiff.contDiffAt.comp p (hh.comp p (pair_contDiff φ).contDiffAt)
  simpa only [Function.comp_def, Complex.imCLM_apply, log_im, direction] using hc

theorem length_contDiffAt (φ : ℝ) (p : ℝ × ℝ) (hpos : 0 < (pair φ p.1 p.2).re) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => length φ p.1 p.2) p := by
  exact (pair_contDiff φ).contDiffAt.norm ℝ (by
    intro hz
    simp only [hz, zero_re, lt_self_iff_false] at hpos)

end
end StructuralNote.MatchingActivityRadialPair
