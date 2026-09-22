import StructuralNote.FixedDualClassificationKernelFourier
import StructuralNote.FixedDualClassificationFunctional
import Mathlib.MeasureTheory.Function.L2Space

/-! Square integrability of the actual logarithmic kernel, including both
singular endpoints. No Fourier expansion or assumed kernel regularity is used. -/

namespace StructuralNote.FixedDualClassificationKernelL2

open Real Set MeasureTheory FixedDualPrimitive FixedDualClassificationLogFourier
open scoped Topology
noncomputable section

theorem mul_log_sq_continuousOn :
    ContinuousOn (fun x : ℝ => x * log x ^ 2) (Ici 0) := by
  have hc : Continuous (fun x : ℝ => 4 * (sqrt x * log (sqrt x)) ^ 2) := by
    exact continuous_const.mul ((continuous_mul_log.comp continuous_sqrt).pow 2)
  apply hc.continuousOn.congr
  intro x hx
  by_cases hx0 : x = 0
  · simp [hx0]
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    dsimp only
    rw [log_sqrt hxpos.le]
    nlinarith [sq_sqrt hxpos.le]

theorem log_sq_intervalIntegrable {b : ℝ} (hb : 0 ≤ b) :
    IntervalIntegrable (fun x : ℝ => log x ^ 2) volume 0 b := by
  let F : ℝ → ℝ := fun x => x * log x ^ 2 - 2 * (x * log x) + 2 * x
  have hc : ContinuousOn F (Icc 0 b) := by
    exact ((mul_log_sq_continuousOn.mono (Icc_subset_Ici_self)).sub
      (continuous_const.mul continuous_mul_log).continuousOn).add
        (continuous_const.mul continuous_id).continuousOn
  apply intervalIntegral.intervalIntegrable_deriv_of_nonneg
    (g := F) (by simpa only [uIcc_of_le hb] using hc)
  · intro x hx
    rw [min_eq_left hb, max_eq_right hb] at hx
    have hx0 := hx.1.ne'
    have hd := (((hasDerivAt_id x).mul ((hasDerivAt_log hx0).pow 2)).sub
      (((hasDerivAt_id x).mul (hasDerivAt_log hx0)).const_mul 2)).add
        ((hasDerivAt_id x).const_mul 2)
    convert hd using 1 <;> try rfl
    dsimp only [id_eq, Pi.pow_apply]
    field_simp
    ring
  · intro x _
    exact sq_nonneg _

theorem logSine_bound {u : ℝ} (hu : u ∈ Ioc 0 (Real.pi / 2)) :
    |logSine u| ≤ |log u| + |log (2 / Real.pi)| + |log 2| := by
  have hs : 0 < sin u := sin_pos_of_pos_of_lt_pi hu.1 (by linarith [pi_pos, hu.2])
  have hlo := Real.log_le_log (mul_pos (div_pos (by norm_num) pi_pos) hu.1)
    (mul_le_sin hu.1.le hu.2)
  have hhi := Real.log_le_log hs (sin_le hu.1.le)
  rw [Real.log_mul (div_ne_zero (by norm_num) pi_pos.ne') hu.1.ne'] at hlo
  have hsabs : |log (sin u)| ≤ |log u| + |log (2 / Real.pi)| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le (log u), neg_abs_le (log (2 / Real.pi))]
    · linarith [le_abs_self (log u), abs_nonneg (log (2 / Real.pi))]
  unfold logSine
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hs.ne']
  exact (abs_add_le _ _).trans (by linarith)

theorem logSine_sq_half_integrable :
    IntervalIntegrable (fun u => logSine u ^ 2) volume 0 (Real.pi / 2) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : 0 ≤ Real.pi / 2)]
  have hlog := log_sq_intervalIntegrable (b := Real.pi / 2) (by positivity)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : 0 ≤ Real.pi / 2)] at hlog
  let c := |log (2 / Real.pi)| + |log 2|
  have hdom : IntegrableOn (fun u : ℝ => 2 * log u ^ 2 + 2 * c ^ 2) (Ioc 0 (Real.pi / 2)) :=
    (hlog.const_mul 2).add intervalIntegrable_const.1
  apply hdom.mono' ((show Measurable (fun u => logSine u ^ 2) by unfold logSine; fun_prop).aestronglyMeasurable)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := logSine_bound hu
  have hc : 0 ≤ c := add_nonneg (abs_nonneg _) (abs_nonneg _)
  rw [add_assoc] at h
  nlinarith [sq_abs (logSine u), sq_abs (log u), sq_nonneg (|log u| - c),
    abs_nonneg (logSine u), abs_nonneg (log u)]

theorem logSine_sq_integrable :
    IntervalIntegrable (fun u => logSine u ^ 2) volume 0 Real.pi := by
  have hr := (logSine_sq_half_integrable.comp_sub_left Real.pi).symm
  simp only [sub_zero, show Real.pi - Real.pi / 2 = Real.pi / 2 by ring,
    logSine, sin_pi_sub] at hr
  exact logSine_sq_half_integrable.trans hr

theorem kernel_sq_integrable :
    IntervalIntegrable (fun u => kernel u ^ 2) volume 0 Real.pi := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le pi_pos.le]
  have hlog := logSine_sq_integrable
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le pi_pos.le] at hlog
  have hdom : IntegrableOn (fun u : ℝ => 2 + 2 * logSine u ^ 2 + Real.pi ^ 2)
      (Ioc 0 Real.pi) :=
    (intervalIntegrable_const.1.add (hlog.const_mul 2)).add intervalIntegrable_const.1
  apply hdom.mono' ((show Measurable (fun u => kernel u ^ 2) by unfold kernel; fun_prop).aestronglyMeasurable)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hc : |cos u| ≤ 1 := abs_cos_le_one u
  have hs : |sin u| ≤ 1 := abs_sin_le_one u
  have ht : |Real.pi / 2 - u| ≤ Real.pi / 2 := abs_le.mpr ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have ha : |-(1 / 2) * cos u * (1 + logSine u)| ≤ (1 + |logSine u|) / 2 := by
    rw [abs_mul, abs_mul]
    norm_num only [abs_neg, abs_div, abs_one, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hh := abs_add_le 1 (logSine u)
    norm_num only [abs_one] at hh
    nlinarith [abs_nonneg (1 + logSine u), abs_nonneg (logSine u)]
  have hb : |(1 / 2) * (Real.pi / 2 - u) * sin u| ≤ Real.pi / 4 := by
    rw [abs_mul, abs_mul]
    norm_num only [abs_div, abs_one, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [abs_nonneg (Real.pi / 2 - u), abs_nonneg (sin u), pi_pos]
  have hk : |kernel u| ≤ (1 + |logSine u|) / 2 + Real.pi / 4 := by
    exact (abs_add_le _ _).trans (add_le_add ha hb)
  nlinarith [sq_abs (kernel u), sq_abs (logSine u), sq_nonneg (|logSine u| - 1),
    sq_nonneg ((1 + |logSine u|) / 2 - Real.pi / 4), abs_nonneg (kernel u),
    abs_nonneg (logSine u), pi_pos]

theorem kernel_memLp : MemLp kernel 2 (volume.restrict (Ioc 0 Real.pi)) := by
  apply (memLp_two_iff_integrable_sq ((show Measurable kernel by unfold kernel; fun_prop).aestronglyMeasurable)).mpr
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le pi_pos.le).mp kernel_sq_integrable

end
end StructuralNote.FixedDualClassificationKernelL2
