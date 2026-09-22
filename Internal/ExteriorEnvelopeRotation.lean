import ExteriorEnvelopeTopology
import ExteriorConvexCriterion
import ExteriorInfinity
import Mathlib.Analysis.Normed.Module.Convex

/-! Rotated averages and their scalar envelopes. -/

namespace ExteriorReduction.ExteriorEnvelope

open Complex Metric Set Filter Bornology
open scoped Topology

noncomputable section

def rotatedAverage (Ψ : ℂ → ℂ) (u v w : ℂ) : ℂ := (Ψ (u * w) + Ψ (v * w)) / 2

theorem unit_mul_mem_exterior {u w : ℂ} (hu : ‖u‖ = 1) (hw : w ∈ exteriorDisk) :
    u * w ∈ exteriorDisk := by simpa [exteriorDisk, norm_mul, hu] using hw

theorem rotatedAverage_continuousOn {Ψ : ℂ → ℂ} {u v : ℂ}
    (hΨ : ContinuousOn Ψ exteriorDisk) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ContinuousOn (rotatedAverage Ψ u v) exteriorDisk := by
  exact ((hΨ.comp (continuous_const.mul continuous_id).continuousOn
    (fun _ hw => unit_mul_mem_exterior hu hw)).add
    (hΨ.comp (continuous_const.mul continuous_id).continuousOn
      (fun _ hw => unit_mul_mem_exterior hv hw))).div_const 2

/-- Convexity is used precisely here: close points have a close midpoint,
because every metric thickening of a convex set is convex. -/
theorem rotatedAverage_envelope_collar {K : Set ℂ} {Ψ Φ : ℂ → ℂ} {u v : ℂ}
    (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    (hU : Continuous (inverseNormEnvelope K Φ))
    (hΦ : ContinuousOn Φ Kᶜ) (hΦmap : MapsTo Φ Kᶜ exteriorDisk)
    (hleft : ∀ w ∈ exteriorDisk, Φ (Ψ w) = w)
    (hΦinfty : Tendsto (fun y => ‖Φ y‖) (cocompact ℂ) atTop)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, 1 < ‖w‖ → ‖w‖ < 1 + δ →
      |inverseNormEnvelope K Φ (rotatedAverage Ψ u v w) - 1| < ε := by
  have hsub : K ⊆ {x : ℂ | |inverseNormEnvelope K Φ x - 1| < ε} := by
    intro x hx
    simpa [inverseNormEnvelope_eq_one hx] using hε
  obtain ⟨η, hη, hηsub⟩ := hK.exists_thickening_subset_open
    (isOpen_lt ((hU.sub continuous_const).abs) continuous_const) hsub
  obtain ⟨δ, hδ, hcollar⟩ := exists_collar_infDist_lt hΦ hΦmap hleft hΦinfty hη
  refine ⟨δ, hδ, ?_⟩
  intro w hw hwr
  have hPu : Ψ (u * w) ∈ thickening η K := (mem_thickening_iff_infDist_lt hne).mpr
    (hcollar (u * w) (by simpa only [norm_mul, hu, one_mul] using hw)
      (by simpa only [norm_mul, hu, one_mul] using hwr))
  have hPv : Ψ (v * w) ∈ thickening η K := (mem_thickening_iff_infDist_lt hne).mpr
    (hcollar (v * w) (by simpa only [norm_mul, hv, one_mul] using hw)
      (by simpa only [norm_mul, hv, one_mul] using hwr))
  apply hηsub
  have hmid := (hconv.thickening η) hPu hPv (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  convert hmid using 1
  simp only [rotatedAverage, Complex.real_smul]
  push_cast
  ring

def planeEnvelope (U : ℂ → ℝ) (V : ℂ → ℂ) (w : ℂ) : ℝ :=
  if ‖w‖ ≤ 1 then 1 else U (V w) / ‖w‖

theorem planeEnvelope_eq_inside {U : ℂ → ℝ} {V : ℂ → ℂ} {w : ℂ}
    (hw : ‖w‖ ≤ 1) : planeEnvelope U V w = 1 := by simp [planeEnvelope, hw]

theorem planeEnvelope_eq_outside {U : ℂ → ℝ} {V : ℂ → ℂ} {w : ℂ}
    (hw : 1 < ‖w‖) : planeEnvelope U V w = U (V w) / ‖w‖ := by
  simp [planeEnvelope, not_le_of_gt hw]

/-- Scalar collar convergence is sufficient to patch the exterior expression
to the constant one inside the disk. No complex boundary values are used. -/
theorem continuous_planeEnvelope {U : ℂ → ℝ} {V : ℂ → ℂ}
    (hU : Continuous U) (hV : ContinuousOn V exteriorDisk)
    (hcollar : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ,
      1 < ‖w‖ → ‖w‖ < 1 + δ → |U (V w) - 1| < ε) :
    Continuous (planeEnvelope U V) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rcases lt_trichotomy ‖x‖ 1 with hx | hx | hx
  · apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [continuous_norm.continuousAt.eventually (Iio_mem_nhds hx)] with y hy
    exact planeEnvelope_eq_inside hy.le
  · rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hδbound⟩ := hcollar (ε / 2) (half_pos hε)
    refine ⟨min δ (ε / 2), lt_min hδ (half_pos hε), ?_⟩
    intro y hy
    rw [planeEnvelope_eq_inside hx.le]
    by_cases hyy : ‖y‖ ≤ 1
    · simpa [planeEnvelope_eq_inside hyy] using hε
    have hyout : 1 < ‖y‖ := lt_of_not_ge hyy
    have hnorm : |‖y‖ - 1| ≤ dist y x := by
      simpa only [hx, dist_eq_norm] using abs_norm_sub_norm_le y x
    have hnormε : |‖y‖ - 1| < ε / 2 := hnorm.trans_lt (hy.trans_le (min_le_right _ _))
    have hynorm : ‖y‖ < 1 + δ := by
      have hh := hnorm.trans_lt (hy.trans_le (min_le_left _ _))
      have hh' := le_abs_self (‖y‖ - 1)
      linarith
    have hUy := hδbound y hyout hynorm
    rw [planeEnvelope_eq_outside hyout, Real.dist_eq, div_sub_one
      (ne_of_gt (zero_lt_one.trans hyout)), abs_div, abs_of_pos (zero_lt_one.trans hyout)]
    calc
      |U (V y) - ‖y‖| / ‖y‖ ≤ |U (V y) - ‖y‖| :=
        div_le_self (abs_nonneg _) hyout.le
      _ ≤ |U (V y) - 1| + |1 - ‖y‖| := abs_sub_le _ _ _
      _ < ε := by rw [abs_sub_comm 1 ‖y‖]; linarith
  · have hbase : ContinuousAt (fun y => U (V y) / ‖y‖) x :=
      (hU.continuousAt.comp (hV.continuousAt (exteriorDisk_isOpen.mem_nhds hx))).div
        continuous_norm.continuousAt (ne_of_gt (zero_lt_one.trans hx))
    apply hbase.congr_of_eventuallyEq
    filter_upwards [exteriorDisk_isOpen.mem_nhds hx] with y hy
    exact planeEnvelope_eq_outside hy

#print axioms rotatedAverage_envelope_collar
#print axioms continuous_planeEnvelope

theorem rotatedAverage_analyticAt {Ψ : ℂ → ℂ} {u v w : ℂ}
    (hΨ : AnalyticOnNhd ℂ Ψ exteriorDisk) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hw : w ∈ exteriorDisk) : AnalyticAt ℂ (rotatedAverage Ψ u v) w := by
  exact (((hΨ _ (unit_mul_mem_exterior hu hw)).comp
    (analyticAt_const.mul analyticAt_id)).add
    ((hΨ _ (unit_mul_mem_exterior hv hw)).comp
      (analyticAt_const.mul analyticAt_id))).div_const

/-- Above level one the patched envelope has the required local holomorphic
representative. No inverse is applied to points of the omitted set. -/
theorem planeEnvelope_local_norm {K : Set ℂ} {Ψ Φ : ℂ → ℂ} {u v : ℂ}
    (hK : IsClosed K) (hΨ : AnalyticOnNhd ℂ Ψ exteriorDisk)
    (hΦ : AnalyticOnNhd ℂ Φ Kᶜ) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {z : ℂ} (hz : 1 < planeEnvelope (inverseNormEnvelope K Φ) (rotatedAverage Ψ u v) z) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F z ∧ ∀ᶠ w in 𝓝 z,
      planeEnvelope (inverseNormEnvelope K Φ) (rotatedAverage Ψ u v) w = ‖F w‖ := by
  have hzout : 1 < ‖z‖ := by
    by_contra hbad
    rw [planeEnvelope_eq_inside (le_of_not_gt hbad)] at hz
    exact (lt_irrefl 1) hz
  have hVz : rotatedAverage Ψ u v z ∉ K := by
    intro hbad
    rw [planeEnvelope_eq_outside hzout, inverseNormEnvelope_eq_one hbad] at hz
    have hh : 1 / ‖z‖ ≤ 1 := (div_le_one (zero_lt_one.trans hzout)).mpr hzout.le
    exact (not_lt_of_ge hh) hz
  have hV := rotatedAverage_analyticAt hΨ hu hv hzout
  refine ⟨fun w => Φ (rotatedAverage Ψ u v w) / w,
    ((hΦ _ hVz).comp hV).div analyticAt_id
      (norm_pos_iff.mp (zero_lt_one.trans hzout)), ?_⟩
  have hn : ∀ᶠ w in 𝓝 z, rotatedAverage Ψ u v w ∉ K :=
    hV.continuousAt.preimage_mem_nhds (hK.isOpen_compl.mem_nhds hVz)
  filter_upwards [exteriorDisk_isOpen.mem_nhds hzout, hn] with w hw hVw
  rw [planeEnvelope_eq_outside hw, inverseNormEnvelope_eq_norm hVw, norm_div]

#print axioms planeEnvelope_local_norm

end
end ExteriorReduction.ExteriorEnvelope
