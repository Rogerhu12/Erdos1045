import ExteriorEnvelopeModel

/-! General scalar envelope estimates used to prove convexity of exterior
level sets, including the antipodal case of a rotated average. -/

namespace ExteriorReduction.ExteriorEnvelope

open Complex Metric Set Filter Bornology
open scoped Topology

noncomputable section

theorem exists_global_linear_bound {U : ℂ → ℝ} {L : ℝ}
    (hU : Continuous U)
    (hlim : Tendsto (fun z => U z / ‖z‖) (cocompact ℂ) (𝓝 L)) :
    ∃ B : ℝ, 0 < B ∧ ∀ z : ℂ, |U z| ≤ B * (1 + ‖z‖) := by
  have he : ∀ᶠ z : ℂ in cocompact ℂ, |U z / ‖z‖| < |L| + 1 :=
    hlim.abs.eventually (Iio_mem_nhds (by linarith))
  rw [← cobounded_eq_cocompact] at he
  obtain ⟨R, _, hR⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp he
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (max R 1)).exists_bound_of_continuousOn
    hU.continuousOn
  let B : ℝ := max M (|L| + 1) + 1
  have hB : 0 < B := by dsimp [B]; have := le_max_right M (|L| + 1); positivity
  refine ⟨B, hB, ?_⟩
  intro z
  by_cases hz : ‖z‖ ≤ max R 1
  · have hzM := hM z (mem_closedBall_zero_iff.mpr hz)
    have hMB : M ≤ B := by dsimp [B]; have := le_max_left M (|L| + 1); linarith
    have hMz0 : |U z| ≤ M := by simpa only [Real.norm_eq_abs] using hzM
    have hMz : |U z| ≤ B := hMz0.trans hMB
    nlinarith [norm_nonneg z]
  · have hzR : R ≤ ‖z‖ := (le_max_left R 1).trans (le_of_not_ge hz)
    have hz1 : 1 ≤ ‖z‖ := (le_max_right R 1).trans (le_of_not_ge hz)
    have hratio := hR hzR
    rw [abs_div, abs_of_nonneg (norm_nonneg z)] at hratio
    have hzpos : 0 < ‖z‖ := zero_lt_one.trans_le hz1
    have hb := (div_lt_iff₀ hzpos).mp hratio
    have hLB : |L| + 1 ≤ B := by dsimp [B]; have := le_max_right M (|L| + 1); linarith
    nlinarith [norm_nonneg z]

theorem envelope_ratio_tendsto {K : Set ℂ} {Φ : ℂ → ℂ} {d : ℂ}
    (hK : IsCompact K)
    (hΦ : Tendsto (fun z => Φ z / z) (cocompact ℂ) (𝓝 d)) :
    Tendsto (fun z => inverseNormEnvelope K Φ z / ‖z‖) (cocompact ℂ) (𝓝 ‖d‖) := by
  apply hΦ.norm.congr'
  filter_upwards [hK.compl_mem_cocompact] with z hz
  rw [inverseNormEnvelope_eq_norm hz, norm_div]

theorem scalar_composition_ratio_zero {U : ℂ → ℝ} {V : ℂ → ℂ} {L : ℝ}
    (hU : Continuous U) (hUnonneg : ∀ z, 0 ≤ U z)
    (hUratio : Tendsto (fun z => U z / ‖z‖) (cocompact ℂ) (𝓝 L))
    (hVratio : Tendsto (fun z => V z / z) (cocompact ℂ) (𝓝 0)) :
    Tendsto (fun z => U (V z) / ‖z‖) (cocompact ℂ) (𝓝 0) := by
  obtain ⟨B, hB, hbound⟩ := exists_global_linear_bound hU hUratio
  have hi : Tendsto (fun z : ℂ => 1 / ‖z‖) (cocompact ℂ) (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
      (tendsto_norm_cocompact_atTop (E := ℂ))
  have hv : Tendsto (fun z => ‖V z‖ / ‖z‖) (cocompact ℂ) (𝓝 0) := by
    simpa only [norm_div, norm_zero] using hVratio.norm
  have hupp : Tendsto (fun z => B * (1 / ‖z‖ + ‖V z‖ / ‖z‖))
      (cocompact ℂ) (𝓝 0) := by simpa using (hi.add hv).const_mul B
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupp
  · exact Filter.Eventually.of_forall fun z => div_nonneg (hUnonneg _) (norm_nonneg _)
  · filter_upwards [eventually_ne_zero_cocompact] with z hz
    have hb := (le_abs_self (U (V z))).trans (hbound (V z))
    have hdiv := div_le_div_of_nonneg_right hb (norm_nonneg z)
    convert hdiv using 1
    ring

/-- A scalar maximum principle on an arbitrary compact set. Only boundary
values and local holomorphic norm representatives above the threshold enter. -/
theorem scalar_envelope_maximum_on_compact {S : Set ℂ} {U : ℂ → ℝ} {C : ℝ}
    (hS : IsCompact S) (hU : Continuous U)
    (hboundary : ∀ z ∈ frontier S, U z ≤ C)
    (hlocal : ∀ z, C < U z → ∃ F : ℂ → ℂ, AnalyticAt ℂ F z ∧
      ∀ᶠ w in 𝓝 z, U w = ‖F w‖) :
    ∀ z ∈ S, U z ≤ C := by
  intro z hz
  by_contra hbad
  have hbad' : C < U z := lt_of_not_ge hbad
  obtain ⟨a, ha, hmax⟩ := hS.exists_isMaxOn ⟨z, hz⟩ hU.continuousOn
  have hCa : C < U a := hbad'.trans_le (hmax hz)
  let T : Set ℂ := S ∩ {w | U w = U a}
  have hTc : IsCompact T := hS.inter_right (isClosed_eq hU continuous_const)
  have hTo : IsOpen T := by
    apply isOpen_iff_mem_nhds.mpr
    intro w hw
    have hweq : U w = U a := hw.2
    have hwfront : w ∉ frontier S := by
      intro hf
      have hh := hboundary w hf
      rw [hw.2] at hh
      exact (not_le_of_gt hCa) hh
    have hwint : w ∈ interior S := by
      rw [frontier, hS.isClosed.closure_eq] at hwfront
      exact not_not.mp (fun hi => hwfront ⟨hw.1, hi⟩)
    obtain ⟨F, hF, heq⟩ := hlocal w (by rw [hweq]; exact hCa)
    have hFw : U w = ‖F w‖ := heq.self_of_nhds
    have hFm : IsLocalMax (norm ∘ F) w := by
      filter_upwards [heq, mem_interior_iff_mem_nhds.mp hwint] with v hv hvS
      change ‖F v‖ ≤ ‖F w‖
      rw [← hv, ← hFw, hw.2]
      exact hmax hvS
    have hconst := Complex.norm_eventually_eq_of_isLocalMax
      (hF.eventually_analyticAt.mono fun _ h => h.differentiableAt) hFm
    filter_upwards [heq, hconst, mem_interior_iff_mem_nhds.mp hwint] with v hv hc hvS
    refine ⟨hvS, ?_⟩
    change U v = U a
    rw [hv, hc, ← hFw, hweq]
  have hT : T = univ := (show IsClopen T from ⟨hTc.isClosed, hTo⟩).eq_univ ⟨a, ha, rfl⟩
  have hSuniv : S = univ := eq_univ_of_forall fun w => by
    have hwT : w ∈ T := by rw [hT]; trivial
    exact hwT.1
  exact hS.ne_univ hSuniv

#print axioms scalar_envelope_maximum_on_compact
#print axioms scalar_composition_ratio_zero

theorem general_planeEnvelope_tendsto {K : Set ℂ} {Φ V : ℂ → ℂ} {d a : ℂ}
    (hK : IsCompact K) (hU : Continuous (inverseNormEnvelope K Φ))
    (hΦmap : MapsTo Φ Kᶜ exteriorDisk)
    (hΦratio : Tendsto (fun z => Φ z / z) (cocompact ℂ) (𝓝 d))
    (hVratio : Tendsto (fun z => V z / z) (cocompact ℂ) (𝓝 a)) :
    Tendsto (planeEnvelope (inverseNormEnvelope K Φ) V)
      (cocompact ℂ) (𝓝 ‖d * a‖) := by
  by_cases ha : a = 0
  · subst a
    have hl := scalar_composition_ratio_zero hU
      (fun z => zero_le_one.trans (one_le_inverseNormEnvelope hΦmap z))
      (envelope_ratio_tendsto hK hΦratio) hVratio
    have he : (fun z => inverseNormEnvelope K Φ (V z) / ‖z‖) =ᶠ[cocompact ℂ]
        planeEnvelope (inverseNormEnvelope K Φ) V := by
      filter_upwards [(tendsto_norm_cocompact_atTop (E := ℂ)).eventually_gt_atTop 1] with z hz
      exact (planeEnvelope_eq_outside hz).symm
    simpa only [mul_zero, norm_zero] using hl.congr' he
  · have hVnorm := norm_tendsto_infty_of_ratio hVratio ha
    have hVproper : Tendsto V (cocompact ℂ) (cocompact ℂ) := by
      simpa only [cobounded_eq_cocompact] using tendsto_norm_atTop_iff_cobounded.mp hVnorm
    have hFinfty := (hΦratio.comp hVproper).mul hVratio
    have hF : Tendsto (fun w => Φ (V w) / w) (cocompact ℂ) (𝓝 (d * a)) := by
      apply hFinfty.congr'
      filter_upwards [hVproper.eventually eventually_ne_zero_cocompact] with w hw
      change Φ (V w) / V w * (V w / w) = Φ (V w) / w
      field_simp
    have he : (fun w => ‖Φ (V w) / w‖) =ᶠ[cocompact ℂ]
        planeEnvelope (inverseNormEnvelope K Φ) V := by
      filter_upwards [(tendsto_norm_cocompact_atTop (E := ℂ)).eventually_gt_atTop 1,
        hVproper.eventually hK.compl_mem_cocompact] with w hw hVw
      rw [planeEnvelope_eq_outside hw, inverseNormEnvelope_eq_norm hVw, norm_div]
    exact hF.norm.congr' he

theorem general_planeEnvelope_local_norm {K : Set ℂ} {Φ V : ℂ → ℂ}
    (hK : IsClosed K) (hV : AnalyticOnNhd ℂ V exteriorDisk)
    (hΦ : AnalyticOnNhd ℂ Φ Kᶜ)
    {z : ℂ} (hz : 1 < planeEnvelope (inverseNormEnvelope K Φ) V z) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F z ∧ ∀ᶠ w in 𝓝 z,
      planeEnvelope (inverseNormEnvelope K Φ) V w = ‖F w‖ := by
  have hzout : 1 < ‖z‖ := by
    by_contra hbad
    rw [planeEnvelope_eq_inside (le_of_not_gt hbad)] at hz
    exact (lt_irrefl 1) hz
  have hVz : V z ∉ K := by
    intro hbad
    rw [planeEnvelope_eq_outside hzout, inverseNormEnvelope_eq_one hbad] at hz
    have hh : 1 / ‖z‖ ≤ 1 := (div_le_one (zero_lt_one.trans hzout)).mpr hzout.le
    exact (not_lt_of_ge hh) hz
  have hVzA := hV z hzout
  refine ⟨fun w => Φ (V w) / w,
    ((hΦ _ hVz).comp hVzA).div analyticAt_id
      (norm_pos_iff.mp (zero_lt_one.trans hzout)), ?_⟩
  have hn : ∀ᶠ w in 𝓝 z, V w ∉ K :=
    hVzA.continuousAt.preimage_mem_nhds (hK.isOpen_compl.mem_nhds hVz)
  filter_upwards [exteriorDisk_isOpen.mem_nhds hzout, hn] with w hw hVw
  rw [planeEnvelope_eq_outside hw, inverseNormEnvelope_eq_norm hVw, norm_div]

theorem general_analytic_envelope_le {K : Set ℂ} {Φ V : ℂ → ℂ} {d a : ℂ}
    (hK : IsCompact K) (hU : Continuous (inverseNormEnvelope K Φ))
    (hΦ : AnalyticOnNhd ℂ Φ Kᶜ) (hΦmap : MapsTo Φ Kᶜ exteriorDisk)
    (hV : AnalyticOnNhd ℂ V exteriorDisk)
    (hcollar : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ,
      1 < ‖w‖ → ‖w‖ < 1 + δ → |inverseNormEnvelope K Φ (V w) - 1| < ε)
    (hΦratio : Tendsto (fun z => Φ z / z) (cocompact ℂ) (𝓝 d))
    (hVratio : Tendsto (fun z => V z / z) (cocompact ℂ) (𝓝 a))
    (hda : ‖d * a‖ ≤ 1) {w : ℂ} (hw : w ∈ exteriorDisk) :
    inverseNormEnvelope K Φ (V w) ≤ ‖w‖ := by
  have hqc := continuous_planeEnvelope hU hV.continuousOn hcollar
  have hb := ExteriorConvexCriterion.scalar_envelope_maximum hqc
    (fun z hz => general_planeEnvelope_local_norm hK.isClosed hV hΦ hz)
    (fun R hR => (general_planeEnvelope_tendsto hK hU hΦmap hΦratio hVratio).eventually
      (Iio_mem_nhds (hda.trans_lt hR))) w
  rw [planeEnvelope_eq_outside hw] at hb
  exact (div_le_one (zero_lt_one.trans hw)).mp hb

#print axioms general_analytic_envelope_le

end
end ExteriorReduction.ExteriorEnvelope
