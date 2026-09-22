import EventualExact.ExteriorRadialPairs
import OrderedBoundaryAngles

/-! Sorting physical polar angles from support bounds, including nonvertex nodes. -/

namespace Erdos1045.EventualExact.ExteriorSupport

open Complex Set ExteriorClassical ExteriorBoundary Configuration CyclicAngles
open scoped ComplexConjugate
noncomputable section

theorem node_radius_pos {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (hc : 1 / 2 ≤ d.capacity) (he : errorRadius d ≤ 1 / 4)
    {ν : ℂ} (hν : ‖ν‖ = 1) (i : Fin n)
    (hs : ∀ v ∈ hull z, (conj ν * (v - center d)).re ≤ (conj ν * (z i - center d)).re) :
    1 / 4 ≤ ‖z i - center d‖ := by
  have hlo := support_lower d HF hν hs
  have hn : (conj ν * (z i - center d)).re ≤ ‖z i - center d‖ := by
    simpa [hν] using re_le_norm (conj ν * (z i - center d))
  linarith

theorem exists_polar_angle {w : ℂ} (hw : 0 < ‖w‖) :
    ∃ t : ℝ, 0 ≤ t ∧ t < 2 * Real.pi ∧ w = (‖w‖ : ℂ) * unit t := by
  have hu : ‖w / (‖w‖ : ℂ)‖ = 1 := by
    simp [hw.ne']
  obtain ⟨t, ht0, ht1, ht⟩ := ExteriorReduction.exists_angle_Ico_of_norm_one hu
  refine ⟨t, ht0, ht1, ?_⟩
  rw [ht]
  field_simp [Complex.ofReal_ne_zero.mpr hw.ne']

/-- No assumption of radial injectivity is needed: the support estimate proves it. -/
theorem physical_angles_exist {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (hn : 0 < n) (hinj : Function.Injective z)
    (hc : 1 / 2 ≤ d.capacity) (he : errorRadius d ≤ 1 / 4)
    (ν : Fin n → ℂ) (hν : ∀ i, ‖ν i‖ = 1)
    (hs : ∀ i v, v ∈ hull z → (conj (ν i) * (v - center d)).re ≤
      (conj (ν i) * (z i - center d)).re) :
    ∃ (σ : Equiv.Perm (Fin n)) (a : Angles n),
      (∀ i : Fin n, 0 ≤ a.angle i ∧ a.angle i < 2 * Real.pi) ∧
      ∀ i : Fin n, z (σ i) - center d = (‖z (σ i) - center d‖ : ℂ) * unit (a.angle i) := by
  have hr (i : Fin n) : 0 < ‖z i - center d‖ :=
    lt_of_lt_of_le (by norm_num) (node_radius_pos d HF hc he (hν i) i (hs i))
  choose t ht0 ht1 ht using fun i => exists_polar_angle (hr i)
  have hzmem (i : Fin n) : z i ∈ hull z := subset_convexHull ℝ _ (mem_range_self i)
  have hti : Function.Injective t := by
    intro i j hij
    have hpj : z j - center d = (‖z j - center d‖ : ℂ) * unit (t i + 0) := by
      simpa only [add_zero, hij] using ht j
    have hlog := log_radius_pair_bound d HF hc he (hzmem i) (hzmem j)
      (hν i) (hν j) (hs i) (hs j) (norm_nonneg _) (norm_nonneg _) (ht i) hpj
    simp only [abs_zero, mul_zero] at hlog
    have hlogeq := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hlog (abs_nonneg _)))
    have hnorm : ‖z j - center d‖ = ‖z i - center d‖ :=
      Real.log_injOn_pos (hr j) (hr i) hlogeq
    apply hinj
    have hh : z i - center d = z j - center d := by rw [ht i, ht j, hnorm, hij]
    linear_combination hh
  obtain ⟨σ, hσ⟩ := ExteriorReduction.exists_perm_strictMono hti
  let a := ExteriorReduction.anglesOfFinite hn (t ∘ σ) hσ (fun i => ⟨ht0 (σ i), ht1 (σ i)⟩)
  have ha (i : Fin n) : a.angle i = t (σ i) := ExteriorReduction.periodicAngle_fin hn (t ∘ σ) i
  refine ⟨σ, a, fun i => ?_, fun i => ?_⟩
  · rw [ha]
    exact ⟨ht0 _, ht1 _⟩
  · rw [ha]
    exact ht (σ i)

end
end Erdos1045.EventualExact.ExteriorSupport
