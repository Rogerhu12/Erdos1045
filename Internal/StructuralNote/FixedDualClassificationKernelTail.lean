import StructuralNote.FixedDualClassificationOddSpectrum

/-! Uniform Fourier truncation of the actual integral potential on a bounded
box. The cutoff is independent of the profile. -/

namespace StructuralNote.FixedDualClassificationKernelTail

open Real MeasureTheory Set Filter FixedDualPrimitive FixedDualClassificationFunctional
open FixedDualClassificationKernelL2 FixedDualClassificationOddSpectrum
open scoped BigOperators Topology
noncomputable section

def squareMass (f : ℝ → ℝ) : ℝ := (∫ u in 0..Real.pi, f u ^ 2) / Real.pi

theorem oddCoefficient_parseval {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc 0 Real.pi))) :
    HasSum (fun k : ℤ => ‖oddCoefficient f k‖ ^ 2) (squareMass f) := by
  have h := hasSum_sq_fourierCoeffOn pi_pos (modulated_memLp hf)
  simpa only [oddCoefficient, modulated_norm, sq_abs, sub_zero, smul_eq_mul,
    squareMass, div_eq_inv_mul] using h

theorem kernelCoefficient_parseval :
    HasSum (fun k : ℤ => kernelCoefficient k ^ 2) (squareMass kernel) := by
  have h := oddCoefficient_parseval kernel_memLp
  simpa only [oddCoefficient_kernel, Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

theorem squareMass_nonneg (f : ℝ → ℝ) : 0 ≤ squareMass f := by
  apply div_nonneg _ pi_pos.le
  exact intervalIntegral.integral_nonneg pi_pos.le (fun _ _ => sq_nonneg _)

theorem coefficient_bessel {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc 0 Real.pi))) (s : Finset ℤ) :
    ∑ k ∈ s, ‖oddCoefficient f k‖ ^ 2 ≤ squareMass f :=
  sum_le_hasSum s (fun _ _ => sq_nonneg _) (oddCoefficient_parseval hf)

def truncation (f : ℝ → ℝ) (s : Finset ℤ) : ℂ :=
  ∑ k ∈ s, (2 * kernelCoefficient k : ℂ) * oddCoefficient f k

theorem truncation_sq_le {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc 0 Real.pi))) (s : Finset ℤ) :
    ‖truncation f s‖ ^ 2 ≤ 4 * (∑ k ∈ s, kernelCoefficient k ^ 2) * squareMass f := by
  have hnorm : ‖truncation f s‖ ≤
      ∑ k ∈ s, 2 * |kernelCoefficient k| * ‖oddCoefficient f k‖ := by
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro k _
    norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hpos : 0 ≤ ∑ k ∈ s, 2 * |kernelCoefficient k| * ‖oddCoefficient f k‖ :=
    Finset.sum_nonneg (fun k _ => by positivity)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun k => 2 * |kernelCoefficient k|) (fun k => ‖oddCoefficient f k‖)
  have he : (∑ k ∈ s, (2 * |kernelCoefficient k|) ^ 2) =
      4 * ∑ k ∈ s, kernelCoefficient k ^ 2 := by
    simp only [mul_pow, sq_abs]
    norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num]
    rw [Finset.mul_sum]
  rw [he] at hcs
  exact ((sq_le_sq₀ (norm_nonneg _) hpos).mpr hnorm).trans
    (hcs.trans (mul_le_mul_of_nonneg_left (coefficient_bessel hf s)
      (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))))

def tailMass (s : Finset ℤ) : ℝ := squareMass kernel - ∑ k ∈ s, kernelCoefficient k ^ 2

theorem tailMass_nonneg (s : Finset ℤ) : 0 ≤ tailMass s := by
  exact sub_nonneg.mpr (sum_le_hasSum s (fun _ _ => sq_nonneg _) kernelCoefficient_parseval)

theorem disjoint_kernel_mass_le (s t : Finset ℤ) :
    ∑ k ∈ t \ s, kernelCoefficient k ^ 2 ≤ tailMass s := by
  classical
  have h := sum_le_hasSum (s ∪ (t \ s)) (fun _ _ => sq_nonneg _) kernelCoefficient_parseval
  rw [Finset.sum_union (Finset.disjoint_left.mpr (fun _ hs ht => (Finset.mem_sdiff.mp ht).2 hs))] at h
  exact le_sub_iff_add_le.mpr (by simpa only [add_comm] using h)

theorem potential_truncation_sq_le {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc 0 Real.pi))) (s : Finset ℤ) :
    ‖(kernelPotential f : ℂ) - truncation f s‖ ^ 2 ≤ 4 * tailMass s * squareMass f := by
  classical
  have hlim : Tendsto (fun t : Finset ℤ => truncation f t) atTop (𝓝 (kernelPotential f : ℂ)) :=
    kernel_potential_hasSum hf
  apply le_of_tendsto ((hlim.sub_const (truncation f s)).norm.pow 2)
  filter_upwards [eventually_ge_atTop s] with t hst
  have he : truncation f t - truncation f s = truncation f (t \ s) := by
    symm
    exact Finset.sum_sdiff_eq_sub hst
  rw [he]
  exact (truncation_sq_le hf (t \ s)).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (disjoint_kernel_mass_le s t) (by norm_num))
        (squareMass_nonneg f))

theorem tailMass_tendsto : Tendsto tailMass atTop (𝓝 0) := by
  have h := (tendsto_const_nhds (x := squareMass kernel)).sub
    (show Tendsto (fun s : Finset ℤ => ∑ k ∈ s, kernelCoefficient k ^ 2)
      atTop (𝓝 (squareMass kernel)) from kernelCoefficient_parseval)
  change Tendsto (fun s => squareMass kernel - ∑ k ∈ s, kernelCoefficient k ^ 2) atTop (𝓝 0)
  simpa only [sub_self] using h

theorem box_memLp {f : ℝ → ℝ} (hf : Measurable f) {A : ℝ}
    (hbox : ∀ u ∈ Icc 0 Real.pi, |f u| ≤ A) :
    MemLp f 2 (volume.restrict (Ioc 0 Real.pi)) := by
  apply MemLp.of_bound hf.aestronglyMeasurable A
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with u hu
  exact hbox u ⟨hu.1.le, hu.2⟩

theorem box_squareMass_le {f : ℝ → ℝ} (hf : Measurable f) {A : ℝ}
    (hA : 0 ≤ A) (hbox : ∀ u ∈ Icc 0 Real.pi, |f u| ≤ A) : squareMass f ≤ A ^ 2 := by
  have hi : IntervalIntegrable (fun u => f u ^ 2) volume 0 Real.pi :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le pi_pos.le).mpr (box_memLp hf hbox).integrable_sq
  have h := intervalIntegral.integral_mono_on pi_pos.le hi intervalIntegrable_const
    (fun u hu => by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hA).mpr (hbox u hu))
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
  exact (div_le_iff₀ pi_pos).mpr (by simpa only [mul_comm] using h)

/-- A single finite signed-frequency set approximates every actual bounded profile. -/
theorem uniform_potential_truncation {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ s : Finset ℤ, ∀ f : ℝ → ℝ, Measurable f →
      (∀ u ∈ Icc 0 Real.pi, |f u| ≤ A) →
      ‖(kernelPotential f : ℂ) - truncation f s‖ < ε := by
  have hδ : 0 < ε ^ 2 / (4 * (A ^ 2 + 1)) := by positivity
  obtain ⟨s, hs⟩ := (tailMass_tendsto.eventually (gt_mem_nhds hδ)).exists
  refine ⟨s, fun f hf hbox => ?_⟩
  have hb := box_squareMass_le hf hA hbox
  have ht := potential_truncation_sq_le (box_memLp hf hbox) s
  have hδ' := (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * (A ^ 2 + 1))).mp hs
  have hc := mul_le_mul_of_nonneg_left hb
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (tailMass_nonneg s))
  have hsq : ‖(kernelPotential f : ℂ) - truncation f s‖ ^ 2 < ε ^ 2 := by
    nlinarith [tailMass_nonneg s]
  exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hsq

end
end StructuralNote.FixedDualClassificationKernelTail
