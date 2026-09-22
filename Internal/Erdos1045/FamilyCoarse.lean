import Erdos1045.AnalyticFamily

/-! # Uniform coarse control for the actual extremal family

The inverse-square bootstrap, the bounded circular defect, and the limiting
Fourier square sum are consequences of the classical inputs. They are not
additional hypotheses on `ExtremalFamily`.
-/

namespace Erdos1045.GlobalProof

open Filter
open scoped Topology
open ExteriorClassical ExteriorBoundary Configuration MatrixDefect
noncomputable section

theorem ExtremalFamily.coarse_control (s : ExtremalFamily) (B : ClassicalAnalysis) :
    ∃ C K D : ℝ, 0 < C ∧ 0 ≤ K ∧ 0 ≤ D ∧ ∀ᶠ j in atTop,
      (1 / 2 : ℝ) ≤ s.capacity j ∧
      FaberFourier.H1Sampling (fun i : Fin (s.size j) => (s.data j).angles.angle i) C ∧
      (s.size j : ℝ) ^ 2 * s.energySquared j ≤ K ∧ s.matrixError j ≤ D := by
  obtain ⟨C, K₀, hC, hK₀, hinit⟩ := s.initial_matrix_estimates B
  let K : ℝ := 16 * K₀ * (18 * Real.pi) ^ 2
  refine ⟨C, K, K₀ * K, hC, by dsimp [K]; positivity, by dsimp [K]; positivity, ?_⟩
  filter_upwards [hinit,
    AsymptoticScales.eventual_real_dimension s.size_tendsto (4 * K₀ * (18 * Real.pi))]
    with j hj hlarge
  have hb := (s.data j).bootstrap_bound B.circle B.matrix (s.size_ge j)
    (s.discriminant_ge B j) hK₀ hj.2.2 hlarge
  refine ⟨hj.1, hj.2.1, hb.2, ?_⟩
  calc
    s.matrixError j ≤ K₀ * (s.size j : ℝ) ^ 2 * s.energySquared j := hj.2.2
    _ ≤ K₀ * K := by
      have h := mul_le_mul_of_nonneg_left hb.2 hK₀
      simpa only [K, ExtremalFamily.energySquared, mul_assoc] using h

theorem ExtremalFamily.capacity_tendsto_one (s : ExtremalFamily) (B : ClassicalAnalysis) :
    Tendsto s.capacity atTop (𝓝 1) := by
  have hu : Tendsto (fun j => Real.log 4 * ((1 : ℝ) / s.size j)) atTop (𝓝 0) := by
    simpa using (AsymptoticScales.inv_dimension s.size_tendsto).const_mul (Real.log 4)
  have hδ : Tendsto (fun j => 1 - s.capacity j) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun j =>
      sub_nonneg.mpr (s.data j).toBoundaryData.capacity_le_one) _ hu
    apply Eventually.of_forall
    intro j
    have hn : (0 : ℝ) < s.size j := by exact_mod_cast (show 0 < s.size j by have := s.size_ge j; omega)
    have hb := (s.data j).initial_capacity_deficit B.circle B.hadamard (s.identities j)
      (by have := s.size_ge j; omega) (s.discriminant_ge B j)
    have h : 1 - s.capacity j ≤ Real.log 4 / (s.size j : ℝ) :=
      (le_div_iff₀ hn).2 (by simpa only [ExtremalFamily.capacity, mul_comm] using hb)
    simpa only [ExtremalFamily.capacity, div_eq_mul_inv, one_mul] using h
  have h := hδ.const_sub 1
  simpa only [sub_zero, sub_sub_cancel] using h

theorem ExtremalFamily.normalized_matrix_nonsingular (s : ExtremalFamily)
    (B : ClassicalAnalysis) (j : ℕ) : (normalize (s.data j).matrix).det ≠ 0 := by
  apply (detSq_pos_iff _).1
  rw [detSq_normalize]
  have hF := (detSq_pos_iff _).2 ((s.data j).matrix_det_ne_zero B.circle (s.injective B j))
  have hn : (0 : ℝ) < s.size j := by exact_mod_cast (show 0 < s.size j by have := s.size_ge j; omega)
  exact div_pos hF (pow_pos hn _)

theorem ExtremalFamily.normalized_difference_tendsto (s : ExtremalFamily) (B : ClassicalAnalysis) :
    Tendsto (fun j => frobSq (normalize (s.data j).matrix - normalize (s.data j).circleMatrix))
      atTop (𝓝 0) := by
  obtain ⟨C, K, D, hC, hK, hD, hcontrol⟩ := s.coarse_control B
  have hu : Tendsto (fun j => D * ((1 : ℝ) / s.size j)) atTop (𝓝 0) := by
    simpa using (AsymptoticScales.inv_dimension s.size_tendsto).const_mul D
  apply squeeze_zero' (Eventually.of_forall fun j => frobSq_nonneg _) _ hu
  filter_upwards [hcontrol] with j hj
  rw [(s.data j).normalized_difference]
  have h := div_le_div_of_nonneg_right hj.2.2.2 (Nat.cast_nonneg (s.size j) : (0 : ℝ) ≤ s.size j)
  convert h using 1 <;> first | rfl | ring

theorem ExtremalFamily.matrix_defect_bounded (s : ExtremalFamily) (B : ClassicalAnalysis) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ j in atTop,
      0 ≤ defect (normalize (s.data j).matrix) ∧ defect (normalize (s.data j).matrix) ≤ D := by
  obtain ⟨C, K, D, hC, hK, hD, hcontrol⟩ := s.coarse_control B
  refine ⟨2 * Real.sqrt D + D, by positivity, ?_⟩
  filter_upwards [hcontrol] with j hj
  have hn : 0 < s.size j := by have := s.size_ge j; omega
  have hn1 : (1 : ℝ) ≤ s.size j := by exact_mod_cast hn
  have htrace0 := (s.data j).trace_nonneg B.circle B.matrix hn (s.discriminant_ge B j)
  have htrace := (s.data j).trace_coarse_bound hn
  have hd : 0 ≤ 1 - (s.data j).capacity := sub_nonneg.mpr (s.data j).toBoundaryData.capacity_le_one
  have hnegative : -(s.size j : ℝ) * (s.size j - 1) * (1 - (s.data j).capacity) ≤ 0 := by
    have hprod : 0 ≤ (s.size j : ℝ) * (s.size j - 1) * (1 - (s.data j).capacity) := by positivity
    nlinarith
  have hroot : Real.sqrt (frobSq (s.data j).errorMatrix) ≤ Real.sqrt D := Real.sqrt_le_sqrt hj.2.2.2
  have hquad : frobSq (s.data j).errorMatrix / s.size j ≤ D := by
    have h := div_le_self (frobSq_nonneg (s.data j).errorMatrix) hn1
    exact h.trans hj.2.2.2
  refine ⟨defect_nonneg B.matrix _ (s.normalized_matrix_nonsingular B j), ?_⟩
  rw [(s.data j).defect_trace_identity B.circle hn (s.injective B j)]
  linarith

theorem ExtremalFamily.circleEnergy_bounded (s : ExtremalFamily) (B : ClassicalAnalysis) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ j in atTop, 0 ≤ s.circleEnergy j ∧ s.circleEnergy j ≤ D := by
  obtain ⟨C, hC, hbound⟩ := s.matrix_defect_bounded B
  have h := direct_eventually_bounded_defect
    (fun j => normalize (s.data j).matrix) (fun j => normalize (s.data j).circleMatrix)
    (Eventually.of_forall (s.normalized_matrix_nonsingular B)) hC
    (hbound.mono fun _ hj => hj.2) (s.normalized_difference_tendsto B)
  refine ⟨directStabilityConstant C * (C + 1),
    mul_nonneg (directStabilityConstant_nonneg hC) (by linarith), ?_⟩
  filter_upwards [h] with j hj
  have heq := (s.data j).circle_energy_eq_defect B.circle B.geometry (by have := s.size_ge j; omega)
  simpa only [ExtremalFamily.circleEnergy, heq] using hj.2

theorem ExtremalFamily.fourierSquareSum_tendsto (s : ExtremalFamily) (B : ClassicalAnalysis) :
    Tendsto (fun j => KernelWeights.fourierSquareSum (s.data j).angles) atTop
      (𝓝 (Real.pi ^ 2 / 6)) := by
  obtain ⟨C, hC, hbound⟩ := s.circleEnergy_bounded B
  exact KernelWeights.fourierSquareSum_tendsto_eventually B.cosine
    (fun j => by have := s.size_ge j; omega) s.size_odd s.size_tendsto
    (fun j => (s.data j).angles) hC (hbound.mono fun _ hj => hj.2)

end
end Erdos1045.GlobalProof
