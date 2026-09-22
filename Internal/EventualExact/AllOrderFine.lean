import EventualExact.CoarseFeketeFamilyProved
import EventualExact.AllOrderFourier

/-! # The sharp trace squeeze and vanishing circle energy

This is the second pass through the actual matrices. The first-order Faber
remainder vanishes, the SC upper-side error vanishes, and the finite sharp
quadratic bound squeezes the matrix defect to zero.
-/

namespace Erdos1045.EventualExact.CoarseFekete

open Filter
open scoped Topology
open ExteriorClassical ExteriorBoundary Configuration HullGeometry MatrixDefect GlobalProof
noncomputable section

def Family.trace (s : Family) (j : ℕ) : ℝ :=
  traceExcess (s.data j).capacity (s.data j).matrix

def Family.value (s : Family) (j : ℕ) : ℝ :=
  Real.log (discriminant (s.points j)) - (s.size j : ℝ) * Real.log (s.size j)

def Family.remainderError (s : Family) (j : ℕ) : ℝ :=
  frobSq ((s.data j).errorMatrix - (s.data j).firstOrderMatrix)

theorem Family.fourierSquareSum_tendsto (s : Family) (B : ClassicalAnalysis) :
    Tendsto (fun j => KernelWeights.fourierSquareSum (s.data j).angles) atTop
      (𝓝 (Real.pi ^ 2 / 6)) := by
  obtain ⟨C, hC, hbound⟩ := s.circleEnergy_bounded B
  exact AllOrderFourier.fourierSquareSum_tendsto_eventually
    (fun j => by have := s.size_ge j; omega) s.size_tendsto
    (fun j => (s.data j).angles) hC (hbound.mono fun _ hj => hj.2)

def Family.quotientSize (s : Family) (H : ℝ) (j : ℕ) : ℝ :=
  Real.sqrt (4 * H ^ 2 * s.size j * s.energySquared j)

theorem Family.quotientSize_tendsto (s : Family) (B : ClassicalAnalysis) (H : ℝ) :
    Tendsto (s.quotientSize H) atTop (𝓝 0) := by
  obtain ⟨C, K, D, hC, hK, hD, hb⟩ := s.coarse_control B
  have hV := AsymptoticScales.dimension_times_tendsto s.size_tendsto
    (Eventually.of_forall fun j => (s.data j).energySquared_nonneg)
    (hb.mono fun j hj => hj.2.2.1)
  have h := (Real.continuous_sqrt.tendsto 0).comp
    (by simpa [mul_assoc] using hV.const_mul (4 * H ^ 2))
  change Tendsto (fun j => Real.sqrt (4 * H ^ 2 * s.size j * s.energySquared j)) atTop (𝓝 0)
  simpa only [Family.quotientSize, Family.energySquared,
    Function.comp_def, Real.sqrt_zero, mul_assoc] using h

theorem Family.cubic_energy_tendsto (s : Family) (B : ClassicalAnalysis) :
    Tendsto (fun j => (s.size j : ℝ) ^ 3 * s.energySquared j ^ 2) atTop (𝓝 0) := by
  obtain ⟨C, K, D, hC, hK, hD, hb⟩ := s.coarse_control B
  have hb' : ∀ᶠ j in atTop, (s.size j : ℝ) ^ 2 * (Real.sqrt (s.energySquared j)) ^ 2 ≤ K := by
    filter_upwards [hb] with j hj
    rw [Real.sq_sqrt (show 0 ≤ s.energySquared j from (s.data j).energySquared_nonneg)]
    exact hj.2.2.1
  have h := AsymptoticScales.cubic_fourth_tendsto s.size_tendsto hb'
  have heq (j : ℕ) : Real.sqrt (s.energySquared j) ^ 4 = s.energySquared j ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
      Real.sq_sqrt (show 0 ≤ s.energySquared j from (s.data j).energySquared_nonneg)]
  simpa only [heq] using h

theorem Family.remainderError_tendsto (s : Family) (B : ClassicalAnalysis) :
    Tendsto s.remainderError atTop (𝓝 0) := by
  obtain ⟨C, K, D, hC, hK, hD, hb⟩ := s.coarse_control B
  obtain ⟨H, hH, holder⟩ := holder_for_data B
  have heta := s.quotientSize_tendsto B H
  have hh := (tendsto_order.1 heta).2 (1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
  have hu : Tendsto (fun j => (matrixConstant C 1 * (4 * H ^ 2)) *
      ((s.size j : ℝ) ^ 3 * s.energySquared j ^ 2)) atTop (𝓝 0) := by
    simpa using (s.cubic_energy_tendsto B).const_mul (matrixConstant C 1 * (4 * H ^ 2))
  apply squeeze_zero' (Eventually.of_forall fun j => frobSq_nonneg _) _ hu
  filter_upwards [hb, hh] with j hj hjη
  have hn : 0 < s.size j := by have := s.size_ge j; omega
  have hn0 : (0 : ℝ) < s.size j := by exact_mod_cast hn
  have hr : 1 < 1 + 1 / (s.size j : ℝ) := by linarith [one_div_pos.mpr hn0]
  have hq (i : Fin (s.size j)) (t : ℝ) :
      ‖(s.data j).quotient i (((1 + 1 / s.size j : ℝ) : ℂ) * unit t)‖ ≤ s.quotientSize H j := by
    apply Real.le_sqrt_of_sq_le
    have h := (s.data j).quotient_sq_bound hH.le hj.1 (holder _ _ _) hr i t
    dsimp only [Family.energySquared]
    convert h using 1; first | rfl | (field_simp; ring)
  have heta2 : s.quotientSize H j ^ 2 = 4 * H ^ 2 * s.size j * s.energySquared j := by
    apply Real.sq_sqrt
    exact mul_nonneg (by positivity) (s.data j).energySquared_nonneg
  have h := (s.data j).faber_remainder_bound (Q := 4 * H ^ 2) (η := s.quotientSize H j)
    (s.identities j) B.series B.fourier B.moment
    hn hC.le (Real.sqrt_nonneg _) hj.1 hj.2.1
    (fun i t => (hq i t).trans hjη.le) hq
    (by simpa only [Family.energySquared] using heta2.le)
  dsimp [Family.remainderError, Family.energySquared, ExteriorData.errorMatrix]
  convert h using 1; first | rfl | ring

def Family.traceError (s : Family) (j : ℕ) : ℝ :=
  2 * Real.sqrt (s.remainderError j) + s.matrixError j / s.size j

theorem Family.traceError_tendsto (s : Family) (B : ClassicalAnalysis) :
    Tendsto s.traceError atTop (𝓝 0) := by
  have hr := (Real.continuous_sqrt.tendsto 0).comp (s.remainderError_tendsto B)
  have he : Tendsto (fun j => s.matrixError j / s.size j) atTop (𝓝 0) := by
    simpa only [ExteriorData.normalized_difference, Family.matrixError] using
      s.normalized_difference_tendsto B
  change Tendsto (fun j => 2 * Real.sqrt (s.remainderError j) + s.matrixError j / s.size j) atTop (𝓝 0)
  simpa only [Function.comp_def, Real.sqrt_zero, mul_zero, zero_add] using
    (hr.const_mul 2).add he

def Family.capacityError (s : Family) (j : ℕ) : ℝ :=
  sharpBoundaryError (s.size j) (s.energySquared j) / 2

theorem Family.capacityError_tendsto (s : Family) (B : ClassicalAnalysis) :
    Tendsto s.capacityError atTop (𝓝 0) := by
  obtain ⟨C, K, D, hC, hK, hD, hb⟩ := s.coarse_control B
  have h := sharpBoundaryError_tendsto s.size_tendsto
    (Eventually.of_forall fun j => (s.data j).energySquared_nonneg)
    (hb.mono fun j hj => hj.2.2.1)
  change Tendsto (fun j => sharpBoundaryError (s.size j) (s.energySquared j) / 2) atTop (𝓝 0)
  simpa only [Family.energySquared, zero_div] using h.div_const 2

theorem Family.sharp_trace_upper (s : Family) (B : ClassicalAnalysis) :
    ∀ᶠ j in atTop, s.trace j ≤
      (1 + s.capacityError j) * KernelWeights.fourierSquareSum (s.data j).angles /
        (s.capacity j * (1 - 1 / (s.size j : ℝ))) + s.traceError j := by
  filter_upwards [s.capacity_half B] with j hc
  have hn : 0 < s.size j := by have := s.size_ge j; omega
  have hS : 0 ≤ KernelWeights.fourierSquareSum (s.data j).angles := by
    unfold KernelWeights.fourierSquareSum
    apply div_nonneg _ (sq_nonneg _)
    exact tsum_nonneg fun k => mul_nonneg (KernelWeights.weight_nonneg _ _) (sq_nonneg _)
  have hε : 0 ≤ s.capacityError j := div_nonneg (sharpBoundaryError_nonneg _ _) (by norm_num)
  have he := (s.data j).sharp_energy
    (sharpBoundaryError_nonneg _ _)
    ((s.data j).sharp_boundary_bound B.laurent hn hc)
  have ht := (s.data j).trace_sharp_bound B.laurent B.sequence (by have := s.size_ge j; omega)
  have henergy : Real.sqrt (s.energySquared j) ^ 2 ≤
      8 * Real.pi * s.capacity j * (1 + s.capacityError j) * (1 - s.capacity j) := by
    dsimp only [Family.energySquared, Family.capacity, Family.capacityError]
    rw [Real.sq_sqrt (s.data j).energySquared_nonneg]
    convert he using 1; first | rfl | ring
  have htrace : s.trace j ≤ -(s.size j : ℝ) * (s.size j - 1) * (1 - s.capacity j) +
      s.size j * Real.sqrt (s.energySquared j) * Real.sqrt (KernelWeights.fourierSquareSum (s.data j).angles) /
        (s.capacity j * Real.sqrt (2 * Real.pi)) + s.traceError j := by
    dsimp only [Family.trace, Family.energySquared, Family.capacity,
      Family.traceError, Family.remainderError, Family.matrixError]
    convert ht using 1; first | rfl | ring
  have h := SharpTrace.finite_trace_bound (by exact_mod_cast (show 1 < s.size j by have := s.size_ge j; omega))
    (s.data j).capacity_pos hS hε henergy htrace
  rwa [SharpTrace.finite_upper_eq (by exact_mod_cast (Nat.ne_of_gt hn))] at h

theorem Family.matrix_defect_tendsto_zero (s : Family) (B : ClassicalAnalysis)
    (hmax : ∀ j, PerimeterExtremal (s.size j) (s.points j)) :
    Tendsto (fun j => defect (normalize (s.data j).matrix)) atTop (𝓝 0) := by
  have hlo : ∀ᶠ j in atTop, regularComparison (s.size j) ≤ s.value j :=
    Eventually.of_forall fun j => regularComparison_le_extremal B.geometry
      (by have := s.size_ge j; omega) (hmax j)
  have hmid : ∀ᶠ j in atTop, s.value j ≤ s.trace j := by
    apply Eventually.of_forall
    intro j
    exact energy_le_traceExcess B.matrix (by have := s.size_ge j; omega) (s.data j).capacity_pos
      (s.data j).matrix (discriminant_pos _ (s.injective j)) ((s.data j).determinant_identity B.circle)
  have h := (SharpTrace.squeeze_trace_and_defect s.size_tendsto (s.capacity_tendsto_one B)
    (s.fourierSquareSum_tendsto B) (s.capacityError_tendsto B) (s.traceError_tendsto B)
    (regularComparison_tendsto B.sine (fun j => by have := s.size_ge j; omega) s.size_tendsto)
    hlo hmid (s.sharp_trace_upper B)).2.2
  apply h.congr'
  exact Eventually.of_forall fun j =>
    ((s.data j).defect_trace_identity B.circle (by have := s.size_ge j; omega) (s.injective j)).symm

/-- Core global conclusion: the concrete cyclic-angle energy tends to zero. -/
theorem Family.circleEnergy_tendsto_zero (s : Family) (B : ClassicalAnalysis)
    (hmax : ∀ j, PerimeterExtremal (s.size j) (s.points j)) :
    Tendsto s.circleEnergy atTop (𝓝 0) := by
  have hA : ∀ᶠ j in atTop, (normalize (s.data j).matrix).det ≠ 0 := by
    apply Eventually.of_forall
    intro j
    apply (detSq_pos_iff _).1
    rw [detSq_normalize]
    exact div_pos ((detSq_pos_iff _).2 ((s.data j).matrix_det_ne_zero B.circle (s.injective j)))
      (pow_pos (by exact_mod_cast (show 0 < s.size j by have := s.size_ge j; omega)) _)
  have h := (direct_tendsto_defect_and_eventually_nonsingular
    (fun j => normalize (s.data j).matrix) (fun j => normalize (s.data j).circleMatrix)
    hA (s.matrix_defect_tendsto_zero B hmax) (s.normalized_difference_tendsto B)).2
  apply h.congr'
  exact Eventually.of_forall fun j =>
    ((s.data j).circle_energy_eq_defect B.circle B.geometry (by have := s.size_ge j; omega)).symm

end
end Erdos1045.EventualExact.CoarseFekete

