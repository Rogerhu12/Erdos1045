import Erdos1045.ExteriorClassical
import Erdos1045.ExteriorEstimates
import Erdos1045.FaberKernelBridge
import Erdos1045.MatrixHadamard
import Erdos1045.CircleMatrix
import Mathlib.LinearAlgebra.Vandermonde

namespace Erdos1045.ExteriorClassical

open scoped BigOperators
open Configuration MatrixDefect FaberFourier ExteriorBoundary
noncomputable section

variable {n : ℕ} {z : Points n}

theorem ExteriorData.matrix_zero_column (d : ExteriorData z) (i j : Fin n)
    (hj : (j : ℕ) = 0) : d.matrix i j = 1 := by
  simp [ExteriorData.matrix, ExteriorData.faber, hj]

theorem ExteriorData.matrix_other_bound (d : ExteriorData z) (HF : FaberIdentities d)
    (i j : Fin n) (hj : (j : ℕ) ≠ 0) : ‖d.matrix i j‖ ≤ 2 := by
  apply HF.norm_bound j (by omega) (z i)
  exact subset_convexHull ℝ _ (Set.mem_range_self i)

/-- The concrete Faber evaluation determinant. The polynomial change of basis
uses mathlib's monic Vandermonde theorem, rather than an additional assumption. -/
theorem ExteriorData.determinant_identity (d : ExteriorData z)
    (HC : CircleMatrix.ClassicalCircleIdentities) :
    discriminant z = d.capacity ^ (n * (n - 1)) * detSq d.matrix := by
  let w : Points n := fun i => (z i - d.offset) / (d.capacity : ℂ)
  let p : Fin n → Polynomial ℂ := fun j =>
    FaberAlgebra.normalizedFaber (fun m => d.coefficient m / d.capacity) j
  have hv : (Matrix.vandermonde w).det = d.matrix.det := by
    have h := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde w p
      (fun j => FaberAlgebra.normalizedFaber_natDegree _ j)
      (fun j => FaberAlgebra.normalizedFaber_monic _ j)
    exact h
  have hdisc : detSq d.matrix = discriminant w := by
    rw [← HC.vandermonde n w]
    change Complex.normSq d.matrix.det = Complex.normSq (Matrix.vandermonde w).det
    rw [hv]
  have hc : (d.capacity : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr d.capacity_pos.ne'
  have haff : (fun i => d.offset + (d.capacity : ℂ) * w i) = z := by
    funext i
    dsimp only [w]
    field_simp
    ring
  have hd := congrArg discriminant haff
  rw [discriminant_affine] at hd
  simpa only [exponent, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos d.capacity_pos, hdisc] using hd.symm

theorem ExteriorData.initial_capacity_deficit (d : ExteriorData z)
    (HC : CircleMatrix.ClassicalCircleIdentities) (HH : ClassicalMatrixHadamard)
    (HF : FaberIdentities d) (hn : 2 ≤ n) (hΔ : (n : ℝ) ^ n ≤ discriminant z) :
    (n : ℝ) * (1 - d.capacity) ≤ Real.log 4 := by
  apply ExteriorEstimates.initial_capacity_deficit (by exact_mod_cast hn) d.capacity_pos
  exact initial_capacity_log_bound HH (by omega) d.capacity_pos d.matrix
    d.matrix_zero_column (d.matrix_other_bound HF) hΔ (d.determinant_identity HC)

theorem ExteriorData.initial_capacity_half (d : ExteriorData z)
    (HC : CircleMatrix.ClassicalCircleIdentities) (HH : ClassicalMatrixHadamard)
    (HF : FaberIdentities d) (hn : 2 ≤ n) (hΔ : (n : ℝ) ^ n ≤ discriminant z)
    (hlarge : 2 * Real.log 4 ≤ n) : (1 : ℝ) / 2 ≤ d.capacity := by
  exact ExteriorEstimates.capacity_half_of_initial (by exact_mod_cast (show 0 < n by omega))
    hlarge (d.initial_capacity_deficit HC HH HF hn hΔ)

theorem ExteriorData.initial_energy_bound (d : ExteriorData z)
    (HC : CircleMatrix.ClassicalCircleIdentities) (HH : ClassicalMatrixHadamard)
    (HF : FaberIdentities d) (hn : 2 ≤ n) (hΔ : (n : ℝ) ^ n ≤ discriminant z) :
    (n : ℝ) * d.energySquared ≤ 18 * Real.pi * Real.log 4 := by
  have hd := d.initial_capacity_deficit HC HH HF hn hΔ
  have he := d.toBoundaryData.coarse_energy
  have hmul := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg n)
  have hd' := mul_le_mul_of_nonneg_left hd (show 0 ≤ 18 * Real.pi by positivity)
  nlinarith

theorem ExteriorData.circleMatrix_eq_characterMatrix (d : ExteriorData z) :
    d.circleMatrix = characterMatrix (fun i : Fin n => d.angles.angle i) := by
  rw [characterMatrix_eq_powers]
  rfl

theorem ExteriorData.circleMatrix_unit (d : ExteriorData z) :
    ∀ i j, Complex.normSq (d.circleMatrix i j) = 1 := by
  rw [d.circleMatrix_eq_characterMatrix]
  exact characterMatrix_unit _

def ExteriorData.errorMatrix (d : ExteriorData z) : Mat n := d.matrix - d.circleMatrix

theorem ExteriorData.errorMatrix_eq (d : ExteriorData z) :
    d.errorMatrix = coefficientMatrix d.remainder := rfl

theorem ExteriorData.matrix_eq (d : ExteriorData z) :
    d.matrix = d.circleMatrix + d.errorMatrix := by
  unfold ExteriorData.errorMatrix
  abel

theorem ExteriorData.normalized_difference (d : ExteriorData z) :
    frobSq (normalize d.matrix - normalize d.circleMatrix) = frobSq d.errorMatrix / n := by
  exact frobSq_normalized_difference d.matrix d.circleMatrix

theorem ExteriorData.circle_energy_eq_defect (d : ExteriorData z)
    (HC : CircleMatrix.ClassicalCircleIdentities) (HG : HullGeometry.ClassicalHullGeometry)
    (hn : 3 ≤ n) :
    CyclicAngles.energy d.angles = defect (normalize d.circleMatrix) :=
  CircleMatrix.energy_eq_matrix_defect HC HG hn d.angles

theorem ExteriorData.matrix_det_ne_zero (d : ExteriorData z)
    (HC : CircleMatrix.ClassicalCircleIdentities) (hz : Function.Injective z) :
    d.matrix.det ≠ 0 := by
  apply (detSq_pos_iff _).1
  have h := discriminant_pos z hz
  rw [d.determinant_identity HC] at h
  exact (mul_pos_iff_of_pos_left (pow_pos d.capacity_pos _)).1 h

theorem ExteriorData.defect_trace_identity (d : ExteriorData z)
    (HC : CircleMatrix.ClassicalCircleIdentities) (hn : 0 < n) (hz : Function.Injective z) :
    defect (normalize d.matrix) = traceExcess d.capacity d.matrix -
      (Real.log (discriminant z) - n * Real.log n) :=
  MatrixDefect.defect_trace_identity hn d.capacity_pos d.matrix (discriminant_pos z hz)
    (d.determinant_identity HC)

theorem ExteriorData.trace_nonneg (d : ExteriorData z)
    (HC : CircleMatrix.ClassicalCircleIdentities) (HM : ClassicalMatrixFacts)
    (hn : 0 < n) (hΔ : (n : ℝ) ^ n ≤ discriminant z) :
    0 ≤ Real.log (discriminant z) - n * Real.log n ∧ 0 ≤ traceExcess d.capacity d.matrix :=
  traceExcess_nonneg HM hn d.capacity_pos d.matrix hΔ (d.determinant_identity HC)

theorem ExteriorData.log_capacity_bound (d : ExteriorData z) (hn : 0 < n) :
    ((n * (n - 1) : ℕ) : ℝ) * Real.log d.capacity ≤
      -(n : ℝ) * (n - 1) * (1 - d.capacity) := by
  have hl := Real.log_le_sub_one_of_pos d.capacity_pos
  have hm := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (n * (n - 1)))
  rw [Nat.cast_mul, Nat.cast_sub hn, Nat.cast_one] at hm ⊢
  nlinarith

theorem ExteriorData.trace_coarse_bound (d : ExteriorData z) (hn : 0 < n) :
    traceExcess d.capacity d.matrix ≤ -(n : ℝ) * (n - 1) * (1 - d.capacity) +
      2 * Real.sqrt (frobSq d.errorMatrix) + frobSq d.errorMatrix / n := by
  have he := normalized_frobSq_add_le hn d.circleMatrix d.errorMatrix d.circleMatrix_unit
  rw [← d.matrix_eq] at he
  have hl := d.log_capacity_bound hn
  unfold traceExcess
  linarith

theorem ExteriorData.firstOrder_cross_bound (d : ExteriorData z)
    (HL : ClassicalLaurentAnalysis) (HS : ClassicalSequenceFacts) (hn : 2 ≤ n) :
    cross d.circleMatrix d.firstOrderMatrix ≤
      ((n : ℝ) * Real.sqrt d.energySquared / (d.capacity * Real.sqrt (2 * Real.pi))) *
        Real.sqrt (KernelWeights.fourierSquareSum d.angles) := by
  rw [d.circleMatrix_eq_characterMatrix, ← spectralSquareSum_eq_fourierSquareSum d.angles]
  exact matrix_firstOrder_cross_le HS hn d.capacity_pos (Real.sqrt_nonneg _)
    d.coefficient (fun i : Fin n => d.angles.angle i) d.sobolev.2
    (HL.absolute d.coefficient d.sobolev)
    (by rw [Real.sq_sqrt d.toBoundaryData.energySquared_nonneg, d.parseval_identity]; rfl)

/-- The exact data-level trace estimate needed in the sharp bootstrap. -/
theorem ExteriorData.trace_firstOrder_bound (d : ExteriorData z)
    (HL : ClassicalLaurentAnalysis) (HS : ClassicalSequenceFacts) (hn : 2 ≤ n) :
    traceExcess d.capacity d.matrix ≤
      ((n * (n - 1) : ℕ) : ℝ) * Real.log d.capacity +
      ((n : ℝ) * Real.sqrt d.energySquared / (d.capacity * Real.sqrt (2 * Real.pi))) *
        Real.sqrt (KernelWeights.fourierSquareSum d.angles) +
      2 * Real.sqrt (frobSq (d.errorMatrix - d.firstOrderMatrix)) + frobSq d.errorMatrix / n := by
  have ht := traceExcess_firstOrder_le (by omega : 0 < n) d.capacity
    d.circleMatrix d.errorMatrix d.firstOrderMatrix d.circleMatrix_unit
  rw [← d.matrix_eq] at ht
  have hx := d.firstOrder_cross_bound HL HS hn
  linarith

theorem ExteriorData.trace_sharp_bound (d : ExteriorData z)
    (HL : ClassicalLaurentAnalysis) (HS : ClassicalSequenceFacts) (hn : 2 ≤ n) :
    traceExcess d.capacity d.matrix ≤ -(n : ℝ) * (n - 1) * (1 - d.capacity) +
      ((n : ℝ) * Real.sqrt d.energySquared / (d.capacity * Real.sqrt (2 * Real.pi))) *
        Real.sqrt (KernelWeights.fourierSquareSum d.angles) +
      2 * Real.sqrt (frobSq (d.errorMatrix - d.firstOrderMatrix)) + frobSq d.errorMatrix / n := by
  have ht := d.trace_firstOrder_bound HL HS hn
  have hl := d.log_capacity_bound (by omega)
  linarith

end
end Erdos1045.ExteriorClassical
