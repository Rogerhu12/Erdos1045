import Erdos1045.ExteriorSeparation
import Erdos1045.ExteriorQuantitative
import Erdos1045.ExteriorFaber
import Erdos1045.ExteriorBootstrap
import Erdos1045.RegularComparison
import Erdos1045.MatrixLimits
import Erdos1045.SharpTrace

/-! # A family of genuine perimeter extremizers

`ClassicalAnalysis` lists the external general theorems. `ExtremalFamily`
merely chooses configurations and their classical exterior data along a
sequence of odd dimensions. All quantitative estimates are proved below
and in the subsequent files, not included in either record.
-/

namespace Erdos1045.GlobalProof

open Filter
open scoped Topology
open ExteriorClassical ExteriorBoundary Configuration HullGeometry MatrixDefect
noncomputable section

structure ClassicalAnalysis : Prop where
  geometry : ClassicalHullGeometry
  circle : CircleMatrix.ClassicalCircleIdentities
  matrix : ClassicalMatrixFacts
  hadamard : ClassicalMatrixHadamard
  fourier : FaberFourier.ClassicalFourierFacts
  moment : FaberSampling.ClassicalGeometricMoment
  laurent : ClassicalLaurentAnalysis
  series : ClassicalLaurentSeries
  level : ClassicalLevelAnalysis
  sequence : FaberFourier.ClassicalSequenceFacts
  cosine : KernelWeights.ClassicalCosineFourier
  sine : ClassicalSineExpansion

structure ExtremalFamily where
  size : ℕ → ℕ
  size_ge : ∀ j, 4 ≤ size j
  size_odd : ∀ j, Odd (size j)
  size_tendsto : Tendsto size atTop atTop
  points : ∀ j, Points (size j)
  maximal : ∀ j, PerimeterExtremal (size j) (points j)
  data : ∀ j, ExteriorData (points j)
  identities : ∀ j, FaberIdentities (data j)

def ExtremalFamily.capacity (s : ExtremalFamily) (j : ℕ) : ℝ := (s.data j).capacity
def ExtremalFamily.energySquared (s : ExtremalFamily) (j : ℕ) : ℝ := (s.data j).energySquared
def ExtremalFamily.circleEnergy (s : ExtremalFamily) (j : ℕ) : ℝ := CyclicAngles.energy (s.data j).angles
def ExtremalFamily.trace (s : ExtremalFamily) (j : ℕ) : ℝ :=
  traceExcess (s.data j).capacity (s.data j).matrix
def ExtremalFamily.value (s : ExtremalFamily) (j : ℕ) : ℝ :=
  Real.log (discriminant (s.points j)) - (s.size j : ℝ) * Real.log (s.size j)
def ExtremalFamily.matrixError (s : ExtremalFamily) (j : ℕ) : ℝ := frobSq (s.data j).errorMatrix
def ExtremalFamily.remainderError (s : ExtremalFamily) (j : ℕ) : ℝ :=
  frobSq ((s.data j).errorMatrix - (s.data j).firstOrderMatrix)

theorem ExtremalFamily.injective (s : ExtremalFamily) (B : ClassicalAnalysis) (j : ℕ) :
    Function.Injective (s.points j) :=
  perimeterExtremal_injective B.geometry (by have := s.size_ge j; omega) (s.maximal j)

theorem ExtremalFamily.fekete (s : ExtremalFamily) (B : ClassicalAnalysis) (j : ℕ) :
    Fekete (s.points j) :=
  fun w hw => perimeterExtremal_dominates_hull B.geometry (s.maximal j) w hw

theorem ExtremalFamily.discriminant_ge (s : ExtremalFamily) (B : ClassicalAnalysis) (j : ℕ) :
    (s.size j : ℝ) ^ s.size j ≤ discriminant (s.points j) :=
  perimeterExtremal_discriminant_ge B.geometry (by have := s.size_ge j; omega) (s.maximal j)

theorem ExtremalFamily.initial_energy (s : ExtremalFamily) (B : ClassicalAnalysis) (j : ℕ) :
    (s.size j : ℝ) * s.energySquared j ≤ 18 * Real.pi * Real.log 4 :=
  (s.data j).initial_energy_bound B.circle B.hadamard (s.identities j)
    (by have := s.size_ge j; omega) (s.discriminant_ge B j)

theorem ExtremalFamily.capacity_half (s : ExtremalFamily) (B : ClassicalAnalysis) :
    ∀ᶠ j in atTop, (1 / 2 : ℝ) ≤ s.capacity j := by
  filter_upwards [AsymptoticScales.eventual_real_dimension s.size_tendsto (2 * Real.log 4)] with j hj
  exact (s.data j).initial_capacity_half B.circle B.hadamard (s.identities j)
    (by have := s.size_ge j; omega) (s.discriminant_ge B j) hj

theorem holder_for_data (B : ClassicalAnalysis) : ∃ H : ℝ, 0 < H ∧
    ∀ n (z : Points n) (d : ExteriorData z) (u v : ℂ), 1 ≤ ‖u‖ → 1 ≤ ‖v‖ →
      ‖laurent d.coefficient u - laurent d.coefficient v‖ ≤
        H * Real.sqrt d.energySquared * Real.sqrt ‖u - v‖ := by
  obtain ⟨H, hH, h⟩ := B.laurent.holder
  refine ⟨H, hH, ?_⟩
  intro n z d u v hu hv
  rw [d.parseval_identity]
  exact h d.coefficient d.sobolev u v hu hv

/-- A single sampling constant and a single matrix-error constant work for
every sufficiently large extremizer in the family. -/
theorem ExtremalFamily.initial_matrix_estimates (s : ExtremalFamily) (B : ClassicalAnalysis) :
    ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧ ∀ᶠ j in atTop,
      (1 / 2 : ℝ) ≤ s.capacity j ∧
      FaberFourier.H1Sampling (fun i : Fin (s.size j) => (s.data j).angles.angle i) C ∧
      s.matrixError j ≤ K * (s.size j : ℝ) ^ 2 * s.energySquared j := by
  obtain ⟨H, hH, holder⟩ := holder_for_data B
  let C₀ : ℝ := 18 * Real.pi * Real.log 4
  let A : ℝ := max 1 (16 * H ^ 2 * C₀)
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hlarge : 16 * H ^ 2 * C₀ ≤ A := le_max_right _ _
  have hγ : 0 < A / (32 * Real.exp A) := by positivity
  obtain ⟨C, hC, hsample⟩ := B.fourier.sampling _ hγ
  refine ⟨C, matrixConstant C A, hC, matrixConstant_nonneg hC.le, ?_⟩
  filter_upwards [s.capacity_half B] with j hc
  have hn : 0 < s.size j := by have := s.size_ge j; omega
  have hn0 : (0 : ℝ) < s.size j := by exact_mod_cast hn
  have hr : 1 < 1 + A / (s.size j : ℝ) := by linarith [div_pos hA hn0]
  have hsep := (s.data j).separated (s.identities j) B.level
    (by have := s.size_ge j; omega) (s.injective B j) (s.fekete B j)
    hH.le hA hc (s.initial_energy B j) hlarge (holder _ _ _)
  have hs := hsample _ hn _ hsep
  have hq := (s.data j).quotient_half hn hA (s.initial_energy B j) hlarge
    (fun i t => (s.data j).quotient_sq_bound hH.le hc (holder _ _ _) hr i t)
  exact ⟨hc, hs, (s.data j).faber_error_bound (s.identities j) B.series B.fourier B.moment
    hn hA hC.le hc hs hq⟩

end
end Erdos1045.GlobalProof
