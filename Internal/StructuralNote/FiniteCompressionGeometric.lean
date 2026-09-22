import StructuralNote.FiniteCompressionDivergent
import StructuralNote.FixedDualClassificationKernelSignsFinal

/-! The self-interaction monotonicity premise is discharged for the actual
kernel on a compression arc of angular diameter at most pi/12. -/

namespace StructuralNote.FiniteCompressionGeometric

open Erdos1045.EventualExact FourierMultiplier Filter
open FiniteCompressionEnergy FiniteCompressionRanked FiniteCompressionDivergent
open FixedDualClassificationKernelSignsFinal
open scoped Topology
noncomputable section

theorem gridKernel_eq (m r : ℕ) :
    gridKernel (2 * m) r = FixedDualClassificationKernelSignsPropagation.gridKernel m r := by
  unfold gridKernel FixedDualClassificationKernelSignsPropagation.gridKernel
  congr 1
  push_cast
  ring

theorem eventual_near_antitone : ∀ᶠ m : ℕ in atTop, ∀ N : ℕ,
    2 * Real.pi * N / (2 * m : ℝ) ≤ Real.pi / 12 →
    AntitoneOn (gridKernel (2 * m)) (Set.Icc 1 N) := by
  filter_upwards [eventually_compressionKernelSigns] with m hs N hN
  intro i hi j hj hij
  rw [gridKernel_eq, gridKernel_eq]
  apply near_antitone hs hij
  have hangle : (j : ℝ) * (2 * Real.pi / (2 * m : ℕ)) ≤
      (N : ℝ) * (2 * Real.pi / (2 * m : ℕ)) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hj.2) (by positivity)
  have he : (N : ℝ) * (2 * Real.pi / (2 * m : ℕ)) =
      2 * Real.pi * N / (2 * m : ℝ) := by push_cast; ring
  rw [he] at hangle
  exact hangle.trans hN

theorem eventual_prefix_of_angular_span (C₀ η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 0 < m) (ℓ L R : ℕ) (e : ℕ → ℕ)
      (b : Fin (2 * m) → ℝ),
    R < 2 * m → StrictMonoOn e (Set.Iio ℓ) → e 0 = L → e (ℓ - 1) ≤ R →
    2 * Real.pi * (R - L : ℕ) / (2 * m : ℝ) ≤ Real.pi / 12 →
    b ∈ FiniteBox.Q hm →
    (∀ k ∈ Set.Icc L R, b (site hm k) = -FiniteBox.amplitude (2 * m)) →
    AntitoneOn (fun k => operator (2 * m) b (site hm k)) (Set.Icc L R) →
    η ≤ |Real.sin (2 * Real.pi * ℓ / (2 * m : ℝ))| →
    FiniteBox.B hm - normalizedBoxEnergy (operator (2 * m))
      (b + patch hm (FiniteBox.amplitude (2 * m)) (sites hm ℓ e)) ≤ C₀ / (2 * m : ℝ) ^ 2 →
    ∀ j < ℓ, e j = L + j := by
  filter_upwards [eventual_prefix_of_sine_bound C₀ η hη, eventual_near_antitone] with m hp hK
  intro hm ℓ L R e b hR he hfirst hlast hspan hb hbase hbackground hsin hdeficit
  apply hp hm ℓ L R (R - L) e b hR he hfirst hlast
    (by rw [hfirst]; exact Nat.sub_le_sub_right hlast L) hb hbase
    (hK (R - L) hspan) hbackground hsin hdeficit

end
end StructuralNote.FiniteCompressionGeometric
