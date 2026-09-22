import StructuralNote.FiniteCompressionConvolutionBase

/-! Exact full-circle and arbitrary half-circle summation-by-parts entries for the actual operator. -/

namespace StructuralNote.FiniteCompressionConvolutionDifference

open Real Finset Erdos1045.EventualExact FourierMultiplier
open FiniteCompressionRanked FiniteCompressionConvolutionBase
open scoped BigOperators
noncomputable section

theorem periodic_sum_shift_one {n : ℕ} (f : ℕ → ℝ) (hf : Function.Periodic f n) :
    (∑ k ∈ range n, f (k + 1)) = ∑ k ∈ range n, f k := by
  have h1 := sum_range_succ f n
  have h2 := sum_range_succ' f n
  have he : f n = f 0 := by simpa only [zero_add] using hf 0
  rw [he] at h1
  linarith

theorem periodic_sum_shift {n : ℕ} (f : ℕ → ℝ) (hf : Function.Periodic f n) (a : ℕ) :
    (∑ k ∈ range n, f (a + k)) = ∑ k ∈ range n, f k := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hp : Function.Periodic (fun k => f (a + k)) n := by
      intro k
      simpa only [Nat.add_assoc] using hf (a + k)
    have hh := periodic_sum_shift_one (fun k => f (a + k)) hp
    have he : (∑ k ∈ range n, f (a + 1 + k)) = ∑ k ∈ range n, f (a + (k + 1)) := by
      apply sum_congr rfl
      intro k _
      congr 1
      omega
    exact he.trans (hh.trans ih)

theorem operator_difference_full {m : ℕ} (hm : 0 < m) (b : Fin (2 * m) → ℝ) (j : ℕ) :
    operator (2 * m) b (site hm (j + 1)) - operator (2 * m) b (site hm j) =
      (2 / (2 * m : ℕ) : ℝ) * ∑ s ∈ range (2 * m),
        kernelAt m j s * (sequence hm b (s + 1) - sequence hm b s) := by
  have hp : Function.Periodic (fun s => sequence hm b s * kernelAt m (j + 1) s) (2 * m) := by
    intro s
    dsimp only
    rw [sequence_periodic hm b, kernelAt_second_periodic hm]
  have hs := periodic_sum_shift_one (fun s => sequence hm b s * kernelAt m (j + 1) s) hp
  simp only [kernelAt_shift] at hs
  rw [operator_sequence_convolution hm, operator_sequence_convolution hm, ← hs,
    ← mul_sub, ← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro s _
  ring

def incrementContribution {m : ℕ} (hm : 0 < m) (b : Fin (2 * m) → ℝ) (j s : ℕ) : ℝ :=
  kernelAt m j s * (sequence hm b (s + 1) - sequence hm b s)

theorem incrementContribution_periodic {m : ℕ} (hm : 0 < m) (b : Fin (2 * m) → ℝ)
    (hb : FiniteBox.Antiperiodic hm b) (j : ℕ) :
    Function.Periodic (incrementContribution hm b j) m := by
  intro s
  unfold incrementContribution
  rw [kernelAt_second_antiperiodic hm, show s + m + 1 = (s + 1) + m by omega,
    sequence_antiperiodic hm b hb, sequence_antiperiodic hm b hb]
  ring

theorem operator_difference_half {m : ℕ} (hm : 0 < m) (b : Fin (2 * m) → ℝ)
    (hb : FiniteBox.Antiperiodic hm b) (j a : ℕ) :
    operator (2 * m) b (site hm (j + 1)) - operator (2 * m) b (site hm j) =
      (4 / (2 * m : ℕ) : ℝ) * ∑ s ∈ range m,
        kernelAt m j (a + s) * (sequence hm b (a + s + 1) - sequence hm b (a + s)) := by
  have hp := incrementContribution_periodic hm b hb j
  have hs : (∑ s ∈ range (2 * m), incrementContribution hm b j s) =
      2 * ∑ s ∈ range m, incrementContribution hm b j s := by
    rw [show 2 * m = m + m by omega, sum_range_add]
    have hh : (∑ s ∈ range m, incrementContribution hm b j (m + s)) =
        ∑ s ∈ range m, incrementContribution hm b j s := periodic_sum_shift _ hp m
    rw [hh]
    ring
  have ht := periodic_sum_shift (incrementContribution hm b j) hp a
  rw [operator_difference_full]
  change (2 / (2 * m : ℕ) : ℝ) * (∑ s ∈ range (2 * m), incrementContribution hm b j s) =
    (4 / (2 * m : ℕ) : ℝ) * ∑ s ∈ range m, incrementContribution hm b j (a + s)
  rw [hs, ht]
  ring

theorem kernelAt_gridAngle {m : ℕ} (hm : 0 < m) (j s : ℕ) :
    kernelAt m j s = FixedDualClassificationKernel.finiteKernel (2 * m)
      (FixedDualClassificationKernel.gridAngle (site hm j) -
        FixedDualClassificationKernel.gridAngle (site hm s)) := by
  symm
  rw [kernelAt_site hm]
  exact (kernelAt_second_periodic hm j).map_mod_nat s

theorem operator_difference_half_gridAngle {m : ℕ} (hm : 0 < m) (b : Fin (2 * m) → ℝ)
    (hb : FiniteBox.Antiperiodic hm b) (j a : ℕ) :
    operator (2 * m) b (site hm (j + 1)) - operator (2 * m) b (site hm j) =
      (4 / (2 * m : ℕ) : ℝ) * ∑ s ∈ range m,
        FixedDualClassificationKernel.finiteKernel (2 * m)
          (FixedDualClassificationKernel.gridAngle (site hm j) -
            FixedDualClassificationKernel.gridAngle (site hm (a + s))) *
          (b (site hm (a + s + 1)) - b (site hm (a + s))) := by
  simpa only [kernelAt_gridAngle hm, FiniteCompressionConvolutionBase.sequence] using
    operator_difference_half hm b hb j a

end
end StructuralNote.FiniteCompressionConvolutionDifference
