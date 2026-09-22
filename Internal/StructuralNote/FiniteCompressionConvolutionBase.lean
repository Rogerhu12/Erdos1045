import StructuralNote.FiniteCompressionRanked
import StructuralNote.FixedDualClassificationRecurrenceWronskian
import Mathlib.Data.Nat.Periodic

/-! Periodic natural-coordinate realization of the actual finite Schur convolution. -/

namespace StructuralNote.FiniteCompressionConvolutionBase

open Real Finset Erdos1045.EventualExact FourierMultiplier
open FixedDualClassificationKernel FixedDualClassificationRecurrenceWronskian
open FiniteCompressionRanked
open scoped BigOperators
noncomputable section

def sequence {m : ℕ} (hm : 0 < m) (b : Fin (2 * m) → ℝ) (k : ℕ) : ℝ := b (site hm k)

def kernelAt (m j s : ℕ) : ℝ :=
  finiteKernel (2 * m) (2 * Real.pi * ((j : ℝ) - s) / (2 * m : ℕ))

theorem sequence_periodic {m : ℕ} (hm : 0 < m) (b : Fin (2 * m) → ℝ) :
    Function.Periodic (sequence hm b) (2 * m) := by
  intro k
  unfold sequence
  congr 1
  apply Fin.ext
  simp only [site, Nat.add_mod, Nat.mod_self, add_zero, Nat.mod_mod]

theorem site_halfTurn {m : ℕ} (hm : 0 < m) (k : ℕ) :
    halfTurn hm (site hm k) = site hm (k + m) := by
  apply Fin.ext
  simp only [halfTurn, site, Nat.add_mod, Nat.mod_mod]

theorem sequence_antiperiodic {m : ℕ} (hm : 0 < m) (b : Fin (2 * m) → ℝ)
    (hb : FiniteBox.Antiperiodic hm b) (k : ℕ) : sequence hm b (k + m) = -sequence hm b k := by
  unfold sequence
  rw [← site_halfTurn hm k]
  exact hb (site hm k)

theorem finiteKernel_periodic (n : ℕ) : Function.Periodic (finiteKernel n) (2 * Real.pi) := by
  intro t
  rw [show t + 2 * Real.pi = (t + Real.pi) + Real.pi by ring,
    finiteKernel_antiperiodic, finiteKernel_antiperiodic, neg_neg]

theorem finiteKernel_sub_pi (n : ℕ) (t : ℝ) : finiteKernel n (t - Real.pi) = -finiteKernel n t := by
  have h := finiteKernel_antiperiodic n (t - Real.pi)
  rw [sub_add_cancel] at h
  linarith

theorem kernelAt_first_periodic {m : ℕ} (hm : 0 < m) (s : ℕ) :
    Function.Periodic (fun j => kernelAt m j s) (2 * m) := by
  intro j
  have hn : ((2 * m : ℕ) : ℝ) ≠ 0 := by positivity
  dsimp only [kernelAt]
  rw [show 2 * Real.pi * (((j + 2 * m : ℕ) : ℝ) - s) / (2 * m : ℕ) =
      2 * Real.pi * ((j : ℝ) - s) / (2 * m : ℕ) + 2 * Real.pi by push_cast; field_simp; ring]
  exact finiteKernel_periodic (2 * m) _

theorem kernelAt_second_antiperiodic {m : ℕ} (hm : 0 < m) (j s : ℕ) :
    kernelAt m j (s + m) = -kernelAt m j s := by
  have hmR : (m : ℝ) ≠ 0 := by positivity
  unfold kernelAt
  rw [show 2 * Real.pi * ((j : ℝ) - ((s + m : ℕ) : ℝ)) / (2 * m : ℕ) =
      2 * Real.pi * ((j : ℝ) - s) / (2 * m : ℕ) - Real.pi by push_cast; field_simp; ring]
  exact finiteKernel_sub_pi (2 * m) _

theorem kernelAt_second_periodic {m : ℕ} (hm : 0 < m) (j : ℕ) :
    Function.Periodic (kernelAt m j) (2 * m) := by
  intro s
  rw [show s + 2 * m = (s + m) + m by omega,
    kernelAt_second_antiperiodic hm, kernelAt_second_antiperiodic hm, neg_neg]

theorem kernelAt_shift (m j s : ℕ) : kernelAt m (j + 1) (s + 1) = kernelAt m j s := by
  unfold kernelAt
  congr 1
  push_cast
  ring

theorem kernelAt_site {m : ℕ} (hm : 0 < m) (j : ℕ) (s : Fin (2 * m)) :
    finiteKernel (2 * m) (gridAngle (site hm j) - gridAngle s) = kernelAt m j s := by
  have he : gridAngle (site hm j) - gridAngle s =
      2 * Real.pi * (((j % (2 * m) : ℕ) : ℝ) - s) / (2 * m : ℕ) := by
    unfold gridAngle site
    ring
  rw [he]
  exact (kernelAt_first_periodic hm s).map_mod_nat j

theorem operator_sequence_convolution {m : ℕ} (hm : 0 < m) (b : Fin (2 * m) → ℝ) (j : ℕ) :
    operator (2 * m) b (site hm j) =
      (2 / (2 * m : ℕ) : ℝ) * ∑ s ∈ range (2 * m), sequence hm b s * kernelAt m j s := by
  rw [operator_convolution]
  have hs : (∑ s : Fin (2 * m), b s * finiteKernel (2 * m) (gridAngle (site hm j) - gridAngle s)) =
      ∑ s : Fin (2 * m), sequence hm b s * kernelAt m j s := by
    apply sum_congr rfl
    intro s _
    rw [kernelAt_site hm]
    congr 1
    unfold sequence
    congr 1
    apply Fin.ext
    exact (Nat.mod_eq_of_lt s.isLt).symm
  rw [hs, Fin.sum_univ_eq_sum_range (fun s : ℕ => sequence hm b s * kernelAt m j s) (2 * m)]

end
end StructuralNote.FiniteCompressionConvolutionBase
