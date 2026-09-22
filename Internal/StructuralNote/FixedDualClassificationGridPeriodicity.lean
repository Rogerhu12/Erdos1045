import StructuralNote.FixedDualClassificationStep
import StructuralNote.FixedDualClassificationZeroArcs
import StructuralNote.FiniteCompressionRanked

/-! Periodicity of the unwrapped natural-number grid indices.

The finite site map records the residue modulo `2 * m`.  The midpoint at an
arbitrary natural index therefore differs from the midpoint at its site by an
integer number of full turns.  We keep the index unwrapped here so that the
same statement can be used before passing to a `Fin (2 * m)` site.
-/

namespace StructuralNote.FixedDualClassificationGridPeriodicity

open Real
open Erdos1045.EventualExact
open StructuralNote.FixedDualClassificationStep
open StructuralNote.FixedDualClassificationZeroArcs
open StructuralNote.FiniteCompressionRanked

noncomputable section

theorem cellMidpoint_site_period {m : ℕ} (hm : 0 < m) (j : ℕ) :
    cellMidpoint (2 * m) j =
      cellMidpoint (2 * m) (site hm j) +
        ((j / (2 * m) : ℕ) : ℝ) * (2 * Real.pi) := by
  have hdecomp : j = 2 * m * (j / (2 * m)) + j % (2 * m) := by
    exact (Nat.div_add_mod j (2 * m)).symm
  unfold cellMidpoint
  simp only [site]
  push_cast
  have hdecompR : (j : ℝ) =
      (2 * m : ℝ) * (j / (2 * m) : ℕ) + (j % (2 * m) : ℕ) := by
    exact_mod_cast hdecomp
  have hden : (2 * (m : ℝ)) ≠ 0 := by positivity
  field_simp [hden]
  rw [hdecompR]
  ring

theorem cos_third_cellMidpoint_site {m : ℕ} (hm : 0 < m) (j : ℕ)
    (α : ℝ) :
    cos (3 * (cellMidpoint (2 * m) j - α)) =
      cos (3 * (cellMidpoint (2 * m) (site hm j) - α)) := by
  rw [cellMidpoint_site_period hm j]
  have harg :
      3 * (cellMidpoint (2 * m) (site hm j) +
          ((j / (2 * m) : ℕ) : ℝ) * (2 * Real.pi) - α) =
        3 * (cellMidpoint (2 * m) (site hm j) - α) +
          ((3 * (j / (2 * m)) : ℕ) : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [harg, Real.cos_add_nat_mul_two_pi]

theorem zeroCenter_add_six_nat (α : ℝ) (k : ℤ) (r : ℕ) :
    zeroCenter α (k + 6 * (r : ℤ)) =
      zeroCenter α k + (r : ℝ) * (2 * Real.pi) := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hindex : k + 6 * ((r + 1 : ℕ) : ℤ) =
          (k + 6 * (r : ℤ)) + 6 := by
        push_cast
        ring
      rw [hindex, zeroCenter_add_six, ih]
      push_cast
      ring

theorem haway_site_of_haway {m : ℕ} (hm : 0 < m) (j : ℕ) (α : ℝ)
    (haway : ∀ k : ℤ, (1 : ℝ) / 8 ≤
      |cellMidpoint (2 * m) j - zeroCenter α k|) :
    ∀ k : ℤ, (1 : ℝ) / 8 ≤
      |cellMidpoint (2 * m) (site hm j) - zeroCenter α k| := by
  intro k
  have hk := haway (k + 6 * ((j / (2 * m) : ℕ) : ℤ))
  rw [cellMidpoint_site_period hm j,
    zeroCenter_add_six_nat α k (j / (2 * m))] at hk
  have heq :
      (cellMidpoint (2 * m) (site hm j) +
          ((j / (2 * m) : ℕ) : ℝ) * (2 * Real.pi)) -
          (zeroCenter α k + ((j / (2 * m) : ℕ) : ℝ) * (2 * Real.pi)) =
        cellMidpoint (2 * m) (site hm j) - zeroCenter α k := by
    ring
  rw [heq] at hk
  exact hk

end
end StructuralNote.FixedDualClassificationGridPeriodicity
