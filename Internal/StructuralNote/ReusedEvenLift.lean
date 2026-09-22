import StructuralNote.ReusedEndpoints
import EventualExact.WholeBoxLowerBound

/-! The already verified whole-box construction, connected to the new note's
actual extremal value. This gives the lower-bound half of the even reduction;
it does not classify the finite sign maximizers or prove the pressure upper bound. -/

noncomputable section
namespace StructuralNote

open Erdos1045 Erdos1045.Configuration Erdos1045.EventualExact

theorem M_eq_verified_diameterMaximum (n : ℕ) :
    M n = WholeBoxLowerBound.diameterMaximum n := by
  unfold M diameterValues WholeBoxLowerBound.diameterMaximum
  congr 1

theorem M_attained {n : ℕ} (hn : 0 < n) :
    ∃ z : Points n, DiameterAtMost 2 z ∧ discriminant z = M n := by
  rw [M_eq_verified_diameterMaximum]
  exact WholeBoxLowerBound.diameterMaximum_attained hn

theorem M_positive {n : ℕ} (hn : 3 ≤ n) : 0 < M n := by
  rw [M_eq_verified_diameterMaximum]
  exact WholeBoxLowerBound.diameterMaximum_pos hn

theorem even_box_lower_bound {m : ℕ} (hm : 256 ≤ 2 * m) :
    FiniteBox.B (by omega : 0 < m) - 1000000 / ((2 * m : ℕ) : ℝ) ^ 2 ≤
      Real.log (M (2 * m) / ((2 * m : ℕ) : ℝ) ^ (2 * m)) := by
  rw [M_eq_verified_diameterMaximum]
  exact WholeBoxLowerBound.diameterMaximum_log_lower hm

end StructuralNote
