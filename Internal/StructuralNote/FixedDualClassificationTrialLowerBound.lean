import StructuralNote.FixedDualClassificationTrialPartialEnergy
import StructuralNote.FixedDualClassificationTrialCoefficients

/-! A fixed positive gap above 531/2000 for the actual finite box maximum.
The trial is the cell average of the actual third square wave; its nine
retained terms are evaluated exactly. -/

namespace StructuralNote.FixedDualClassificationTrialLowerBound

open Filter Erdos1045.EventualExact
open FixedDualClassificationTrialPartialEnergy FixedDualClassificationTrialCoefficients
open scoped BigOperators Topology

theorem thirdLimit_nine :
    thirdLimit trial 9 = 11460107888773 / 43158748192560 := by
  unfold thirdLimit
  simp_rw [trial_coefficient_norm]
  exact nine_term_value

theorem eventual_B_fixed_gap : ∀ᶠ m : ℕ in atTop, ∀ hm : 0 < m,
    (531 : ℝ) / 2000 + 1 / 100000 ≤ FiniteBox.B hm := by
  apply eventual_B_ge_trial_limit trial_measurable trial_bound (P := 9)
  rw [thirdLimit_nine]
  exact nine_term_strict_margin

theorem eventual_B_strict : ∀ᶠ m : ℕ in atTop, ∀ hm : 0 < m,
    (531 : ℝ) / 2000 < FiniteBox.B hm := by
  filter_upwards [eventual_B_fixed_gap] with m hm hm0
  have h := hm hm0
  linarith

theorem exists_eventual_B_gap : ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ m : ℕ in atTop,
    ∀ hm : 0 < m, (531 : ℝ) / 2000 + ε ≤ FiniteBox.B hm :=
  ⟨1 / 100000, by norm_num, eventual_B_fixed_gap⟩

end StructuralNote.FixedDualClassificationTrialLowerBound
