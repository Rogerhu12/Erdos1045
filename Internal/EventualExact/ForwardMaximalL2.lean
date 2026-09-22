import EventualExact.ForwardMaximal
import EventualExact.FiniteLayercake

/-! Uniform strong L2 control of actual finite forward averages. -/

noncomputable section
open scoped BigOperators

namespace Erdos1045.EventualExact.ForwardMaximal

theorem square_sum_le {n : ℕ} (hn : 0 < n) (f : ℕ → ℝ)
    (hperiod : Function.Periodic f n) (hf : ∀ j, 0 ≤ f j) :
    (∑ j ∈ Finset.range n, maximal hn f j ^ 2) ≤
      16 * ∑ j ∈ Finset.range n, f j ^ 2 := by
  apply FiniteLayercake.square_sum_of_truncated_weak
  · exact fun j _ => maximal_nonneg hn f hf j
  · exact fun j _ => hf j
  · intro t ht
    simpa only [truncate] using truncated_weak_bound hn f hperiod hf ht

end Erdos1045.EventualExact.ForwardMaximal
