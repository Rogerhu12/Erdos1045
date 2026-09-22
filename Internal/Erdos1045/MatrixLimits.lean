import Erdos1045.MatrixDirectLimits

/-!
# The two asymptotic uses of the same matrix stability theorem

Matrices may have a different size at every natural index.  Hence none of
the statements below silently fixes the dimension before taking a limit.
The coarse conclusion corresponds to Section 5.1; the vanishing conclusion
corresponds to Section 2.1 after the sharp trace estimate has been proved.
-/

namespace Erdos1045.MatrixDefect

open Filter
open scoped Topology
open Erdos1045.MatrixStability

noncomputable section

variable {N : ℕ → ℕ} (facts : ClassicalMatrixFacts) (A V : (j : ℕ) → Mat (N j))
include facts

/-- Vanishing logarithmic defect implies convergence of the actual Gram
matrix to the identity in squared Frobenius norm. -/
theorem tendsto_gram_frobSq
    (hA : ∀ᶠ n in atTop, (A n).det ≠ 0)
    (hD : Tendsto (fun n => defect (A n)) atTop (𝓝 0)) :
    Tendsto (fun n => frobSq (gram (A n) - 1)) atTop (𝓝 0) := by
  have hbound : Tendsto (fun n => (4 * defect (A n) + 6) * defect (A n))
      atTop (𝓝 0) := by
    convert ((hD.const_mul 4).add_const 6).mul hD using 1
    norm_num
  apply squeeze_zero' (Filter.Eventually.of_forall fun n => frobSq_nonneg _) _ hbound
  exact hA.mono fun n hn => gram_deviation_bound facts (A n) hn

theorem tendsto_gram_frob
    (hA : ∀ᶠ n in atTop, (A n).det ≠ 0)
    (hD : Tendsto (fun n => defect (A n)) atTop (𝓝 0)) :
    Tendsto (fun n => frob (gram (A n) - 1)) atTop (𝓝 0) := by
  have hsq := tendsto_gram_frobSq facts A hA hD
  simpa [frob, Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hsq

end

end Erdos1045.MatrixDefect
