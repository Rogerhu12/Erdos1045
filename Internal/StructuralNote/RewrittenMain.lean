import StructuralNote.RewrittenMaxima
import StructuralNote.FixedSchurActualDiameterGraph
import StructuralNote.FixedSchurActualEuclideanSymmetry
import StructuralNote.RewrittenEvenPolynomialSelection
import StructuralNote.RewrittenEvenLimit
import StructuralNote.RewrittenOddLimit

/-! Principal conclusions of the rewritten manuscript.

The geometric endpoints retain the original point configuration, not only its
discriminant. `RewrittenMaxima.eventual_diameter_maximum_attained_unique`
states attainment and Euclidean uniqueness for the literal supremum.
`FixedSchurActualDiameterGraph.eventual_actual_extremizer_diameterGraph`
identifies its full diameter graph; that module supplies the complete cycle,
three pendant edges and the exact three arc lengths.
`FixedSchurActualEuclideanSymmetry` transports reflection and third-turn
symmetries to the original configuration.

`RewrittenEvenPolynomialSelection.eventual_even_maximum_single_polynomial_root`
gives the unique algebraic branch using a single polynomial inequality, with
the full stationary system, both nonsingular Jacobians and the exact maximum.
Odd diameter and perimeter values are the previously proved geometric results.
The localization proof is reused from the earlier unconditional project;
formalization of the new exposition's alternative capacity/Sturm argument is
not needed for these conclusions.
-/

namespace StructuralNote.RewrittenMain

open Erdos1045 Erdos1045.Configuration Erdos1045.HullGeometry
open FixedSchurActualRigidEquivalence Filter
open scoped Topology
noncomputable section

theorem eventual_perimeter_characterization :
    ∃ n₀ : ℕ, 4 ≤ n₀ ∧ ∀ n ≥ n₀,
      W n = (n : ℝ)^n * (Real.pi / (n * Real.sin (Real.pi / n)))^(n * (n - 1)) ∧
      (∃ z : Points n, hullPerimeter z ≤ 2 * Real.pi ∧ discriminant z = W n) ∧
      (∀ z : Points n, hullPerimeter z ≤ 2 * Real.pi → discriminant z = W n →
        Configuration.IsRegular z) ∧
      (∀ z w : Points n, hullPerimeter z ≤ 2 * Real.pi → discriminant z = W n →
        hullPerimeter w ≤ 2 * Real.pi → discriminant w = W n → DirectRigidRelabeling z w) := by
  obtain ⟨n₀, hn₀, hvalue⟩ := eventual_perimeter_maximum
  obtain ⟨n₁, _, hregular⟩ := eventual_perimeter_maximizer_regular
  obtain ⟨n₂, _, huniq⟩ := RewrittenMainUniqueness.eventual_perimeter_maximizers_unique
  refine ⟨max n₀ (max n₁ n₂), by omega, ?_⟩
  intro n hn
  exact ⟨hvalue n (by omega), RewrittenMaxima.W_attained (by omega),
    hregular n (by omega), huniq n (by omega)⟩

theorem normalized_limits :
    Tendsto (fun m : ℕ => M (2 * m) / (2 * m : ℝ)^(2 * m)) atTop
      (𝓝 ((3 : ℝ)^(9 / 4 : ℝ) / 8 *
        Real.exp ((Real.pi^2 - 2 * Real.sqrt 3 * Real.pi) / 8))) ∧
    Tendsto (fun m : ℕ => M (2 * m + 1) / (2 * m + 1 : ℝ)^(2 * m + 1)) atTop
      (𝓝 (Real.exp (Real.pi^2 / 8))) :=
  ⟨RewrittenEvenLimit.even_normalized_maximum_closed_form,
    RewrittenOddLimit.odd_normalized_maximum_tendsto⟩

end
end StructuralNote.RewrittenMain
