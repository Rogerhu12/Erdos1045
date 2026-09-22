import StructuralNote.RewrittenEvenPolynomialSelection
import StructuralNote.RewrittenMaxima

/-! The selected rational root is an actual feasible diameter maximizer, not
only an algebraic point whose discriminant has the right value. -/

namespace StructuralNote.RewrittenSelectedConfiguration

open Complex Filter
open Erdos1045 Erdos1045.Configuration Erdos1045.EventualExact
open RationalStationarySystem
open RationalCommonConfiguration
open FixedSchurChart FixedSchurChartGeometry
open FixedSchurCanonicalWordSymmetry
open FixedSchurRationalWindowDomain FixedSchurRationalWindowObjectiveTransfer
open FixedSchurRationalClosureMatrix CommonDomainRadius
open RewrittenEvenAlgebraicMaximum RewrittenMaxima
open scoped Topology

noncomputable section

/-- Literal window membership and closure already make the literal rational
configuration diameter-feasible. -/
theorem eventual_selectedWindow_diameterAtMost : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 8 ≤ m) (s : FiniteBox.SignPattern (by omega : 0 < m))
      (X : RationalConfiguration.Variables m → ℝ),
      selectedWindowEnergy (by omega) s X <
          (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
      RationalConfiguration.closure (by omega) (rationalSign s) X = 0 →
      DiameterAtMost 2
        (RationalConfiguration.configuration (by omega) (rationalSign s) X) := by
  filter_upwards [eventual_selectedWindow_inDomain,
    eventual_fixed_configuration_eq_rigid,
    eventual_geometric_properties] with m hdomain hrigid hgeometry
  intro hm s X hwindow hclosure
  let x := fixedSchurCoordinates (show 2 ≤ m by omega) s X
  let w := FixedSchurChart.configuration (by omega) s x.1 x.2
  let z := RationalConfiguration.configuration (by omega) (rationalSign s) X
  let u := LensClosure.unit (-angleMean (by omega) X)
  let c := centerMean (by omega) (rationalSign s) X
  have hx : x ∈ FixedSchurChartSmooth.domain (by omega) :=
    hdomain (show 2 ≤ m by omega) s X hwindow
  have hw : DiameterAtMost 2 w :=
    (hgeometry (show 2 ≤ m by omega) s x.1 x.2 hx).diameter
  have he : w = fun j => u * (z j - c) := by
    simpa only [x, w, z, u, c] using hrigid hm s X hwindow hclosure
  have hu : ‖u‖ = 1 := by
    simp only [u, LensClosure.norm_unit]
  intro i j
  calc
    ‖z i - z j‖ = ‖u * (z i - z j)‖ := by rw [norm_mul, hu, one_mul]
    _ = ‖u * (z i - c) - u * (z j - c)‖ := by congr 1; ring
    _ = ‖w i - w j‖ := by rw [congrFun he i, congrFun he j]
    _ ≤ 2 := hw i j

/-- Every canonical stationary root in the literal selected window is the
actual diameter extremizer represented by that root. -/
theorem eventual_canonical_selected_root_diameterExtremal :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ (hm : 3 ≤ m)
      (Y : RationalStationarySystem.Variables m → ℝ),
      let s := canonicalPattern hm
      selectedWindowEnergy (by omega) s (coordinates Y) <
          (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
      Stationary (by omega) (halfWord s) Y →
      ExtremalNormalization.DiameterExtremal
        (RationalConfiguration.configuration (by omega) (rationalSign s)
          (coordinates Y)) := by
  obtain ⟨m₀, hroot⟩ := eventual_even_maximum_selected_root
  obtain ⟨m₁, hfeasible⟩ := eventually_atTop.1
    eventual_selectedWindow_diameterAtMost
  refine ⟨max (max m₀ m₁) 8, ?_⟩
  intro m hm hm3 Y
  dsimp only
  intro hwindow hstationary
  obtain ⟨hm3', Y', hwindow', hstationary', hunique, hM, halgebraic⟩ :=
    hroot m (by omega)
  have hYY : Y = Y' := hunique Y hwindow hstationary
  subst Y'
  have hclosure : RationalConfiguration.closure (by omega)
      (rationalSign (canonicalPattern hm3)) (coordinates Y) = 0 := by
    rw [← sign_halfWord]
    exact hstationary.1
  have hdiam := hfeasible m (by omega) (show 8 ≤ m by omega)
    (canonicalPattern hm3) (coordinates Y) hwindow hclosure
  apply (diameterExtremal_iff_attains (show 0 < 2 * m by omega) _).2
  exact ⟨hdiam, hM.symm⟩

/-- A single endpoint collecting existence, uniqueness in the selected
stationary window, actual extremality, and the exact maximum identity. -/
theorem eventual_exists_selected_actual_maximizer :
    ∃ m₀ : ℕ, ∀ m ≥ m₀,
      ∃ (hm : 3 ≤ m) (Y : RationalStationarySystem.Variables m → ℝ),
        let s := canonicalPattern hm
        selectedWindowEnergy (by omega) s (coordinates Y) <
            (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) ∧
        Stationary (by omega) (halfWord s) Y ∧
        (∀ Z : RationalStationarySystem.Variables m → ℝ,
          selectedWindowEnergy (by omega) s (coordinates Z) <
              (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
          Stationary (by omega) (halfWord s) Z → Z = Y) ∧
        ExtremalNormalization.DiameterExtremal
          (RationalConfiguration.configuration (by omega) (rationalSign s)
            (coordinates Y)) ∧
        M (2 * m) = discriminant
          (RationalConfiguration.configuration (by omega) (rationalSign s)
            (coordinates Y)) ∧
        IsAlgebraic ℚ (M (2 * m)) := by
  obtain ⟨m₀, hroot⟩ := eventual_even_maximum_selected_root
  obtain ⟨m₁, hactual⟩ := eventual_canonical_selected_root_diameterExtremal
  refine ⟨max m₀ m₁, ?_⟩
  intro m hm
  obtain ⟨hm3, Y, hwindow, hstationary, hunique, hM, halgebraic⟩ :=
    hroot m (by omega)
  have hmax := hactual m (by omega) hm3 Y hwindow hstationary
  exact ⟨hm3, Y, hwindow, hstationary, hunique, hmax, hM, halgebraic⟩

end
end StructuralNote.RewrittenSelectedConfiguration
