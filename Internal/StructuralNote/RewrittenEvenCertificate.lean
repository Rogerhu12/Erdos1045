import StructuralNote.RewrittenSelectedConfiguration

/-! A single certificate joins the literal polynomial prescription to the
actual geometric maximum. All fields are conclusions of an unconditional
eventual existence theorem. -/

namespace StructuralNote.RewrittenEvenCertificate

open Filter MvPolynomial Erdos1045 Erdos1045.Configuration
open Erdos1045.EventualExact FixedSchurRationalWindowDomain
open RationalExpressions RationalStationarySystem
open FixedSchurRationalClosureMatrix FixedSchurCanonicalWordSymmetry
open FixedSchurRationalWindowPolynomial FixedSchurRationalStationarySelection
open RewrittenEvenPolynomialSelection RewrittenSelectedConfiguration
open CommonDomainRadius
open scoped Topology
noncomputable section

structure Certificate (m : ℕ) where
  large : 3 ≤ m
  root : RationalStationarySystem.Variables m → ℝ
  window : MvPolynomial (RationalConfiguration.Variables m) Coeff
  dimension : Fintype.card (RationalStationarySystem.Variables m) = 2 * m + 1
  window_spec : ∀ X : RationalConfiguration.Variables m → ℝ,
    (selectedWindowEnergy (by omega) (canonicalPattern large) X <
      (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) ↔ 0 < aeval X window)
  in_window : 0 < aeval (coordinates root) window
  stationary : Stationary (by omega) (halfWord (canonicalPattern large)) root
  polynomial_root : ∀ q,
    aeval root (polynomials (by omega) (halfWord (canonicalPattern large)) q) = 0
  system_iff : ∀ Y : RationalStationarySystem.Variables m → ℝ,
    0 < aeval (coordinates Y) window →
    ((∀ q, aeval Y (polynomials (by omega) (halfWord (canonicalPattern large)) q) = 0) ↔
      Stationary (by omega) (halfWord (canonicalPattern large)) Y)
  unique_root : ∀ Y : RationalStationarySystem.Variables m → ℝ,
    0 < aeval (coordinates Y) window →
    (∀ q, aeval Y (polynomials (by omega) (halfWord (canonicalPattern large)) q) = 0) →
    Y = root
  rational_nonsingular : (RationalSystemAlgebraicity.jacobian
    (systemExpression (by omega) (halfWord (canonicalPattern large))) root).det ≠ 0
  polynomial_nonsingular : (PolynomialAlgebraicity.jacobian
    (polynomials (by omega) (halfWord (canonicalPattern large))) root).det ≠ 0
  algebraic : ∀ q, IsAlgebraic ℚ (root q)
  geometric_algebraic : ∀ j,
    IsAlgebraic ℚ (RationalConfiguration.configuration (by omega)
      (rationalSign (canonicalPattern large)) (coordinates root) j).re ∧
    IsAlgebraic ℚ (RationalConfiguration.configuration (by omega)
      (rationalSign (canonicalPattern large)) (coordinates root) j).im
  distances_algebraic : ∀ i j, IsAlgebraic ℚ
    ‖RationalConfiguration.configuration (by omega)
        (rationalSign (canonicalPattern large)) (coordinates root) i -
      RationalConfiguration.configuration (by omega)
        (rationalSign (canonicalPattern large)) (coordinates root) j‖
  extremal : ExtremalNormalization.DiameterExtremal
    (RationalConfiguration.configuration (by omega)
      (rationalSign (canonicalPattern large)) (coordinates root))
  maximum : M (2 * m) = discriminant
    (RationalConfiguration.configuration (by omega)
      (rationalSign (canonicalPattern large)) (coordinates root))
  maximum_algebraic : IsAlgebraic ℚ (M (2 * m))

theorem eventual_certificate : ∀ᶠ m : ℕ in atTop, Nonempty (Certificate m) := by
  obtain ⟨m₀, hroot⟩ := eventual_exists_selected_actual_maximizer
  filter_upwards [eventually_ge_atTop m₀, eventually_ge_atTop 8,
    eventual_exists_selectedWindowPolynomial,
    eventual_window_polynomial_system_iff,
    eventual_selectedWindow_stationary_algebraic] with
      m hm hm8 hpoly hiff halg
  obtain ⟨hm3, Y, hwindow, hstationary, hunique, hextremal, hM, hMalg⟩ := hroot m hm
  let s := canonicalPattern hm3
  obtain ⟨P, hP⟩ := hpoly (show 2 ≤ m by omega) s
  have hi := hiff hm8 s P hP
  obtain ⟨hJ, hzero, hPJ, hYalg, hzalg, hdalg, _⟩ :=
    halg hm8 s Y hwindow hstationary
  refine ⟨{
    large := hm3
    root := Y
    window := P
    dimension := variables_card (by omega)
    window_spec := hP
    in_window := (hP (coordinates Y)).1 hwindow
    stationary := hstationary
    polynomial_root := hzero
    system_iff := hi
    unique_root := ?_
    rational_nonsingular := hJ
    polynomial_nonsingular := hPJ
    algebraic := hYalg
    geometric_algebraic := hzalg
    distances_algebraic := hdalg
    extremal := hextremal
    maximum := hM
    maximum_algebraic := hMalg }⟩
  intro Z hZwindow hZzero
  exact hunique Z ((hP (coordinates Z)).2 hZwindow) ((hi Z hZwindow).1 hZzero)

end
end StructuralNote.RewrittenEvenCertificate
