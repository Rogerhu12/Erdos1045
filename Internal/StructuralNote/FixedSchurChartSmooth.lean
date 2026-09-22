import StructuralNote.FixedSchurEquationSmooth
import StructuralNote.FixedSchurStrictInterior
import StructuralNote.FixedSchurImplicitBanach

/-! Smooth dependence of the chosen root on the actual parameter domain.
An ambient implicit branch is identified with the chosen root by ball uniqueness. -/

namespace StructuralNote.FixedSchurChartSmooth

open Complex Filter Metric
open Erdos1045.EventualExact FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open CommonDomainClosure EdgeCoordinates FixedSchurData
open FixedSchurDomainSmallness FixedSchurEquations FixedSchurContraction
open FixedSchurExistence FixedSchurChart FixedSchurStrictInterior
open FixedSchurEquationSmooth FixedSchurImplicitBanach
open scoped Topology ContDiff

noncomputable section

def domain {m : ℕ} (hm : 0 < m) : Set (SchurParameters m) :=
  {x | InDomain hm x.1 x.2}

private theorem radicand_pos {t : ℝ} (ht : |t| < 2) : 0 < 4 - t ^ 2 := by
  nlinarith only [(abs_lt.mp ht).1, (abs_lt.mp ht).2]

theorem eventual_local_model : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (s : FiniteBox.SignPattern hm) (x : SchurParameters m),
      InDomain hm x.1 x.2 →
      ∃ g : SchurParameters m → SchurState m,
        g x = coordinate hm s x.1 x.2 ∧ ContDiffAt ℝ ∞ g x ∧
          (∀ᶠ y in 𝓝 x, equationMap hm y.1 y.2 (FiniteBox.patternSign s) (g y) = g y ∧
            ‖g y - baseWord (FiniteBox.patternSign s)‖ < radius (2 * m) ∧
            (InDomain hm y.1 y.2 → g y = coordinate hm s y.1 y.2)) := by
  filter_upwards [eventual_coordinate_interior, eventual_domain_smallness,
    eventual_coordinate_spec, eventual_ball_positive_input, eventual_coordinate_unique]
    with m hinter hsmall hspec hinput huniq
  intro hm s x hx
  have hp := hspec hm s x.1 x.2 hx
  have hs := hsmall hm x.1 x.2 _ hx (FiniteBox.patternSign_is_sign s)
  have hi := hinter hm s x.1 x.2 hx
  have hF : ContDiffAt ℝ ∞ (equationFamily hm (FiniteBox.patternSign s))
      (x, coordinate hm s x.1 x.2) := by
    apply equationFamily_contDiffAt
    intro j
    have hj := hinput hm x.1 x.2 _ hx (FiniteBox.patternSign_is_sign s) _ hp.1 j
    change 0 < 4 - (Y (by omega) x.1 j + FiniteBox.patternSign s j * epsilon (2 * m) *
      (tangent (by omega) x.2 j + J (coordinate hm s x.1 x.2) j)) ^ 2
    exact radicand_pos hj
  have hLip : LipschitzOnWith (1 / 2)
      (fun z => equationFamily hm (FiniteBox.patternSign s) (x, z))
      (closedBall (baseWord (FiniteBox.patternSign s)) (radius (2 * m))) := by
    exact crossingMap_lipschitz (show 0 < 2 * m by omega)
      (epsilon_pos (show 2 ≤ 2 * m by omega)) (X (by omega) x.1) (Y (by omega) x.1)
      (tangent (by omega) x.2) (FiniteBox.patternSign s) (baseWord (FiniteBox.patternSign s))
      (FiniteBox.patternSign_is_sign s) hs.2.2
  obtain ⟨g, hgx, hg, he⟩ := exists_smooth_fixedPoint
    (equationFamily hm (FiniteBox.patternSign s)) x (coordinate hm s x.1 x.2)
    (baseWord (FiniteBox.patternSign s)) hF hi hLip hp.2
  refine ⟨g, hgx, hg, ?_⟩
  filter_upwards [he] with y hy
  refine ⟨hy.1, hy.2, ?_⟩
  intro hyd
  exact huniq hm s y.1 y.2 hyd (g y) hy.2.le hy.1

theorem eventual_coordinate_contDiffWithinAt : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (s : FiniteBox.SignPattern hm) (x : SchurParameters m),
      x ∈ domain hm → ContDiffWithinAt ℝ ∞
        (fun y : SchurParameters m => coordinate hm s y.1 y.2) (domain hm) x := by
  filter_upwards [eventual_local_model] with m hmodel
  intro hm s x hx
  obtain ⟨g, hgx, hg, he⟩ := hmodel hm s x hx
  apply hg.contDiffWithinAt.congr_of_eventuallyEq _ hgx.symm
  filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with y hy hyd
  exact (hy.2.2 hyd).symm

end
end StructuralNote.FixedSchurChartSmooth
