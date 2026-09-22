import StructuralNote.FixedSchurExistence

/-! A chosen fixed-Schur coordinate and its geometric identities.  Full
feasibility and the absence of additional diameter edges are separate results. -/

namespace StructuralNote.FixedSchurChart

open Complex Filter
open Erdos1045.EventualExact FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open CommonDomainClosure EdgeCoordinates FixedSchurData FixedSchurLinear FixedSchurEdgeGeometry
open FixedSchurDomainSmallness FixedSchurEquations FixedSchurExistence
open scoped BigOperators Topology

noncomputable section

def coordinate {m : ℕ} (hm : 0 < m) (s : FiniteBox.SignPattern hm)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) : Fin (2 * m) → ℝ := by
  classical
  exact if h : ∃ q : Fin (2 * m) → ℝ,
      ‖q - baseWord (FiniteBox.patternSign s)‖ ≤ radius (2 * m) ∧
      equationMap hm θ v (FiniteBox.patternSign s) q = q then h.choose
    else baseWord (FiniteBox.patternSign s)

def configuration {m : ℕ} (hm : 0 < m) (s : FiniteBox.SignPattern hm)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) : Fin (2 * m) → ℂ :=
  vertex θ (center (coordinate hm s θ v) v)

theorem coordinate_spec_of_exists {m : ℕ} (hm : 0 < m) (s : FiniteBox.SignPattern hm)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (hex : ∃ q : Fin (2 * m) → ℝ,
      ‖q - baseWord (FiniteBox.patternSign s)‖ ≤ radius (2 * m) ∧
      equationMap hm θ v (FiniteBox.patternSign s) q = q) :
    ‖coordinate hm s θ v - baseWord (FiniteBox.patternSign s)‖ ≤ radius (2 * m) ∧
      equationMap hm θ v (FiniteBox.patternSign s) (coordinate hm s θ v) = coordinate hm s θ v := by
  classical
  simp only [coordinate, dif_pos hex]
  exact hex.choose_spec

theorem eventual_coordinate_spec : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (s : FiniteBox.SignPattern hm) (θ : Fin (2 * m) → ℝ)
      (v : Fin (2 * m) → ℂ), InDomain hm θ v →
      ‖coordinate hm s θ v - baseWord (FiniteBox.patternSign s)‖ ≤ radius (2 * m) ∧
        equationMap hm θ v (FiniteBox.patternSign s) (coordinate hm s θ v) = coordinate hm s θ v := by
  filter_upwards [eventual_signPattern_root] with m he
  intro hm s θ v hdom
  exact coordinate_spec_of_exists hm s θ v (he hm s θ v hdom).exists

structure Properties {m : ℕ} (hm : 2 ≤ m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ q : Fin (2 * m) → ℝ) : Prop where
  close : ‖q - baseWord σ‖ ≤ radius (2 * m)
  fixed : equationMap (by omega) θ v σ q = q
  antiperiodic : FiniteBox.Antiperiodic (by omega) q
  norm_le : ‖q‖ ≤ 5
  mean_zero : ∑ j, center q v j = 0
  normal : constraint (by omega) (center q v) = q
  free_projection : projection hm (center q v) = v
  quadratic : pairPotential (by omega) (center q v) =
    normalizedBoxEnergy (operator (2 * m)) q + pairPotential (by omega) v
  positive : ∀ j, 0 < X (by omega) θ j + σ j * epsilon (2 * m) * q j
  matching : ∀ j, ‖vertex θ (center q v) j - vertex θ (center q v) (halfTurn (by omega) j)‖ = 2
  selected : ∀ j, ‖crossingVector hm θ (center q v) σ j‖ = 2

theorem eventual_coordinate_properties : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega)) (θ : Fin (2 * m) → ℝ)
      (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      Properties hm θ v (FiniteBox.patternSign s) (coordinate (by omega) s θ v) := by
  filter_upwards [eventual_coordinate_spec, eventual_ball_positive_input,
    eventual_domain_smallness] with m hspec hin hsmall
  intro hm s θ v hdom
  have hq := hspec (by omega) s θ v hdom
  have hs := FiniteBox.patternSign_is_sign s
  have harg := hin (by omega) θ v _ hdom hs _ hq.1
  have hanti := solution_antiperiodic (by omega) θ v _ _ hdom.1 hdom.2.2.1.1
    (FiniteBox.patternSign_antiperiodic s) hq.2
  have hnorm : ‖coordinate (by omega) s θ v‖ ≤ 5 := by
    have hb := baseWord_norm_le_four (show 2 ≤ 2 * m by omega) hs
    have hr := (hsmall (by omega) θ v _ hdom hs).2.1
    have ht := norm_sub_norm_le (coordinate (by omega) s θ v) (baseWord (FiniteBox.patternSign s))
    linarith [hq.1]
  refine ⟨hq.1, hq.2, hanti, hnorm,
    center_mean_zero hm _ v hdom.2.2.1.2.1,
    center_constraint hm _ v hdom.2.2.1.2.2,
    projection_center hm _ v hdom.2.2.1.2.2,
    center_pairPotential hm _ v hanti hdom.2.2.1.1 hdom.2.2.1.2.2, ?_, ?_, ?_⟩
  · intro j
    exact (solution_positive_branch (by omega) θ v _ _ hs hq.2 harg j).1
  · intro j
    exact vertex_antipodal_norm hm θ _ v hdom.1 hanti hdom.2.2.1.1 j
  · intro j
    exact solution_selected_edge hm θ v _ _ hdom.2.2.1.2.2 hs hq.2 harg j

theorem eventual_coordinate_unique : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (s : FiniteBox.SignPattern hm) (θ : Fin (2 * m) → ℝ)
      (v : Fin (2 * m) → ℂ), InDomain hm θ v →
      ∀ q : Fin (2 * m) → ℝ, ‖q - baseWord (FiniteBox.patternSign s)‖ ≤ radius (2 * m) →
        equationMap hm θ v (FiniteBox.patternSign s) q = q → q = coordinate hm s θ v := by
  filter_upwards [eventual_signPattern_root] with m he
  intro hm s θ v hdom q hq hfix
  have hu := he hm s θ v hdom
  exact hu.unique ⟨hq, hfix⟩ (coordinate_spec_of_exists hm s θ v hu.exists)

end
end StructuralNote.FixedSchurChart
