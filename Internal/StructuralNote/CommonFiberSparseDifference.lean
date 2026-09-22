import StructuralNote.CommonClosureIncrements
import StructuralNote.CommonFiberCanonical
import StructuralNote.CommonFiberNonlocalSizes
import StructuralNote.CommonFiberDifferentialEstimate

/-! Actual root and increment differences for two words at identical continuous
parameters. The support of the word change controls the full nonlinear error. -/

namespace StructuralNote.CommonFiberSparseDifference

open Erdos1045 Erdos1045.EventualExact Complex Filter LensClosure
open CommonClosureEnergy CommonTangentialParameters CommonDomainClosure CommonDomainRadius
open CommonFiberGeometry CommonFiberSmooth CommonFiberCanonical CommonFiberBounds
open CommonFiberNonlocalSizes CommonFiberDifferentialEstimate CommonClosureDifference
open CommonFiberSmallCoefficients
open scoped BigOperators Topology
noncomputable section

theorem actual_sparse_difference {m : ℕ} (hm : 128 ≤ m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) (σ τ : Fin m → ℝ) (ξ η : ℂ)
    (hdom : InDomain (by omega) θ v) (hσ : ∀ j, |σ j| ≤ 1) (hτ : ∀ j, |τ j| ≤ 1)
    (hξ : ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2) (hη : ‖η‖ ≤ 1024 / (2 * m : ℝ) ^ 2)
    (hξz : closure (phase (by omega) θ) (fun j => 2 * Real.cos (halfAngle (by omega) θ j))
      σ (coordinates (by omega) v) ξ = 0)
    (hηz : closure (phase (by omega) θ) (fun j => 2 * Real.cos (halfAngle (by omega) θ j))
      τ (coordinates (by omega) v) η = 0)
    (hscale : energyRadius (2 * m) ≤ 1 / (2 * m : ℝ))
    (horder : 10 * (logOrder (2 * m) : ℝ) + 1024 ≤ 2 * m)
    (hθ : ∀ j, |θ j| ≤ 1 / (1000 * (2 * m : ℝ)))
    (J : Finset (Fin m)) (hagree : ∀ j, j ∉ J → σ j = τ j) :
    ‖ξ - η‖ ≤ 160 * J.card / (2 * m : ℝ) ^ 3 ∧
      (∑ j, ‖fiberIncrement (by omega) θ v σ ξ j - fiberIncrement (by omega) θ v τ η j‖) ≤
        180 * J.card / (2 * m : ℝ) ^ 2 := by
  obtain ⟨hθE, hvE⟩ := domain_energy_bounds (by omega) θ v hdom
  have hsmall (j : Fin m) : |phase (by omega) θ j - midpoint m j| +
      |coordinates (by omega) v j| + 1024 / (2 * m : ℝ) ^ 2 ≤ 1 / 4 := by
    have hs := double_radius_small hm σ (θ, v) hdom.2.1
      (hθE.trans hscale) (hvE.trans hscale) j
    simp only [data] at hs
    have hR : 0 ≤ (1024 : ℝ) / (2 * m : ℝ) ^ 2 := by positivity
    linarith
  have hwidth (j : Fin m) (_ : j ∈ J) :
      |Lens.width (2 * Real.cos (halfAngle (by omega) θ j))
        (heightParameter (coordinates (by omega) v) η j)| ≤ 10 / (2 * m : ℝ) ^ 2 := by
    obtain ⟨hw0, hw⟩ := radial_width_bound (by omega : 8 ≤ m) θ v hdom hη horder hθ j
    rwa [abs_of_nonneg hw0]
  have hroot := root_sparse_word_difference (by omega : 2 ≤ m) (phase (by omega) θ)
    (fun j => 2 * Real.cos (halfAngle (by omega) θ j)) σ τ (coordinates (by omega) v)
    hσ hτ hsmall hξ hη hξz hηz J hagree hwidth
  have hinc := increment_difference_sum (by omega : 2 ≤ m) (phase (by omega) θ)
    (fun j => 2 * Real.cos (halfAngle (by omega) θ j)) σ τ (coordinates (by omega) v)
    hσ hτ hsmall hξ hη hξz hηz J hagree hwidth
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  constructor
  · exact hroot.trans_eq (by field_simp; ring)
  · exact hinc.trans_eq (by ring)

theorem eventual_canonical_sparse_difference : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
      (σ τ : Fin m → ℝ), InDomain hm θ v → (∀ j, |σ j| ≤ 1) → (∀ j, |τ j| ≤ 1) →
    ∀ (J : Finset (Fin m)), (∀ j, j ∉ J → σ j = τ j) →
    ‖root hm σ (θ, v) - root hm τ (θ, v)‖ ≤ 160 * J.card / (2 * m : ℝ) ^ 3 ∧
      (∑ j, ‖fiberIncrement hm θ v σ (root hm σ (θ, v)) j -
        fiberIncrement hm θ v τ (root hm τ (θ, v)) j‖) ≤ 180 * J.card / (2 * m : ℝ) ^ 2 := by
  have hnat : Tendsto (fun m : ℕ => 2 * m) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with m hm
    omega
  filter_upwards [eventual_size_conditions, hnat.eventually eventual_small_coefficients] with m hs hn
  intro hm θ v σ τ hdom hσ hτ J hagree
  have hrootσ := root_spec hs.1 σ (θ, v) hs.2.1 hσ hdom
  have hrootτ := root_spec hs.1 τ (θ, v) hs.2.1 hτ hdom
  have hθ (j : Fin (2 * m)) : |θ j| ≤ 1 / (1000 * (2 * m : ℝ)) := by
    have hb := domain_theta_bound hm θ v hdom j
    exact hb.trans (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hn.2.2.1)
  exact actual_sparse_difference hs.1 θ v σ τ _ _ hdom hσ hτ
    hrootσ.1 hrootτ.1 hrootσ.2 hrootτ.2 hs.2.1 hs.2.2.1 hθ J hagree

end
end StructuralNote.CommonFiberSparseDifference
