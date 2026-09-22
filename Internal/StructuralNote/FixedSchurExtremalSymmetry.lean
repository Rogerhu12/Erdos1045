import StructuralNote.FixedSchurGeometricStationarity
import StructuralNote.FixedSchurCyclicEquivariance
import StructuralNote.FixedSchurReflectionEquivariance

/-! Rigid alignment and forced symmetries of actual fixed-Schur extremizers.

The word action and the geometric action are kept explicit.  The eventual
statements use strict concavity only after both configurations have been
transported into the same selected-word fiber.
-/

namespace StructuralNote.FixedSchurExtremalSymmetry

open Complex Filter
open Erdos1045 Erdos1045.Configuration Erdos1045.HullGeometry
open Erdos1045.EventualExact Erdos1045.EventualExact.FiniteBox
open Erdos1045.EventualExact.FourierMultiplier
open FixedSchurChart FixedSchurEquationSmooth FixedSchurChartSmooth
open FixedSchurGeometricStationarity
open FixedSchurCyclicEquivariance FixedSchurReflectionEquivariance
open SignPatternSymmetry
open scoped Topology

noncomputable section

local notation "conj" => (starRingEnd ℂ)

theorem diameterAtMost_cyclicCenter {n : ℕ} (k : ℕ) {d : ℝ}
    {z : Points n} (hz : DiameterAtMost d z) :
    DiameterAtMost d (cyclicCenter k z) := by
  intro i j
  rw [show cyclicCenter k z i - cyclicCenter k z j =
      conj (LocalPhase.regularRoot n ^ k) *
        (z (cyclicIndex n k i) - z (cyclicIndex n k j)) by
    simp only [cyclicCenter]
    ring,
    norm_mul, norm_conj, norm_pow, ClosedFourier.root_norm, one_pow, one_mul]
  exact hz _ _

theorem discriminant_cyclicCenter {n : ℕ} (k : ℕ) (z : Points n) :
    discriminant (cyclicCenter k z) = discriminant z := by
  let u : ℂ := conj (LocalPhase.regularRoot n ^ k)
  have hfun : cyclicCenter k z =
      fun j => 0 + u * (z ∘ cyclicIndex n k) j := by
    funext j
    simp only [cyclicCenter, u, Function.comp_apply, zero_add]
  rw [hfun, discriminant_affine, discriminant_perm]
  have hu : ‖u‖ = 1 := by
    simp only [u, norm_conj, norm_pow, ClosedFourier.root_norm, one_pow]
  rw [hu, one_pow, one_mul]

theorem diameterExtremal_cyclicCenter {n : ℕ} (k : ℕ) {z : Points n}
    (hz : ExtremalNormalization.DiameterExtremal z) :
    ExtremalNormalization.DiameterExtremal (cyclicCenter k z) := by
  refine ⟨diameterAtMost_cyclicCenter k hz.1, ?_⟩
  intro w hw
  rw [discriminant_cyclicCenter]
  exact hz.2 w hw

theorem diameterAtMost_reflectCenter {n : ℕ} {d : ℝ} {z : Points n}
    (hz : DiameterAtMost d z) : DiameterAtMost d (reflectCenter z) := by
  intro i j
  rw [show reflectCenter z i - reflectCenter z j =
      conj (z (vertexReflection n i) - z (vertexReflection n j)) by
    simp only [reflectCenter, map_sub]]
  rw [norm_conj]
  exact hz _ _

theorem discriminant_reflectCenter {n : ℕ} (z : Points n) :
    discriminant (reflectCenter z) = discriminant z := by
  have hfun : discriminant (reflectCenter z) =
      discriminant (z ∘ vertexReflection n) := by
    unfold discriminant
    apply Finset.prod_congr rfl
    intro i _
    apply Finset.prod_congr rfl
    intro j _
    simp only [reflectCenter, Function.comp_apply, ← map_sub, norm_conj]
  exact hfun.trans (discriminant_perm z (vertexReflection n))

theorem diameterExtremal_reflectCenter {n : ℕ} {z : Points n}
    (hz : ExtremalNormalization.DiameterExtremal z) :
    ExtremalNormalization.DiameterExtremal (reflectCenter z) := by
  refine ⟨diameterAtMost_reflectCenter hz.1, ?_⟩
  intro w hw
  rw [discriminant_reflectCenter]
  exact hz.2 w hw

/-- Cyclically related words have rigidly related extremal chart parameters.
This is an alignment theorem: the two finite words are not identified until
the cyclic action has actually been applied. -/
theorem eventual_cyclic_aligned_extremal_unique : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (k : ℕ) (s : SignPattern (by omega))
      (x y : SchurParameters m),
      x ∈ domain (by omega) → y ∈ domain (by omega) →
      ExtremalNormalization.DiameterExtremal
        (configuration (by omega) s x.1 x.2) →
      ExtremalNormalization.DiameterExtremal
        (configuration (by omega) (rotatePattern k s) y.1 y.2) →
      (cyclicReal k x.1, cyclicCenter k x.2) = y := by
  filter_upwards [eventual_same_word_extremal_unique,
    eventual_configuration_cyclic] with m huniq hcfg
  intro hm k s x y hx hy hxmax hymax
  have hxy : (cyclicReal k x.1, cyclicCenter k x.2) ∈ domain (by omega) :=
    inDomain_cyclic (by omega) k x.1 x.2 hx
  have htrans : ExtremalNormalization.DiameterExtremal
      (configuration (by omega) (rotatePattern k s)
        (cyclicReal k x.1) (cyclicCenter k x.2)) := by
    rw [hcfg hm k s x.1 x.2 hx]
    exact diameterExtremal_cyclicCenter k hxmax
  exact huniq hm (rotatePattern k s)
    (cyclicReal k x.1, cyclicCenter k x.2) hxy y hy htrans hymax

/-- Reflected words have rigidly reflected extremal chart parameters. -/
theorem eventual_reflection_aligned_extremal_unique : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : SignPattern (by omega)) (x y : SchurParameters m),
      x ∈ domain (by omega) → y ∈ domain (by omega) →
      ExtremalNormalization.DiameterExtremal
        (configuration (by omega) s x.1 x.2) →
      ExtremalNormalization.DiameterExtremal
        (configuration (by omega) (reflectPattern s) y.1 y.2) →
      (reflectReal x.1, reflectCenter x.2) = y := by
  filter_upwards [eventual_same_word_extremal_unique,
    eventual_configuration_reflect] with m huniq hcfg
  intro hm s x y hx hy hxmax hymax
  have hxy : (reflectReal x.1, reflectCenter x.2) ∈ domain (by omega) :=
    inDomain_reflect hm x.1 x.2 hx
  have htrans : ExtremalNormalization.DiameterExtremal
      (configuration (by omega) (reflectPattern s)
        (reflectReal x.1) (reflectCenter x.2)) := by
    rw [hcfg hm s x.1 x.2 hx]
    exact diameterExtremal_reflectCenter hxmax
  exact huniq hm (reflectPattern s)
    (reflectReal x.1, reflectCenter x.2) hxy y hy htrans hymax

/-- A cyclic stabilizer of the selected word fixes the unique extremal chart
parameter after the compensating physical rotation. -/
theorem eventual_cyclic_forced_parameters : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (k : ℕ) (s : SignPattern (by omega))
      (x : SchurParameters m),
      x ∈ domain (by omega) →
      ExtremalNormalization.DiameterExtremal
        (configuration (by omega) s x.1 x.2) →
      rotatePattern k s = s →
      (cyclicReal k x.1, cyclicCenter k x.2) = x := by
  filter_upwards [eventual_cyclic_aligned_extremal_unique] with m halign
  intro hm k s x hx hmax hword
  apply halign hm k s x x hx hx hmax
  rwa [hword]

theorem eventual_cyclic_forced_configuration : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (k : ℕ) (s : SignPattern (by omega))
      (x : SchurParameters m),
      x ∈ domain (by omega) →
      ExtremalNormalization.DiameterExtremal
        (configuration (by omega) s x.1 x.2) →
      rotatePattern k s = s →
      configuration (by omega) s x.1 x.2 =
        cyclicCenter k (configuration (by omega) s x.1 x.2) := by
  filter_upwards [eventual_cyclic_forced_parameters,
    eventual_configuration_cyclic] with m hparam hcfg
  intro hm k s x hx hmax hword
  have hp := hparam hm k s x hx hmax hword
  have hc := hcfg hm k s x.1 x.2 hx
  have hp1 : cyclicReal k x.1 = x.1 := by
    simpa using congrArg Prod.fst hp
  have hp2 : cyclicCenter k x.2 = x.2 := by
    simpa using congrArg Prod.snd hp
  rw [hword, hp1, hp2] at hc
  exact hc

/-- A reflection stabilizer of the selected word forces the actual reflected
symmetry of the unique extremal chart parameter. -/
theorem eventual_reflection_forced_parameters : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : SignPattern (by omega)) (x : SchurParameters m),
      x ∈ domain (by omega) →
      ExtremalNormalization.DiameterExtremal
        (configuration (by omega) s x.1 x.2) →
      reflectPattern s = s →
      (reflectReal x.1, reflectCenter x.2) = x := by
  filter_upwards [eventual_reflection_aligned_extremal_unique] with m halign
  intro hm s x hx hmax hword
  apply halign hm s x x hx hx hmax
  rwa [hword]

theorem eventual_reflection_forced_configuration : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : SignPattern (by omega)) (x : SchurParameters m),
      x ∈ domain (by omega) →
      ExtremalNormalization.DiameterExtremal
        (configuration (by omega) s x.1 x.2) →
      reflectPattern s = s →
      configuration (by omega) s x.1 x.2 =
        reflectCenter (configuration (by omega) s x.1 x.2) := by
  filter_upwards [eventual_reflection_forced_parameters,
    eventual_configuration_reflect] with m hparam hcfg
  intro hm s x hx hmax hword
  have hp := hparam hm s x hx hmax hword
  have hc := hcfg hm s x.1 x.2 hx
  have hp1 : reflectReal x.1 = x.1 := by
    simpa using congrArg Prod.fst hp
  have hp2 : reflectCenter x.2 = x.2 := by
    simpa using congrArg Prod.snd hp
  rw [hword, hp1, hp2] at hc
  exact hc

end
end StructuralNote.FixedSchurExtremalSymmetry
