import StructuralNote.LensClosurePathDerivatives

/-! The second derivative of a closed lens path, including the actual implicit
acceleration. Its total variation costs at most nine times the direct source. -/

namespace StructuralNote.LensClosureAcceleration

open Erdos1045.EventualExact Complex LensClosure LensIncrementDerivatives
open LensClosurePathDerivatives Filter
open scoped BigOperators Topology
noncomputable section

def velocitySum {m : ℕ} (α L σ ν α' L' ν' : Fin m → ℝ) (ξ ξ' : ℂ) : ℂ :=
  ∑ j, incrementVelocity (α j) (L j) (σ j) (heightParameter ν ξ j)
    (α' j) (L' j) (heightParameter ν' ξ' j)

def source {m : ℕ} (α L σ ν α' L' ν' α'' L'' ν'' : Fin m → ℝ)
    (ξ ξ' : ℂ) (j : Fin m) : ℂ :=
  incrementAcceleration (α j) (L j) (σ j) (heightParameter ν ξ j)
    (α' j) (L' j) (heightParameter ν' ξ' j) (α'' j) (L'' j) (ν'' j)

theorem velocitySum_eq_zero {m : ℕ} {α L ν : ℝ → Fin m → ℝ}
    {ξ : ℝ → ℂ} {x : ℝ} (σ α' L' ν' : Fin m → ℝ) {ξ' : ℂ}
    (hα : ∀ j, HasDerivAt (fun s => α s j) (α' j) x)
    (hL : ∀ j, HasDerivAt (fun s => L s j) (L' j) x)
    (hν : ∀ j, HasDerivAt (fun s => ν s j) (ν' j) x) (hξ : HasDerivAt ξ ξ' x)
    (ht : ∀ j, heightParameter (ν x) (ξ x) j ^ 2 < 4)
    (hz : ∀ᶠ s in 𝓝 x, closure (α s) (L s) σ (ν s) (ξ s) = 0) :
    velocitySum (α x) (L x) σ (ν x) α' L' ν' (ξ x) ξ' = 0 := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    LensIncrementDerivatives.increment_hasDerivAt (σ j) (hα j) (hL j)
      (heightParameter_hasDerivAt hν hξ j) (ht j))
  have hc : HasDerivAt (fun s => closure (α s) (L s) σ (ν s) (ξ s)) 0 x :=
    (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq hz
  exact hd.unique hc

theorem velocitySum_hasDerivAt {m : ℕ} {α L ν α' L' ν' : ℝ → Fin m → ℝ}
    {ξ ξ' : ℝ → ℂ} {x : ℝ} (σ α'' L'' ν'' : Fin m → ℝ) {ξ'' : ℂ}
    (hα : ∀ j, HasDerivAt (fun s => α s j) (α' x j) x)
    (hL : ∀ j, HasDerivAt (fun s => L s j) (L' x j) x)
    (hν : ∀ j, HasDerivAt (fun s => ν s j) (ν' x j) x) (hξ : HasDerivAt ξ (ξ' x) x)
    (hα' : ∀ j, HasDerivAt (fun s => α' s j) (α'' j) x)
    (hL' : ∀ j, HasDerivAt (fun s => L' s j) (L'' j) x)
    (hν' : ∀ j, HasDerivAt (fun s => ν' s j) (ν'' j) x) (hξ' : HasDerivAt ξ' ξ'' x)
    (ht : ∀ j, heightParameter (ν x) (ξ x) j ^ 2 < 4) :
    HasDerivAt (fun s => velocitySum (α s) (L s) σ (ν s) (α' s) (L' s) (ν' s) (ξ s) (ξ' s))
      ((∑ j, source (α x) (L x) σ (ν x) (α' x) (L' x) (ν' x) α'' L'' ν'' (ξ x) (ξ' x) j) +
        closureDerivative (α x) σ (ν x) (ξ x) ξ'') x := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    incrementVelocity_hasDerivAt (σ j) (hα j) (hL j)
      (heightParameter_hasDerivAt hν hξ j) (hα' j) (hL' j)
      (heightParameter_hasDerivAt hν' hξ' j) rfl rfl rfl (ht j))
  change HasDerivAt
    (fun s => velocitySum (α s) (L s) σ (ν s) (α' s) (L' s) (ν' s) (ξ s) (ξ' s)) _ x at hd
  apply hd.congr_deriv
  simp only [heightParameter, acceleration_split, Finset.sum_add_distrib,
    closureDerivative_apply_sum, source]

/-- Ordinary differentiability of the actual parameter paths in a neighborhood;
no estimate or closure derivative identity is included in this hypothesis. -/
def FirstDerivatives {m : ℕ} (α L ν α' L' ν' : ℝ → Fin m → ℝ)
    (ξ ξ' : ℝ → ℂ) (x : ℝ) : Prop :=
  (∀ j, HasDerivAt (fun s => α s j) (α' x j) x) ∧
  (∀ j, HasDerivAt (fun s => L s j) (L' x j) x) ∧
  (∀ j, HasDerivAt (fun s => ν s j) (ν' x j) x) ∧ HasDerivAt ξ (ξ' x) x ∧
  ∀ j, heightParameter (ν x) (ξ x) j ^ 2 < 4

theorem closure_acceleration_eq {m : ℕ} {α L ν α' L' ν' : ℝ → Fin m → ℝ}
    {ξ ξ' : ℝ → ℂ} {x : ℝ} (σ α'' L'' ν'' : Fin m → ℝ) {ξ'' : ℂ}
    (hfirst : ∀ᶠ s in 𝓝 x, FirstDerivatives α L ν α' L' ν' ξ ξ' s)
    (hα' : ∀ j, HasDerivAt (fun s => α' s j) (α'' j) x)
    (hL' : ∀ j, HasDerivAt (fun s => L' s j) (L'' j) x)
    (hν' : ∀ j, HasDerivAt (fun s => ν' s j) (ν'' j) x) (hξ' : HasDerivAt ξ' ξ'' x)
    (hz : ∀ᶠ s in 𝓝 x, closure (α s) (L s) σ (ν s) (ξ s) = 0) :
    closureDerivative (α x) σ (ν x) (ξ x) ξ'' =
      -∑ j, source (α x) (L x) σ (ν x) (α' x) (L' x) (ν' x) α'' L'' ν'' (ξ x) (ξ' x) j := by
  obtain ⟨hα, hL, hν, hξ, ht⟩ := hfirst.self_of_nhds
  have hd := velocitySum_hasDerivAt σ α'' L'' ν'' hα hL hν hξ hα' hL' hν' hξ' ht
  have he : ∀ᶠ s in 𝓝 x,
      velocitySum (α s) (L s) σ (ν s) (α' s) (L' s) (ν' s) (ξ s) (ξ' s) = 0 := by
    filter_upwards [hfirst, hz.eventually_nhds] with s hs hzs
    exact velocitySum_eq_zero σ (α' s) (L' s) (ν' s) hs.1 hs.2.1 hs.2.2.1
      hs.2.2.2.1 hs.2.2.2.2 hzs
  have hc := (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq he
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hd.unique hc)

theorem closed_acceleration_l1 {m : ℕ} (hm : 2 ≤ m) {α L ν α' L' ν' : ℝ → Fin m → ℝ}
    {ξ ξ' : ℝ → ℂ} {x : ℝ} (σ α'' L'' ν'' : Fin m → ℝ) {ξ'' : ℂ}
    (hfirst : ∀ᶠ s in 𝓝 x, FirstDerivatives α L ν α' L' ν' ξ ξ' s)
    (hα' : ∀ j, HasDerivAt (fun s => α' s j) (α'' j) x)
    (hL' : ∀ j, HasDerivAt (fun s => L' s j) (L'' j) x)
    (hν' : ∀ j, HasDerivAt (fun s => ν' s j) (ν'' j) x) (hξ' : HasDerivAt ξ' ξ'' x)
    (hz : ∀ᶠ s in 𝓝 x, closure (α s) (L s) σ (ν s) (ξ s) = 0)
    (hσ : ∀ j, |σ j| ≤ 1)
    (hsmall : ∀ j, |α x j - midpoint m j| + |heightParameter (ν x) (ξ x) j| ≤ 1 / 4) :
    (∑ j, ‖incrementAcceleration (α x j) (L x j) (σ j) (heightParameter (ν x) (ξ x) j)
      (α' x j) (L' x j) (heightParameter (ν' x) (ξ' x) j)
      (α'' j) (L'' j) (heightParameter ν'' ξ'' j)‖) ≤
      9 * ∑ j, ‖source (α x) (L x) σ (ν x) (α' x) (L' x) (ν' x) α'' L'' ν'' (ξ x) (ξ' x) j‖ := by
  have heq := closure_acceleration_eq σ α'' L'' ν'' hfirst hα' hL' hν' hξ' hz
  have hb := corrected_source_l1 hm (α x) σ (ν x) (ξ x) ξ''
    (source (α x) (L x) σ (ν x) (α' x) (L' x) (ν' x) α'' L'' ν'' (ξ x) (ξ' x))
    hσ hsmall heq
  simpa only [source, heightParameter, acceleration_split] using hb

end
end StructuralNote.LensClosureAcceleration
