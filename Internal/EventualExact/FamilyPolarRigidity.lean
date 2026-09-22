import EventualExact.GeometricScales
import EventualExact.PhysicalAngularGeometry
import EventualExact.FeketeStationarity
import EventualExact.PhysicalForceBudget

/-! Physical polar gap rigidity for genuine normalized Fekete families. -/

namespace Erdos1045.EventualExact.CoarseFekete

open Filter ExteriorClassical ExteriorBoundary Configuration CyclicAngles ExteriorSupport
open PhysicalAngularGeometry AngularHarmonicBound CyclicForceBudget FiniteCircleRigidity
open scoped Topology
noncomputable section

/-- The radii and heights here are the norms and logarithms of the actual nodes. -/
structure PhysicalGeometry {n : ℕ} {z : Points n} (d : ExteriorData z)
    (σ : Equiv.Perm (Fin n)) (a : Angles n) : Prop where
  angle_range : ∀ i : Fin n, 0 ≤ a.angle i ∧ a.angle i < 2 * Real.pi
  radius_lower : ∀ i : Fin n, 1 / 4 ≤ radius d σ i
  polar : ∀ i : Fin n, z (σ i) - center d = (radius d σ i : ℂ) * unit (a.angle i)
  height_bound : ∀ i k : Fin n, |height d σ i - height d σ k| ≤
    geometricEpsilon d * |shortAngle a i k|

theorem exists_physical_stationary_geometry {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (hn : 2 ≤ n) (hinj : Function.Injective z) (hf : Fekete z)
    (hc : 1 / 2 ≤ d.capacity) (he : errorRadius d ≤ 1 / 4) {γ : ℝ}
    (hsep : ∀ i k : Fin n, i ≠ k → γ / n ≤ ‖z i - z k‖) :
    ∃ (σ : Equiv.Perm (Fin n)) (a : Angles n) (slope : Fin n → ℝ),
      PhysicalGeometry d σ a ∧
      (∀ k : ℤ, (γ / 8) / n ≤ a.angle (k + 1) - a.angle k) ∧
      (∀ i, |slope i| ≤ geometricEpsilon d) ∧
      ∀ i, polarForceExpression (height d σ) (angleVector a) i (slope i) = 0 := by
  obtain ⟨σ, a, har, hp, hh, hgap⟩ :=
    physical_angular_geometry d HF hn hinj hc he hsep
  obtain ⟨ν, hν, hsupp⟩ := BoundarySupport.exists_node_unit_normals d HF (center d)
  have hr (i : Fin n) : 1 / 4 ≤ radius d σ i :=
    node_radius_pos d HF hc he (hν (σ i)) (σ i) (hsupp (σ i))
  have hpolar (i : Fin n) : z (σ i) = center d + polarPoint (height d σ i) (a.angle i) := by
    have hrpos : 0 < radius d σ i := lt_of_lt_of_le (by norm_num) (hr i)
    have hexp : polarPoint (height d σ i) (a.angle i) =
        (radius d σ i : ℂ) * unit (a.angle i) := by
      simp only [polarPoint, height, Real.exp_log hrpos, unit]
    rw [hexp]
    exact (sub_eq_iff_eq_add.mp (hp i)).trans (add_comm _ _)
  obtain ⟨slope, hslope, hstat⟩ :=
    FeketeStationarity.exists_stationary_slopes_permuted d HF hc he hinj hf
      (height d σ) a σ hpolar
  refine ⟨σ, a, slope, ⟨har, hr, hp, hh⟩, ?_, ?_, hstat⟩
  · intro k
    convert hgap k using 1
    ring
  · intro i
    exact (hslope i).trans (by unfold geometricEpsilon; nlinarith [Real.sqrt_nonneg (errorRadius d)])

/-- The finitely many indices outside the geometric regime require no choices
of valid polar coordinates; the original exterior angles supply a total fallback. -/
theorem Family.physical_polar_rigidity (s : Family) :
    ∃ (σ : ∀ j, Equiv.Perm (Fin (s.size j))) (a : ∀ j, Angles (s.size j)),
      (∀ᶠ j in atTop, PhysicalGeometry (s.data j) (σ j) (a j)) ∧
      Tendsto (fun j => ‖gapDeviation (a j)‖) atTop (𝓝 0) := by
  classical
  obtain ⟨C, γ, hC, hγ, hgood⟩ := s.eventual_geometric_bounds
  let Good (j : ℕ) : Prop :=
    (1 / 2 : ℝ) ≤ (s.data j).capacity ∧ errorRadius (s.data j) ≤ 1 / 4 ∧
    geometricEpsilon (s.data j) ≤ C * (s.size j : ℝ) ^ (-(1 / 2 : ℝ)) ∧
    ∀ i k : Fin (s.size j), i ≠ k → γ / s.size j ≤ ‖s.points j i - s.points j k‖
  have hchoices (j : ℕ) :
      ∃ (σ : Equiv.Perm (Fin (s.size j))) (a : Angles (s.size j))
        (slope : Fin (s.size j) → ℝ), Good j →
        PhysicalGeometry (s.data j) σ a ∧
        (∀ k : ℤ, (γ / 8) / s.size j ≤ a.angle (k + 1) - a.angle k) ∧
        (∀ i, |slope i| ≤ geometricEpsilon (s.data j)) ∧
        ∀ i, polarForceExpression (height (s.data j) σ) (angleVector a) i (slope i) = 0 := by
    by_cases hj : Good j
    · obtain ⟨σ, a, slope, h⟩ := exists_physical_stationary_geometry (s.data j)
        (s.identities j) (by have := s.size_ge j; omega) (s.injective j) (s.fekete j)
        hj.1 hj.2.1 hj.2.2.2
      exact ⟨σ, a, slope, fun _ => h⟩
    · exact ⟨Equiv.refl _, (s.data j).angles, fun _ => 0, fun h => (hj h).elim⟩
  choose σ a slope hchoice using hchoices
  have hvalid := hgood.mono fun j hj => hchoice j hj
  refine ⟨σ, a, hvalid.mono (fun _ h => h.1), ?_⟩
  apply PhysicalForceBudget.gapDeviation_tendsto_of_half_power a s.size_tendsto
    (fun j => height (s.data j) (σ j)) slope (fun j => geometricEpsilon (s.data j))
    (show 0 < γ / 8 by positivity) hC.le
  · exact Eventually.of_forall fun j => geometricEpsilon_nonneg (s.data j)
  · exact hgood.mono fun _ h => h.2.2.1
  · exact hvalid.mono fun _ h => h.2.1
  · filter_upwards [hvalid] with j hj
    exact fun i k _ => hj.1.height_bound i k
  · exact hvalid.mono fun _ h => h.2.2.1
  · exact hvalid.mono fun _ h => h.2.2.2

end
end Erdos1045.EventualExact.CoarseFekete
