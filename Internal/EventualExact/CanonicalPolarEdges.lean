import EventualExact.PhysicalAngularGeometry
import EventualExact.RadialEdges

/-! Actual sorted physical radii satisfy the finite relative-edge criterion. -/

namespace Erdos1045.EventualExact.CanonicalPolarEdges

open Complex Set CyclicAngles ExteriorClassical ExteriorBoundary Configuration
open ExteriorSupport PhysicalAngularGeometry
noncomputable section

def index {n : ℕ} (hn : 0 < n) (j : ℕ) : Fin n := ⟨j % n, Nat.mod_lt _ hn⟩

def radii {n : ℕ} {z : Points n} (d : ExteriorData z) (σ : Equiv.Perm (Fin n))
    (hn : 0 < n) (j : ℕ) : ℝ := radius d σ (index hn j)

theorem radii_periodic {n : ℕ} {z : Points n} (d : ExteriorData z)
    (σ : Equiv.Perm (Fin n)) (hn : 0 < n) : Function.Periodic (radii d σ hn) n := by
  intro j
  simp [radii, index]

theorem unit_angle_mod {n : ℕ} (a : Angles n) (hn : 0 < n) (j : ℕ) :
    unit (a.angle j) = unit (a.angle (index hn j)) := by
  have hp : Function.Periodic (fun j : ℕ => unit (a.angle j)) n := by
    intro k
    simp only [Nat.cast_add, a.period, unit_add]
    have hunit : unit (2 * Real.pi) = 1 := by simp [unit, Complex.exp_two_pi_mul_I]
    rw [hunit, mul_one]
  exact periodic_mod (fun k : ℕ => unit (a.angle k)) (fun k => hp k) j

theorem polar_extended {n : ℕ} {z : Points n} (d : ExteriorData z)
    (σ : Equiv.Perm (Fin n)) (a : Angles n) (hn : 0 < n)
    (hp : ∀ i : Fin n, z (σ i) - center d = (radius d σ i : ℂ) * unit (a.angle i)) (j : ℕ) :
    z (σ (index hn j)) - center d = (radii d σ hn j : ℂ) * unit (a.angle j) := by
  rw [unit_angle_mod a hn j]
  exact hp _

theorem radius_budgets {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (σ : Equiv.Perm (Fin n)) (a : Angles n) (hn : 0 < n)
    (hc : 1 / 2 ≤ d.capacity) (he : errorRadius d ≤ 1 / 4)
    (hp : ∀ i : Fin n, z (σ i) - center d = (radius d σ i : ℂ) * unit (a.angle i)) :
    (∀ j, |radii d σ hn j - d.capacity| ≤ errorRadius d) ∧
    ∀ j, |radii d σ hn (j + 1) - radii d σ hn j| ≤
      12 * Real.sqrt (errorRadius d) * window a 1 j := by
  obtain ⟨ν, hν, hs⟩ := BoundarySupport.exists_node_unit_normals d HF (center d)
  have hzmem (i : Fin n) : z i ∈ hull z := subset_convexHull ℝ _ (mem_range_self i)
  have hpolar := polar_extended d σ a hn hp
  constructor
  · intro j
    have hr := point_radius_bounds d HF hc he (hzmem (σ (index hn j)))
      (hν (σ (index hn j))) (hs (σ (index hn j))) (norm_nonneg _) (hpolar j)
    apply abs_le.mpr
    change -errorRadius d ≤ ‖z (σ (index hn j)) - center d‖ - d.capacity ∧
      ‖z (σ (index hn j)) - center d‖ - d.capacity ≤ errorRadius d
    constructor <;> linarith [hr.1, hr.2.1]
  · intro j
    have hpnext : z (σ (index hn (j + 1))) - center d =
        (radii d σ hn (j + 1) : ℂ) * unit (a.angle j + window a 1 j) := by
      have ha : a.angle j + window a 1 j = a.angle ((j + 1 : ℕ) : ℤ) := by simp [window]
      rw [ha]
      exact hpolar (j + 1)
    have hr := radius_pair_bound d HF hc he (hzmem (σ (index hn j))) (hzmem (σ (index hn (j + 1))))
      (hν _) (hν _) (hs _) (hs _) (norm_nonneg _) (norm_nonneg _) (hpolar j) hpnext
    have hwpos : 0 < window a 1 j := window_pos a (by norm_num : 0 < (1 : ℕ)) j
    simpa only [abs_of_pos hwpos, radii, radius] using hr

theorem relative_edges {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (σ : Equiv.Perm (Fin n)) (a : Angles n) (hn : 2 ≤ n)
    (hc : 1 / 2 ≤ d.capacity) (he : errorRadius d ≤ 1 / 4)
    (hp : ∀ i : Fin n, z (σ i) - center d = (radius d σ i : ℂ) * unit (a.angle i)) (j : ℕ) :
    ‖RadialEdges.perturbation a (radii d σ (by omega)) d.capacity (j + 1) -
      RadialEdges.perturbation a (radii d σ (by omega)) d.capacity j‖ ≤
      RadialEdges.edgeError a (errorRadius d) * ‖LocalPhase.regularRoot n - 1‖ := by
  obtain ⟨hclose, hdiff⟩ := radius_budgets d HF σ a (by omega) hc he hp
  exact RadialEdges.relative_edge_bound a hn _ hc (errorRadius_nonneg d) hclose hdiff j

theorem actual_coordinates {n : ℕ} {z : Points n} (d : ExteriorData z)
    (σ : Equiv.Perm (Fin n)) (a : Angles n) (hn : 0 < n)
    (hp : ∀ i : Fin n, z (σ i) - center d = (radius d σ i : ℂ) * unit (a.angle i)) (j : ℕ) :
    z (σ (index hn j)) = center d + ((d.capacity : ℂ) * unit (a.angle 0)) *
      (LocalPhase.regularRoot n ^ j + RadialEdges.perturbation a (radii d σ hn) d.capacity j) := by
  have hc : (d.capacity : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr d.capacity_pos.ne'
  have hu : unit (a.angle 0) * GapRigidity.circlePoints a j = unit (a.angle j) := by
    change unit (a.angle 0) * unit (a.angle j - a.angle 0) = unit (a.angle j)
    rw [← unit_add]
    congr 1
    ring
  rw [RadialEdges.perturbation_eq]
  have he : ((d.capacity : ℂ) * unit (a.angle 0)) *
      ((radii d σ hn j / d.capacity : ℝ) : ℂ) * GapRigidity.circlePoints a j =
      (radii d σ hn j : ℂ) * unit (a.angle j) := by
    rw [← hu]
    push_cast
    field_simp
  rw [← mul_assoc, he]
  have hpj := polar_extended d σ a hn hp j
  linear_combination hpj

end
end Erdos1045.EventualExact.CanonicalPolarEdges
