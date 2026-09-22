import EventualExact.BoundarySupportNormal
import EventualExact.PhysicalPairBounds
import EventualExact.CyclicDistance
import Mathlib.Algebra.Field.Periodic

/-! Actual physical polar geometry, with all support-normal inputs discharged.
Physical separation gives separation of every consecutive integer lift gap. -/

namespace Erdos1045.EventualExact.PhysicalAngularGeometry

open Complex Set ExteriorClassical ExteriorBoundary Configuration CyclicAngles ExteriorSupport
open AngularHarmonicBound
open scoped ComplexConjugate
noncomputable section

def radius {n : ℕ} {z : Points n} (d : ExteriorData z) (σ : Equiv.Perm (Fin n))
    (i : Fin n) : ℝ := ‖z (σ i) - center d‖

def height {n : ℕ} {z : Points n} (d : ExteriorData z) (σ : Equiv.Perm (Fin n))
    (i : Fin n) : ℝ := Real.log (radius d σ i)

theorem sorted_height_bound {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (hc : 1 / 2 ≤ d.capacity) (he : errorRadius d ≤ 1 / 4)
    (σ : Equiv.Perm (Fin n)) (a : Angles n)
    (hp : ∀ i : Fin n, z (σ i) - center d = (radius d σ i : ℂ) * unit (a.angle i))
    (i j : Fin n) :
    |height d σ i - height d σ j| ≤ 48 * Real.sqrt (errorRadius d) * |shortAngle a i j| := by
  obtain ⟨ν, hν, hs⟩ := BoundarySupport.exists_node_unit_normals d HF (center d)
  have hzmem (k : Fin n) : z k ∈ hull z := subset_convexHull ℝ _ (mem_range_self k)
  have hi : z (σ i) - center d =
      (radius d σ i : ℂ) * unit (a.angle j + shortAngle a i j) := by
    rw [unit_add_shortAngle]
    exact hp i
  exact log_radius_pair_bound d HF hc he (hzmem (σ j)) (hzmem (σ i))
    (hν (σ j)) (hν (σ i)) (hs (σ j)) (hs (σ i))
    (norm_nonneg _) (norm_nonneg _) (hp j) hi

theorem sorted_point_bound {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (hc : 1 / 2 ≤ d.capacity) (he : errorRadius d ≤ 1 / 4)
    (σ : Equiv.Perm (Fin n)) (a : Angles n)
    (hp : ∀ i : Fin n, z (σ i) - center d = (radius d σ i : ℂ) * unit (a.angle i))
    (i j : Fin n) : ‖z (σ i) - z (σ j)‖ ≤ 8 * |shortAngle a i j| := by
  obtain ⟨ν, hν, hs⟩ := BoundarySupport.exists_node_unit_normals d HF (center d)
  have hzmem (k : Fin n) : z k ∈ hull z := subset_convexHull ℝ _ (mem_range_self k)
  have hi : z (σ i) - center d =
      (radius d σ i : ℂ) * unit (a.angle j + shortAngle a i j) := by
    rw [unit_add_shortAngle]
    exact hp i
  exact point_pair_bound d HF hc he (hzmem (σ j)) (hzmem (σ i))
    (hν (σ j)) (hν (σ i)) (hs (σ j)) (hs (σ i))
    (norm_nonneg _) (norm_nonneg _) (hp j) hi

theorem shortAngle_next_le_gap {n : ℕ} (a : Angles n) (hn : 2 ≤ n) (i : Fin n) :
    |shortAngle a (cyclicAdvance i 1) i| ≤ a.angle ((i : ℤ) + 1) - a.angle i := by
  have hpos : 0 < a.angle ((i : ℤ) + 1) - a.angle i :=
    sub_pos.mpr (a.increasing (by omega))
  have hupper : a.angle ((i : ℤ) + 1) - a.angle i < 2 * Real.pi := by
    have hh := a.increasing (show (i : ℤ) + 1 < (i : ℤ) + n by omega)
    rw [a.period] at hh
    linarith
  have hprincipal : |shortAngle a (cyclicAdvance i 1) i| =
      principalDistance (a.angle ((i : ℤ) + 1) - a.angle i) := by
    change principalDistance (a.angle (cyclicAdvance i 1) - a.angle i) = _
    by_cases h : i.val + 1 < n
    · have hi : ((cyclicAdvance i 1 : Fin n) : ℤ) = (i : ℤ) + 1 := by
        change (((i.val + 1) % n : ℕ) : ℤ) = (i : ℤ) + 1
        rw [Nat.mod_eq_of_lt h]
        push_cast
        rfl
      rw [hi]
    · have hi : (i : ℤ) + 1 = n := by omega
      have hj : cyclicAdvance i 1 = ⟨0, by omega⟩ := by
        apply Fin.ext
        change (i.val + 1) % n = 0
        rw [show i.val + 1 = n by omega, Nat.mod_self]
      rw [hj, hi]
      have ha : a.angle (n : ℤ) = a.angle 0 + 2 * Real.pi := by simpa using a.period 0
      rw [ha]
      simpa only [Nat.cast_zero, show a.angle 0 + 2 * Real.pi - a.angle i =
        (a.angle 0 - a.angle i) + 2 * Real.pi by ring] using
        (principalDistance_add_two_pi (a.angle 0 - a.angle i)).symm
  rw [hprincipal, principalDistance_eq_min hpos.le hupper.le]
  exact min_le_left _ _

theorem integer_gap_bound_of_finite {n : ℕ} (a : Angles n) (hn : 0 < n) {δ : ℝ}
    (hgap : ∀ i : Fin n, δ ≤ a.angle ((i : ℤ) + 1) - a.angle i) :
    ∀ k : ℤ, δ ≤ a.angle (k + 1) - a.angle k := by
  have hper : Function.Periodic (fun k : ℤ => a.angle (k + 1) - a.angle k) (n : ℤ) := by
    intro k
    dsimp only
    rw [show k + n + 1 = (k + 1) + n by ring, a.period, a.period]
    ring
  intro k
  obtain ⟨l, hl, heq⟩ := hper.exists_mem_Ico₀ (by exact_mod_cast hn) k
  let i : Fin n := ⟨l.toNat, by have := hl.1; have := hl.2; omega⟩
  have hi : (i : ℤ) = l := Int.toNat_of_nonneg hl.1
  rw [heq]
  simpa only [hi] using hgap i

theorem sorted_gap_separation {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (hn : 2 ≤ n) (hc : 1 / 2 ≤ d.capacity) (he : errorRadius d ≤ 1 / 4)
    (σ : Equiv.Perm (Fin n)) (a : Angles n)
    (hp : ∀ i : Fin n, z (σ i) - center d = (radius d σ i : ℂ) * unit (a.angle i))
    {γ : ℝ} (hsep : ∀ i j : Fin n, i ≠ j → γ / n ≤ ‖z i - z j‖) :
    ∀ k : ℤ, γ / (8 * n) ≤ a.angle (k + 1) - a.angle k := by
  apply integer_gap_bound_of_finite a (by omega)
  intro i
  have hne := cyclicAdvance_ne_self i (by norm_num : 0 < (1 : ℕ)) (by omega)
  have hdist := hsep (σ (cyclicAdvance i 1)) (σ i) (fun h => hne (σ.injective h))
  have hpbound := sorted_point_bound d HF hc he σ a hp (cyclicAdvance i 1) i
  have hs := mul_le_mul_of_nonneg_left (shortAngle_next_le_gap a hn i) (by norm_num : (0 : ℝ) ≤ 8)
  have hbound : γ / n ≤ 8 * (a.angle ((i : ℤ) + 1) - a.angle i) := hdist.trans (hpbound.trans hs)
  have hdiv : γ / (8 * n) = (γ / n) / 8 := by ring
  rw [hdiv]
  linarith

/-- All geometry required by the polar force budget, before stationarity and asymptotic estimates. -/
theorem physical_angular_geometry {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (hn : 2 ≤ n) (hinj : Function.Injective z)
    (hc : 1 / 2 ≤ d.capacity) (he : errorRadius d ≤ 1 / 4) {γ : ℝ}
    (hsep : ∀ i j : Fin n, i ≠ j → γ / n ≤ ‖z i - z j‖) :
    ∃ (σ : Equiv.Perm (Fin n)) (a : Angles n),
      (∀ i : Fin n, 0 ≤ a.angle i ∧ a.angle i < 2 * Real.pi) ∧
      (∀ i : Fin n, z (σ i) - center d = (radius d σ i : ℂ) * unit (a.angle i)) ∧
      (∀ i j : Fin n, |height d σ i - height d σ j| ≤
        48 * Real.sqrt (errorRadius d) * |shortAngle a i j|) ∧
      ∀ k : ℤ, γ / (8 * n) ≤ a.angle (k + 1) - a.angle k := by
  obtain ⟨ν, hν, hs⟩ := BoundarySupport.exists_node_unit_normals d HF (center d)
  obtain ⟨σ, a, har, hp⟩ := physical_angles_exist d HF (by omega) hinj hc he ν hν hs
  exact ⟨σ, a, har, hp, sorted_height_bound d HF hc he σ a hp,
    sorted_gap_separation d HF hn hc he σ a hp hsep⟩

end
end Erdos1045.EventualExact.PhysicalAngularGeometry
