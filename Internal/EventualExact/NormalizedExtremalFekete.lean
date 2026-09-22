import EventualExact.CoarseFeketeFamilyProved
import Mathlib.Analysis.Normed.Module.Convex

/-! Both genuine extremal problems give the same normalized Fekete inputs,
in every dimension at least four. No regularity conclusion or parity is used. -/

namespace Erdos1045.EventualExact.ExtremalNormalization

open Filter
open scoped Topology
open Configuration HullGeometry ExteriorClassical
noncomputable section

def DiameterExtremal {n : ℕ} (z : Points n) : Prop :=
  DiameterAtMost 2 z ∧ ∀ w : Points n, DiameterAtMost 2 w → discriminant w ≤ discriminant z

structure NormalizedFekete {n : ℕ} (z : Points n) : Prop where
  perimeter_eq : hullPerimeter z = 2 * Real.pi
  injective : Function.Injective z
  discriminant_ge : (n : ℝ) ^ n ≤ discriminant z
  fekete : Fekete z

def scale {n : ℕ} (r : ℝ) (z : Points n) : Points n := fun i => (r : ℂ) * z i

def normalize {n : ℕ} (z : Points n) : Points n := scale (2 * Real.pi / hullPerimeter z) z

theorem provedGeometry : ClassicalHullGeometry :=
  classicalBackground_proved.toClassicalAnalysis.geometry

theorem hull_scale {n : ℕ} (r : ℝ) (z : Points n) :
    hull (scale r z) = (fun x : ℂ => (r : ℂ) * x) '' hull z := by
  have h := (LinearMap.lsmul ℝ ℂ r).image_convexHull (Set.range z)
  change (fun x : ℂ => (r : ℂ) * x) '' convexHull ℝ (Set.range z) =
    convexHull ℝ ((fun x : ℂ => (r : ℂ) * x) '' Set.range z) at h
  rw [← Set.range_comp'] at h
  exact h.symm

theorem discriminant_scale {n : ℕ} (r : ℝ) (z : Points n) :
    discriminant (scale r z) = |r| ^ exponent n * discriminant z := by
  change discriminant (fun i => (r : ℂ) * z i) = _
  simpa only [zero_add, Complex.norm_real, Real.norm_eq_abs] using
    discriminant_affine z 0 (r : ℂ)

theorem fekete_scale {n : ℕ} {z : Points n} (hz : Fekete z) {r : ℝ} (hr : r ≠ 0) :
    Fekete (scale r z) := by
  intro w hw
  let v := scale r⁻¹ w
  have hv : Set.range v ⊆ hull z := by
    rintro _ ⟨i, rfl⟩
    have hi := hw (Set.mem_range_self i)
    rw [hull_scale] at hi
    obtain ⟨x, hx, he⟩ := hi
    change (r⁻¹ : ℝ) * w i ∈ hull z
    rw [← he]
    simpa only [Complex.ofReal_inv, ← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hr),
      one_mul] using hx
  have hvw : scale r v = w := by
    funext i
    change (r : ℂ) * ((r⁻¹ : ℝ) * w i) = w i
    rw [Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hr), one_mul]
  calc
    discriminant w = discriminant (scale r v) := congrArg discriminant hvw.symm
    _ = |r| ^ exponent n * discriminant v := discriminant_scale r v
    _ ≤ |r| ^ exponent n * discriminant z :=
      mul_le_mul_of_nonneg_left (hz v hv) (pow_nonneg (abs_nonneg _) _)
    _ = _ := (discriminant_scale r z).symm

theorem diameter_of_range_subset_hull {n m : ℕ} {z : Points n} {w : Points m} {d : ℝ}
    (hz : DiameterAtMost d z) (hw : Set.range w ⊆ hull z) : DiameterAtMost d w := by
  have hball (i : Fin n) : hull z ⊆ Metric.closedBall (z i) d := by
    apply convexHull_min _ (convex_closedBall (z i) d)
    rintro _ ⟨j, rfl⟩
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz j i
  intro i j
  have hall : hull z ⊆ Metric.closedBall (w j) d := by
    apply convexHull_min _ (convex_closedBall (w j) d)
    rintro _ ⟨k, rfl⟩
    have hk := hball k (hw (Set.mem_range_self j))
    simpa only [Metric.mem_closedBall, dist_comm] using hk
  simpa only [Metric.mem_closedBall, dist_eq_norm] using hall (hw (Set.mem_range_self i))

theorem DiameterExtremal.fekete {n : ℕ} {z : Points n} (hz : DiameterExtremal z) : Fekete z :=
  fun w hw => hz.2 w (diameter_of_range_subset_hull hz.1 hw)

theorem regular_diameter_two (n : ℕ) : DiameterAtMost 2 (regular n) := by
  intro i j
  calc
    ‖regular n i - regular n j‖ ≤ ‖regular n i‖ + ‖regular n j‖ := norm_sub_le _ _
    _ = 2 := by simp [regular, Complex.norm_exp]; norm_num

theorem DiameterExtremal.discriminant_ge {n : ℕ} (hn : 3 ≤ n) {z : Points n}
    (hz : DiameterExtremal z) : (n : ℝ) ^ n ≤ discriminant z := by
  rw [← provedGeometry.regular_discriminant n hn]
  exact hz.2 (regular n) (regular_diameter_two n)

theorem diameter_perimeter_le_two_pi {n : ℕ} (hn : 3 ≤ n) {z : Points n}
    (hz : DiameterAtMost 2 z) : hullPerimeter z ≤ 2 * Real.pi := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hd : DiameterAtMost 1 (scale (1 / 2) z) := by
    change DiameterAtMost 1 (fun i => ((1 / 2 : ℝ) : ℂ) * z i)
    simpa using diameter_affine hz 0 ((1 / 2 : ℝ) : ℂ)
  have hb := provedGeometry.reinhardt n hn (scale (1 / 2) z) hd
  have hP : hullPerimeter (scale (1 / 2) z) = (1 / 2 : ℝ) * hullPerimeter z := by
    change hullPerimeter (fun i => ((1 / 2 : ℝ) : ℂ) * z i) = _
    simpa using provedGeometry.affine n z 0 ((1 / 2 : ℝ) : ℂ)
  have hs := Real.sin_le (show 0 ≤ Real.pi / (2 * n) by positivity)
  have ht := mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ 2 * n by positivity)
  have he : (2 * (n : ℝ)) * (Real.pi / (2 * n)) = Real.pi := by field_simp
  rw [he] at ht
  rw [hP] at hb
  unfold diameterPerimeterBound at hb
  linarith

theorem perimeter_pos_of_discriminant_pos {n : ℕ} (hn : 2 ≤ n) {z : Points n}
    (hD : 0 < discriminant z) : 0 < hullPerimeter z := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i, j] at this
  have hdist : 0 < ‖z i - z j‖ := norm_pos_iff.mpr
    (sub_ne_zero.mpr (fun h => hij (injective_of_discriminant_pos hD h)))
  have hbound := provedGeometry.distance_le_half n z i j
  linarith

theorem normalize_fekete {n : ℕ} (hn : 3 ≤ n) {z : Points n} (hF : Fekete z)
    (hD : (n : ℝ) ^ n ≤ discriminant z) (hP : hullPerimeter z ≤ 2 * Real.pi) :
    NormalizedFekete (normalize z) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hDpos : 0 < discriminant z := (pow_pos hn0 n).trans_le hD
  have hPpos := perimeter_pos_of_discriminant_pos (by omega : 2 ≤ n) hDpos
  let r := 2 * Real.pi / hullPerimeter z
  have hr : 0 < r := div_pos (by positivity) hPpos
  have hr1 : 1 ≤ r := (one_le_div hPpos).2 hP
  have hscaleD : discriminant (normalize z) = r ^ exponent n * discriminant z := by
    simpa only [normalize, r, abs_of_pos hr] using discriminant_scale r z
  have hnewD : (n : ℝ) ^ n ≤ discriminant (normalize z) := by
    rw [hscaleD]
    exact hD.trans (le_mul_of_one_le_left hDpos.le (one_le_pow₀ hr1))
  refine ⟨?_, injective_of_discriminant_pos ((pow_pos hn0 n).trans_le hnewD),
    hnewD, fekete_scale hF hr.ne'⟩
  have he := provedGeometry.affine n z 0 (r : ℂ)
  simp only [zero_add, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at he
  change hullPerimeter (scale r z) = _
  rw [show hullPerimeter (scale r z) = r * hullPerimeter z from he]
  dsimp [r]
  field_simp

theorem diameterExtremal_normalized {n : ℕ} (hn : 4 ≤ n) {z : Points n}
    (hz : DiameterExtremal z) : NormalizedFekete (normalize z) :=
  normalize_fekete (by omega) hz.fekete (hz.discriminant_ge (by omega))
    (diameter_perimeter_le_two_pi (by omega) hz.1)

theorem perimeterExtremal_normalized {n : ℕ} (hn : 4 ≤ n) {z : Points n}
    (hz : PerimeterExtremal n z) : NormalizedFekete z where
  perimeter_eq := perimeterExtremal_perimeter_eq provedGeometry (by omega) hz
  injective := perimeterExtremal_injective provedGeometry (by omega) hz
  discriminant_ge := perimeterExtremal_discriminant_ge provedGeometry (by omega) hz
  fekete := fun w hw => perimeterExtremal_dominates_hull provedGeometry hz w hw

theorem extremal_normalized {n : ℕ} (hn : 4 ≤ n) {z : Points n}
    (hz : DiameterExtremal z ∨ PerimeterExtremal n z) : NormalizedFekete (normalize z) := by
  rcases hz with hd | hp
  · exact diameterExtremal_normalized hn hd
  · have h := perimeterExtremal_normalized hn hp
    exact normalize_fekete (by omega) h.fekete h.discriminant_ge h.perimeter_eq.le

/-- Genuine extremal sequences feed directly into the proved all-order
inverse-square energy bound after perimeter normalization and boundary sorting. -/
theorem extremal_sequence_inverse_square_energy {N : ℕ → ℕ}
    (hN4 : ∀ j, 4 ≤ N j) (hN : Tendsto N atTop atTop) (z : ∀ j, Points (N j))
    (hz : ∀ j, DiameterExtremal (z j) ∨ PerimeterExtremal (N j) (z j)) :
    ∃ σ : ∀ j, Equiv.Perm (Fin (N j)), ∃ d : ∀ j, ExteriorData (normalize (z j) ∘ σ j),
      (∀ j, FaberIdentities (d j)) ∧ ∃ K : ℝ, 0 ≤ K ∧
        ∀ᶠ j in atTop, (N j : ℝ) ^ 2 * (d j).energySquared ≤ K := by
  have h (j : ℕ) := extremal_normalized (hN4 j) (hz j)
  exact CoarseFekete.normalized_fekete_inverse_square_energy hN4 hN (fun j => normalize (z j))
    (fun j => (h j).injective) (fun j => (h j).perimeter_eq)
    (fun j => (h j).fekete) (fun j => (h j).discriminant_ge)

end
end Erdos1045.EventualExact.ExtremalNormalization
