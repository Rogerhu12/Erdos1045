import FinitePerimeterEndpoints
import FinitePerimeterSort

/-! The sharp Reinhardt inequality, derived from actual finite normal cones.
No polygon, smoothness, general-position, or perimeter assumptions occur. -/

namespace ExteriorReduction.Reinhardt
open Complex Set MeasureTheory
open Erdos1045.Configuration Erdos1045.HullGeometry
open scoped BigOperators
noncomputable section

theorem width_semicircle_integral {n : ℕ} (z : Points n) :
    (∫ t in (-Real.pi)..(0 : ℝ), width z t) = hullPerimeter z := by
  have hc : Continuous (fun t : ℝ => support z (t + Real.pi)) :=
    (support_continuous z).comp (continuous_id.add_const _)
  unfold width
  rw [intervalIntegral.integral_add ((support_continuous z).intervalIntegrable _ _)
    (hc.intervalIntegrable _ _), intervalIntegral.integral_comp_add_right]
  simp only [neg_add_cancel, zero_add]
  rw [intervalIntegral.integral_add_adjacent_intervals
    ((support_continuous z).intervalIntegrable _ _)
    ((support_continuous z).intervalIntegrable _ _)]
  have hh := (support_periodic z).intervalIntegral_add_eq (-Real.pi) 0
  have he : -Real.pi + 2 * Real.pi = Real.pi := by ring
  simpa only [he, zero_add, hullPerimeter] using hh

/-- Jensen's chord estimate on a half circle, with zero-length padding. -/
theorem semicircle_chord_sum_le {n : ℕ} (hn : 0 < n) (δ : Fin n → ℝ)
    (hδ : ∀ i, 0 ≤ δ i) (hsum : ∑ i, δ i = Real.pi) :
    (∑ i, 2 * Real.sin (δ i / 2)) ≤ diameterPerimeterBound n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmem : ∀ i ∈ (Finset.univ : Finset (Fin n)), δ i / 2 ∈ Icc (0 : ℝ) Real.pi := by
    intro i hi
    have hh : δ i ≤ Real.pi := by
      rw [← hsum]
      exact Finset.single_le_sum (fun j _ => hδ j) hi
    constructor <;> linarith [hδ i, Real.pi_pos]
  have hw : ∑ _i : Fin n, (1 / (n : ℝ)) = 1 := by simp [hn.ne']
  have hj := strictConcaveOn_sin_Icc.concaveOn.le_map_sum
    (t := (Finset.univ : Finset (Fin n))) (w := fun _ => 1 / (n : ℝ))
    (p := fun i => δ i / 2) (fun _ _ => by positivity) hw hmem
  simp only [smul_eq_mul, one_div, ← div_eq_inv_mul] at hj
  rw [← Finset.sum_div, ← Finset.sum_div, ← Finset.sum_div, hsum] at hj
  have hh := (div_le_iff₀ hnR).mp hj
  have he : Real.pi / 2 / (n : ℝ) = Real.pi / (2 * n) := by ring
  rw [he] at hh
  rw [← Finset.mul_sum]
  unfold diameterPerimeterBound
  nlinarith

theorem reinhardt_with_normal_cut {n : ℕ} (hn : 0 < n) (z : Points n)
    (hne : ∃ i j, z i ≠ z j) (hcut : ∀ i, (-1 : ℂ) ∉ strictNormalCone z i)
    (hdiam : DiameterAtMost 1 z) : hullPerimeter z ≤ diameterPerimeterBound n := by
  obtain ⟨p, hp0, hpn, hpmono, hpbound, hpgap⟩ := finite_endpoint_partition
    (n := n) (by linarith [Real.pi_pos] : -Real.pi < 0) (widthEndpoints z)
    (widthEndpoints_mem z hne hcut) (zero_mem_widthEndpoints hn z hne hcut)
    (widthEndpoints_card_le z)
  have hcell (k : ℕ) :
      (∫ t in p k..p (k + 1), width z t) ≤ 2 * Real.sin ((p (k + 1) - p k) / 2) := by
    have hle := hpmono (Nat.le_succ k)
    rcases hle.eq_or_lt with he | hlt
    · simp [← he]
    · obtain ⟨i, j, hij⟩ := width_fixed_between_endpoints hn z hne hcut hlt
        (hpbound k).1 (hpbound (k + 1)).2 (hpgap k)
      rw [intervalIntegral.integral_congr (by simpa only [uIcc_of_le hle] using hij)]
      exact projection_integral_le_chord (hdiam i j) hle
        (by linarith [(hpbound k).1, (hpbound (k + 1)).2, Real.pi_pos])
  have hadd := intervalIntegral.sum_integral_adjacent_intervals
    (n := n) (a := p) (μ := volume) (f := width z) (fun k _ => (width_continuous z).intervalIntegrable (p k) (p (k + 1)))
  rw [hp0, hpn, width_semicircle_integral] at hadd
  have hs : (∑ i : Fin n, (p (i.val + 1) - p i.val)) = Real.pi := by
    rw [Fin.sum_univ_eq_sum_range (fun k => p (k + 1) - p k), Finset.sum_range_sub, hp0, hpn]
    ring
  have hchord := semicircle_chord_sum_le hn (fun i : Fin n => p (i.val + 1) - p i.val)
    (fun i => sub_nonneg.mpr (hpmono (Nat.le_succ i.val))) hs
  rw [Fin.sum_univ_eq_sum_range (fun k => 2 * Real.sin ((p (k + 1) - p k) / 2))] at hchord
  rw [← hadd]
  exact (Finset.sum_le_sum (fun k _ => hcell k)).trans hchord

/-- The canonical sharp finite-set perimeter inequality. -/
theorem reinhardtPerimeterInequality_proved : ReinhardtPerimeterInequality := by
  intro n hn z hz
  have hn0 : 0 < n := by omega
  by_cases hne : ∃ i j, z i ≠ z j
  · obtain ⟨a, ha, hcut⟩ := exists_rotation_normal_cut z hne
    have ha0 : a ≠ 0 := by
      intro hh
      simp only [hh, norm_zero] at ha
      norm_num at ha
    have hne' : ∃ i j, a * z i ≠ a * z j := by
      obtain ⟨i, j, hij⟩ := hne
      exact ⟨i, j, fun he => hij (mul_left_cancel₀ ha0 he)⟩
    have hz' : DiameterAtMost 1 (fun i => a * z i) := by
      intro i j
      simpa only [← mul_sub, norm_mul, ha, one_mul] using hz i j
    have hh := reinhardt_with_normal_cut hn0 (fun i => a * z i) hne' hcut hz'
    have hp := hullPerimeter_affine_proved n z 0 a
    simp only [zero_add, ha, one_mul] at hp
    rwa [hp] at hh
  · have he (i j : Fin n) : z i = z j := not_ne_iff.mp (fun hh => hne ⟨i, j, hh⟩)
    let i : Fin n := ⟨0, hn0⟩
    have hp : hullPerimeter z = 0 := by
      have hh := hullPerimeter_affine_proved n z (z i) 0
      have hzconst : (fun j : Fin n => z i + (0 : ℂ) * z j) = z := by
        funext j
        simpa only [zero_mul, add_zero] using he i j
      rw [hzconst, norm_zero, zero_mul] at hh
      exact hh
    rw [hp]
    unfold diameterPerimeterBound
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hsin : 0 ≤ Real.sin (Real.pi / (2 * (n : ℝ))) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
        ((div_le_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr (by nlinarith [Real.pi_pos]))
    positivity

/-- Every field of the former hull-geometry interface is now unconditional. -/
theorem classicalHullGeometry_proved : ClassicalHullGeometry :=
  classicalHullGeometry_of_reinhardt reinhardtPerimeterInequality_proved

#print axioms reinhardtPerimeterInequality_proved
#print axioms classicalHullGeometry_proved
end
end ExteriorReduction.Reinhardt


