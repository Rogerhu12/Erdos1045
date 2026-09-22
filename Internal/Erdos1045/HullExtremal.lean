import Erdos1045.HullGeometry

open scoped BigOperators

namespace Erdos1045.HullGeometry

open Configuration
noncomputable section

theorem injective_of_discriminant_pos {n : ℕ} {z : Points n}
    (hz : 0 < discriminant z) : Function.Injective z := by
  intro i j hij
  by_contra hne
  have hzero : discriminant z = 0 := by
    unfold discriminant
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply Finset.prod_eq_zero (by simp [Ne.symm hne] : j ∈ Finset.univ.erase i)
    simp [hij]
  linarith

/-- A scaled regular polygon supplies a strictly positive feasible competitor. -/
theorem perimeterExtremal_discriminant_pos (H : ClassicalHullGeometry) {n : ℕ}
    (hn : 3 ≤ n) {z : Points n} (hz : PerimeterExtremal n z) :
    0 < discriminant z := by
  let r : ℝ := 2 * Real.pi / circlePerimeter n
  have hr : 0 < r := div_pos (by positivity) (circlePerimeter_pos hn)
  let w : Points n := fun i => (r : ℂ) * regular n i
  have hP : hullPerimeter w = 2 * Real.pi := by
    have h := H.affine n (regular n) 0 (r : ℂ)
    simp only [zero_add, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      H.regular_perimeter n hn] at h
    change hullPerimeter w = _ at h
    rw [h]
    dsimp [r]
    field_simp [(circlePerimeter_pos hn).ne']
  have hD : 0 < discriminant w := by
    have h := discriminant_affine (regular n) 0 (r : ℂ)
    simp only [zero_add, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      H.regular_discriminant n hn] at h
    change discriminant w = _ at h
    rw [h]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  exact hD.trans_le (hz.2 w hP.le)

theorem perimeterExtremal_injective (H : ClassicalHullGeometry) {n : ℕ}
    (hn : 3 ≤ n) {z : Points n} (hz : PerimeterExtremal n z) : Function.Injective z :=
  injective_of_discriminant_pos (perimeterExtremal_discriminant_pos H hn hz)

theorem perimeterExtremal_perimeter_pos (H : ClassicalHullGeometry) {n : ℕ}
    (hn : 3 ≤ n) {z : Points n} (hz : PerimeterExtremal n z) : 0 < hullPerimeter z := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i, j] at this
  have hpos : 0 < ‖z i - z j‖ := norm_pos_iff.mpr
    (sub_ne_zero.mpr (fun h => hij (perimeterExtremal_injective H hn hz h)))
  have hbound := H.distance_le_half n z i j
  linarith

/-- Homogeneity forces every extremizer to use its full perimeter budget. -/
theorem perimeterExtremal_perimeter_eq (H : ClassicalHullGeometry) {n : ℕ}
    (hn : 3 ≤ n) {z : Points n} (hz : PerimeterExtremal n z) :
    hullPerimeter z = 2 * Real.pi := by
  apply le_antisymm hz.1
  by_contra hnot
  have hlt : hullPerimeter z < 2 * Real.pi := lt_of_not_ge hnot
  have hP := perimeterExtremal_perimeter_pos H hn hz
  have hD := perimeterExtremal_discriminant_pos H hn hz
  let r : ℝ := 2 * Real.pi / hullPerimeter z
  have hr1 : 1 < r := (one_lt_div hP).mpr hlt
  have hr : 0 < r := lt_trans zero_lt_one hr1
  let w : Points n := fun i => (r : ℂ) * z i
  have hwP : hullPerimeter w = 2 * Real.pi := by
    have h := H.affine n z 0 (r : ℂ)
    simp only [zero_add, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at h
    change hullPerimeter w = _ at h
    rw [h]
    dsimp [r]
    field_simp [hP.ne']
  have hwD : discriminant w = r ^ exponent n * discriminant z := by
    simpa [w, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using
      discriminant_affine z 0 (r : ℂ)
  have he : exponent n ≠ 0 := by exact Nat.mul_ne_zero (by omega) (by omega)
  have hpow : 1 < r ^ exponent n := one_lt_pow₀ hr1 he
  have hmax := hz.2 w hwP.le
  rw [hwD] at hmax
  nlinarith

/-- Every configuration in the same hull is an admissible competitor. -/
theorem perimeterExtremal_dominates_hull (H : ClassicalHullGeometry) {n : ℕ}
    {z : Points n} (hz : PerimeterExtremal n z) (w : Points n)
    (hw : Set.range w ⊆ convexHull ℝ (Set.range z)) :
    discriminant w ≤ discriminant z :=
  hz.2 w ((H.monotone n n w z hw).trans hz.1)

/-- The single-node replacement inequality required by the Fekete argument. -/
theorem perimeterExtremal_fekete (H : ClassicalHullGeometry) {n : ℕ}
    {z : Points n} (hz : PerimeterExtremal n z) (i : Fin n) (x : ℂ)
    (hx : x ∈ convexHull ℝ (Set.range z)) :
    discriminant (Function.update z i x) ≤ discriminant z := by
  apply perimeterExtremal_dominates_hull H hz
  rintro y ⟨j, rfl⟩
  by_cases hji : j = i
  · simpa [hji] using hx
  · simpa [Function.update_of_ne hji] using
      (subset_convexHull ℝ (Set.range z) (Set.mem_range_self j))

end
end Erdos1045.HullGeometry

