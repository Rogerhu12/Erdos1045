import EventualExact.LensClosureLinear
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Contracting

/-! A quantitative root of the actual nonlinear lens closure, by its proved derivative bound. -/

namespace Erdos1045.EventualExact.LensClosure

open Complex Set Metric
open scoped BigOperators NNReal
noncomputable section

def inverseScale (m : ℕ) : ℂ := ((2 / m : ℝ) : ℂ) * (-I)

def correction {m : ℕ} (α L s t : Fin m → ℝ) (ξ : ℂ) : ℂ :=
  ξ - inverseScale m * closure α L s t ξ

def correctionDerivative {m : ℕ} (α s t : Fin m → ℝ) (ξ : ℂ) : ℂ →L[ℝ] ℂ :=
  ContinuousLinearMap.id ℝ ℂ - inverseScale m • closureDerivative α s t ξ

theorem norm_inverseScale {m : ℕ} : ‖inverseScale m‖ = (2 / m : ℝ) := by
  simp [inverseScale]

theorem inverseScale_ne_zero {m : ℕ} (hm : 0 < m) : inverseScale m ≠ 0 := by
  unfold inverseScale
  apply mul_ne_zero
  · apply ofReal_ne_zero.mpr
    exact div_ne_zero (by norm_num) (by exact_mod_cast hm.ne')
  · exact neg_ne_zero.mpr I_ne_zero

theorem inverseScale_model {m : ℕ} (hm : 2 ≤ m) (v : ℂ) :
    inverseScale m * modelDerivative m v = v := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  rw [modelDerivative_apply hm]
  simp only [inverseScale, ofReal_div, ofReal_ofNat, ofReal_natCast]
  field_simp
  simp [I_sq]

theorem correction_hasFDerivAt {m : ℕ} (α L s t : Fin m → ℝ) (ξ : ℂ)
    (ht : ∀ j, heightParameter t ξ j ^ 2 < 4) :
    HasFDerivAt (correction α L s t) (correctionDerivative α s t ξ) ξ := by
  have hd := (closure_hasFDerivAt α L s t ξ ht).const_smul (inverseScale m)
  convert (hasFDerivAt_id (𝕜 := ℝ) ξ).fun_sub hd using 1 <;> rfl

theorem correctionDerivative_norm_le {m : ℕ} (hm : 2 ≤ m)
    (α s t : Fin m → ℝ) (ξ : ℂ)
    (herror : ∀ j, ‖tangent (α j) (s j) (heightParameter t ξ j) -
      unit (midpoint m j) * I‖ ≤ 1 / 4) :
    ‖correctionDerivative α s t ξ‖ ≤ (1 / 2 : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  have he : correctionDerivative α s t ξ v =
      -inverseScale m * (closureDerivative α s t ξ v - modelDerivative m v) := by
    simp only [correctionDerivative, sub_apply,
      ContinuousLinearMap.id_apply, smul_apply, smul_eq_mul]
    have hi := inverseScale_model hm v
    linear_combination -hi
  rw [he, norm_mul, norm_neg, norm_inverseScale]
  calc
    _ ≤ (2 / m : ℝ) * (m * (1 / 4) * ‖v‖) :=
      mul_le_mul_of_nonneg_left (closureDerivative_error α s t ξ v herror) (by positivity)
    _ = _ := by field_simp; ring

theorem ball_height_small {m : ℕ} (α t : Fin m → ℝ) {R : ℝ}
    (hsmall : ∀ j, |α j - midpoint m j| + |t j| + R ≤ 1 / 4)
    {ξ : ℂ} (hξ : ξ ∈ closedBall 0 R) (j : Fin m) :
    |α j - midpoint m j| + |heightParameter t ξ j| ≤ 1 / 4 := by
  have hn : ‖ξ‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hξ
  have ht : |heightParameter t ξ j| ≤ |t j| + R := by
    unfold heightParameter
    exact (abs_add_le _ _).trans
      (add_le_add le_rfl ((harmonicFunctional_le_norm _ _).trans hn))
  linarith [hsmall j]

theorem correction_lipschitz_on_ball {m : ℕ} (hm : 2 ≤ m)
    (α L s t : Fin m → ℝ) {R : ℝ}
    (hs : ∀ j, |s j| ≤ 1)
    (hsmall : ∀ j, |α j - midpoint m j| + |t j| + R ≤ 1 / 4) :
    LipschitzOnWith (1 / 2 : ℝ≥0) (correction α L s t) (closedBall 0 R) := by
  have hp (ξ : ℂ) (hξ : ξ ∈ closedBall 0 R) (j : Fin m) :=
    ball_height_small α t hsmall hξ j
  have ht (ξ : ℂ) (hξ : ξ ∈ closedBall 0 R) (j : Fin m) :
      |heightParameter t ξ j| ≤ 1 := by
    linarith [hp ξ hξ j, abs_nonneg (α j - midpoint m j)]
  apply (convex_closedBall (0 : ℂ) R).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (f' := correctionDerivative α s t)
  · intro ξ hξ
    apply (correction_hasFDerivAt α L s t ξ _).hasFDerivWithinAt
    intro j
    have h := ht ξ hξ j
    nlinarith [(abs_le.mp h).1, (abs_le.mp h).2]
  · intro ξ hξ
    change ‖correctionDerivative α s t ξ‖ ≤ (1 / 2 : ℝ)
    apply correctionDerivative_norm_le hm
    intro j
    exact (tangent_error (hs j) (ht ξ hξ j)).trans (hp ξ hξ j)

theorem correction_maps_ball {m : ℕ} (hm : 2 ≤ m)
    (α L s t : Fin m → ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ j, |s j| ≤ 1)
    (hsmall : ∀ j, |α j - midpoint m j| + |t j| + R ≤ 1 / 4)
    (hsource : ‖closure α L s t 0‖ ≤ (m : ℝ) * R / 4) :
    MapsTo (correction α L s t) (closedBall 0 R) (closedBall 0 R) := by
  have hLip := correction_lipschitz_on_ball hm α L s t hs hsmall
  have hzero : (0 : ℂ) ∈ closedBall 0 R := by simp [hR]
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnorm0 : ‖correction α L s t 0‖ ≤ R / 2 := by
    simp only [correction, zero_sub, norm_neg, norm_mul, norm_inverseScale]
    calc
      _ ≤ (2 / m : ℝ) * (m * R / 4) :=
        mul_le_mul_of_nonneg_left hsource (by positivity)
      _ = _ := by field_simp; ring
  intro ξ hξ
  have h := (lipschitzOnWith_iff_norm_sub_le.mp hLip) hξ hzero
  have hn : ‖ξ‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hξ
  norm_num at h
  have htri := norm_sub_le (correction α L s t ξ - correction α L s t 0)
    (-correction α L s t 0)
  simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at htri
  apply mem_closedBall_zero_iff.mpr
  linarith

theorem correction_fixed_iff {m : ℕ} (hm : 0 < m) (α L s t : Fin m → ℝ) (ξ : ℂ) :
    correction α L s t ξ = ξ ↔ closure α L s t ξ = 0 := by
  simp only [correction, sub_eq_self, mul_eq_zero, inverseScale_ne_zero hm, false_or]

/-- A directly checkable quantitative root theorem for the genuine square-root closure. -/
theorem exists_unique_closure_root {m : ℕ} (hm : 2 ≤ m)
    (α L s t : Fin m → ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ j, |s j| ≤ 1)
    (hsmall : ∀ j, |α j - midpoint m j| + |t j| + R ≤ 1 / 4)
    (hsource : ‖closure α L s t 0‖ ≤ (m : ℝ) * R / 4) :
    ∃! ξ : ℂ, ‖ξ‖ ≤ R ∧ closure α L s t ξ = 0 := by
  have hmap := correction_maps_ball hm α L s t hR hs hsmall hsource
  have hLip := correction_lipschitz_on_ball hm α L s t hs hsmall
  have hcon : ContractingWith (1 / 2 : ℝ≥0)
      (hmap.restrict (correction α L s t) (closedBall 0 R) (closedBall 0 R)) := by
    refine ⟨by norm_num, ?_⟩
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact hLip.dist_le_mul x x.property y y.property
  have hzero : (0 : ℂ) ∈ closedBall 0 R := by simp [hR]
  obtain ⟨ξ, hξ, hfix, _⟩ := ContractingWith.exists_fixedPoint'
    isClosed_closedBall.isComplete hmap hcon hzero (edist_ne_top _ _)
  have hz := (correction_fixed_iff (by omega) α L s t ξ).mp hfix
  refine ⟨ξ, ⟨mem_closedBall_zero_iff.mp hξ, hz⟩, ?_⟩
  intro η hη
  have hηmem : η ∈ closedBall 0 R := mem_closedBall_zero_iff.mpr hη.1
  have hηfix := (correction_fixed_iff (by omega) α L s t η).mpr hη.2
  have h := (lipschitzOnWith_iff_norm_sub_le.mp hLip) hηmem hξ
  rw [hηfix, hfix] at h
  have hn : ‖η - ξ‖ = 0 := by
    norm_num at h
    nlinarith [norm_nonneg (η - ξ)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

theorem closure_root_norm_bound {m : ℕ} (hm : 2 ≤ m)
    (α L s t : Fin m → ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ j, |s j| ≤ 1)
    (hsmall : ∀ j, |α j - midpoint m j| + |t j| + R ≤ 1 / 4)
    {ξ : ℂ} (hξ : ‖ξ‖ ≤ R) (hzero : closure α L s t ξ = 0) :
    ‖ξ‖ ≤ (4 / m : ℝ) * ‖closure α L s t 0‖ := by
  have hLip := correction_lipschitz_on_ball hm α L s t hs hsmall
  have hfix := (correction_fixed_iff (by omega) α L s t ξ).mpr hzero
  have h := (lipschitzOnWith_iff_norm_sub_le.mp hLip) (mem_closedBall_zero_iff.mpr hξ)
    (by simp [hR] : (0 : ℂ) ∈ closedBall 0 R)
  rw [hfix] at h
  norm_num at h
  have htri := norm_sub_le (ξ - correction α L s t 0) (-correction α L s t 0)
  simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at htri
  have hn : ‖correction α L s t 0‖ = (2 / m : ℝ) * ‖closure α L s t 0‖ := by
    simp only [correction, zero_sub, norm_neg, norm_mul, norm_inverseScale]
  rw [hn] at htri
  calc
    _ ≤ 2 * ((2 / m : ℝ) * ‖closure α L s t 0‖) := by linarith
    _ = _ := by ring

end
end Erdos1045.EventualExact.LensClosure
