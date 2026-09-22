import StructuralNote.FixedDualSignPolynomial
import Mathlib.Analysis.Polynomial.Basic

/-! Genuine critical-point counts and right-endpoint derivative signs for the
Wronskians. These are analytic consequences of the explicit polynomial. -/

namespace StructuralNote.FixedDualWronskianRoots

open Real Polynomial FixedDualPrimitive FixedDualSignPolynomial
open Filter Set
open scoped Topology
noncomputable section

theorem interval_sine_cosine {u : ℝ} (hu : u ∈ Ioo 0 (Real.pi / 2)) :
    0 < sin u ∧ 0 < cos u :=
  ⟨sin_pos_of_pos_of_lt_pi hu.1 (by linarith [pi_pos, hu.2]),
    cos_pos_of_mem_Ioo ⟨by linarith [pi_pos, hu.1], hu.2⟩⟩

theorem critical_point_polynomial {b u : ℝ} (hu : u ∈ Ioo 0 (Real.pi / 2))
    (hz : deriv (wronskian b) u = 0) : (signPolynomial b).IsRoot (tan u) := by
  obtain ⟨hs, hc⟩ := interval_sine_cosine hu
  rw [wronskian_deriv_polynomial b hs.ne' hc.ne'] at hz
  exact (mul_eq_zero.mp hz).resolve_left (div_ne_zero (pow_ne_zero 6 hc.ne') (pow_ne_zero 2 hs.ne'))

theorem critical_points_card_le {b : ℝ} (hb : b ≠ 0) (s : Finset ℝ)
    (hs : ∀ u ∈ s, u ∈ Ioo 0 (Real.pi / 2))
    (hz : ∀ u ∈ s, deriv (wronskian b) u = 0) :
    s.card ≤ (signPolynomial b).roots.countP (0 < ·) := by
  classical
  have hdeg : (0 : WithBot ℕ) < (signPolynomial b).degree := by
    rw [signPolynomial_degree hb]
    norm_num
  have hp : signPolynomial b ≠ 0 := ne_zero_of_degree_gt hdeg
  have hsub : (s.image tan).val ≤ (signPolynomial b).roots.filter (0 < ·) := by
    apply Finset.val_le_iff_val_subset.mpr
    intro t ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    exact Multiset.mem_filter.mpr ⟨(Polynomial.mem_roots hp).mpr (critical_point_polynomial (hs u hu) (hz u hu)),
      tan_pos_of_pos_of_lt_pi_div_two (hs u hu).1 (hs u hu).2⟩
  have hinj : Set.InjOn tan (↑s : Set ℝ) := by
    intro u hu v hv huv
    apply strictMonoOn_tan.injOn _ _ huv
    · exact ⟨by linarith [pi_pos, (hs u hu).1], (hs u hu).2⟩
    · exact ⟨by linarith [pi_pos, (hs v hv).1], (hs v hv).2⟩
  have hcard := Multiset.card_le_card hsub
  rw [← Multiset.countP_eq_card_filter, ← Finset.card_def,
    Finset.card_image_of_injOn hinj] at hcard
  exact hcard

theorem positive_critical_points_card {b : ℝ} (hb : 0 < b) (s : Finset ℝ)
    (hs : ∀ u ∈ s, u ∈ Ioo 0 (Real.pi / 2))
    (hz : ∀ u ∈ s, deriv (wronskian b) u = 0) : s.card ≤ 1 :=
  (critical_points_card_le hb.ne' s hs hz).trans (positive_polynomial_root_bound hb)

theorem negative_critical_points_card {b : ℝ} (hb : 0 < b) (s : Finset ℝ)
    (hs : ∀ u ∈ s, u ∈ Ioo 0 (Real.pi / 2))
    (hz : ∀ u ∈ s, deriv (wronskian (-b)) u = 0) : s.card ≤ 2 :=
  (critical_points_card_le (neg_ne_zero.mpr hb.ne') s hs hz).trans (negative_polynomial_root_bound hb)

theorem signPolynomial_leadingCoeff {b : ℝ} (hb : b ≠ 0) :
    (signPolynomial b).leadingCoeff = 8 * b := by
  rw [← Polynomial.coeff_natDegree, natDegree_eq_of_degree_eq_some (signPolynomial_degree hb)]
  simp only [signPolynomial, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_C]
  norm_num

theorem positive_derivative_near_right {b : ℝ} (hb : 0 < b) :
    ∀ᶠ u in 𝓝[<] (Real.pi / 2), 0 < deriv (wronskian b) u := by
  have hp := (signPolynomial b).tendsto_atTop_of_leadingCoeff_nonneg
    (by rw [signPolynomial_degree hb.ne']; norm_num)
    (by rw [signPolynomial_leadingCoeff hb.ne']; positivity)
  have ht := (hp.comp tendsto_tan_pi_div_two).eventually_gt_atTop 0
  filter_upwards [ht, Ioo_mem_nhdsLT (by positivity : (0 : ℝ) < Real.pi / 2)] with u hu hdom
  obtain ⟨hs, hc⟩ := interval_sine_cosine hdom
  rw [wronskian_deriv_polynomial b hs.ne' hc.ne']
  exact mul_pos (div_pos (pow_pos hc _) (pow_pos hs _)) hu

theorem negative_derivative_near_right {b : ℝ} (hb : 0 < b) :
    ∀ᶠ u in 𝓝[<] (Real.pi / 2), deriv (wronskian (-b)) u < 0 := by
  have hn : -b ≠ 0 := neg_ne_zero.mpr hb.ne'
  have hp := (signPolynomial (-b)).tendsto_atBot_of_leadingCoeff_nonpos
    (by rw [signPolynomial_degree hn]; norm_num)
    (by rw [signPolynomial_leadingCoeff hn]; linarith)
  have ht := (hp.comp tendsto_tan_pi_div_two).eventually_lt_atBot 0
  filter_upwards [ht, Ioo_mem_nhdsLT (by positivity : (0 : ℝ) < Real.pi / 2)] with u hu hdom
  obtain ⟨hs, hc⟩ := interval_sine_cosine hdom
  rw [wronskian_deriv_polynomial (-b) hs.ne' hc.ne']
  exact mul_neg_of_pos_of_neg (div_pos (pow_pos hc _) (pow_pos hs _)) hu

end
end StructuralNote.FixedDualWronskianRoots
