import StructuralNote.FixedDualWronskianRoots
import StructuralNote.FixedDualRolle

/-! The analytic zero count for the actual witnesses. -/

namespace StructuralNote.FixedDualZeroCount

open Real Set FixedDualPrimitive FixedDualWronskianRoots FixedDualRolle
noncomputable section

theorem wronskian_continuousOn (b : ℝ) {a c : ℝ} (ha : 0 < a) (hc : c ≤ Real.pi / 2) :
    ContinuousOn (wronskian b) (Icc a c) := by
  intro u hu
  have hs : 0 < sin u := sin_pos_of_pos_of_lt_pi (ha.trans_le hu.1)
    (by linarith [hu.2, pi_pos])
  exact (wronskian_hasDerivAt b hs.ne').continuousAt.continuousWithinAt

theorem positive_wronskian_no_two {b x y : ℝ} (hb : 0 < b) (hx : 0 < x)
    (hxy : x < y) (hy : y < Real.pi / 2)
    (hzx : wronskian b x = 0) (hzy : wronskian b y = 0) : False := by
  classical
  obtain ⟨c, hc, hcz⟩ := exists_deriv_eq_zero hxy
    (wronskian_continuousOn b hx hy.le) (hzx.trans hzy.symm)
  obtain ⟨d, hd, hdz⟩ := critical_after_zero_of_negative_endpoint hy
    (wronskian_continuousOn b (hx.trans hxy) le_rfl) hzy
    (by simpa only [wronskian_pi_div_two] using neg_neg_of_pos hb)
    (positive_derivative_near_right hb)
  have hcd : c ≠ d := ne_of_lt (hc.2.trans hd.1)
  have hcard := positive_critical_points_card hb {c, d}
    (by intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl
        · exact ⟨hx.trans hc.1, hc.2.trans hy⟩
        · exact ⟨(hx.trans hxy).trans hd.1, hd.2⟩)
    (by intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl <;> assumption)
  simp [hcd] at hcard

theorem negative_wronskian_no_three {b x y z : ℝ} (hb : 0 < b) (hx : 0 < x)
    (hxy : x < y) (hyz : y < z) (hz : z < Real.pi / 2)
    (h0x : wronskian (-b) x = 0) (h0y : wronskian (-b) y = 0)
    (h0z : wronskian (-b) z = 0) : False := by
  classical
  obtain ⟨c, hc, hcz⟩ := exists_deriv_eq_zero hxy
    (wronskian_continuousOn (-b) hx (hyz.trans hz).le) (h0x.trans h0y.symm)
  obtain ⟨d, hd, hdz⟩ := exists_deriv_eq_zero hyz
    (wronskian_continuousOn (-b) (hx.trans hxy) hz.le) (h0y.trans h0z.symm)
  obtain ⟨e, he, hez⟩ := critical_after_zero_of_positive_endpoint hz
    (wronskian_continuousOn (-b) ((hx.trans hxy).trans hyz) le_rfl) h0z
    (by simpa only [wronskian_pi_div_two, neg_neg] using hb)
    (negative_derivative_near_right hb)
  have hcd : c ≠ d := ne_of_lt (hc.2.trans hd.1)
  have hde : d ≠ e := ne_of_lt (hd.2.trans he.1)
  have hce : c ≠ e := ne_of_lt ((hc.2.trans hd.1).trans (hd.2.trans he.1))
  have hcard := negative_critical_points_card hb {c, d, e}
    (by intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl
        · exact ⟨hx.trans hc.1, (hc.2.trans hyz).trans hz⟩
        · exact ⟨(hx.trans hxy).trans hd.1, hd.2.trans hz⟩
        · exact ⟨((hx.trans hxy).trans hyz).trans he.1, he.2⟩)
    (by intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl <;> assumption)
  simp [hcd, hde, hce] at hcard

theorem wronskian_zero_between (b : ℝ) {x y : ℝ} (hx : 0 < x) (hxy : x < y)
    (hy : y < Real.pi / 2) (hzx : witness b x = 0) (hzy : witness b y = 0) :
    ∃ c ∈ Ioo x y, wronskian b c = 0 := by
  have hsc : ∀ u ∈ Icc x y, 0 < sin u ∧ 0 < cos u := by
    intro u hu
    exact interval_sine_cosine ⟨hx.trans_le hu.1, hu.2.trans_lt hy⟩
  obtain ⟨c, hc, hcz⟩ := exists_hasDerivAt_eq_zero hxy
    (fun u hu => (quotient_hasDerivAt b (hsc u hu).1.ne' (hsc u hu).2.ne').continuousAt.continuousWithinAt)
    (by simp only [hzx, hzy, zero_div])
    (fun u hu => quotient_hasDerivAt b (hsc u ⟨hu.1.le, hu.2.le⟩).1.ne'
      (hsc u ⟨hu.1.le, hu.2.le⟩).2.ne')
  refine ⟨c, hc, ?_⟩
  exact (div_eq_zero_iff.mp hcz).resolve_right (pow_ne_zero 2 (hsc c ⟨hc.1.le, hc.2.le⟩).2.ne')

/-- For every positive b, H_b has at most two distinct zeros in (0, π/2). -/
theorem positive_no_three_roots {b x y z : ℝ} (hb : 0 < b) (hx : 0 < x)
    (hxy : x < y) (hyz : y < z) (hz : z < Real.pi / 2)
    (h0x : witness b x = 0) (h0y : witness b y = 0) (h0z : witness b z = 0) : False := by
  obtain ⟨c, hc, hcz⟩ := wronskian_zero_between b hx hxy (hyz.trans hz) h0x h0y
  obtain ⟨d, hd, hdz⟩ := wronskian_zero_between b (hx.trans hxy) hyz hz h0y h0z
  exact positive_wronskian_no_two hb (hx.trans hc.1) (hc.2.trans hd.1) (hd.2.trans hz) hcz hdz

/-- For every positive b, H_{-b} has at most three distinct zeros in (0, π/2). -/
theorem negative_no_four_roots {b w x y z : ℝ} (hb : 0 < b) (hw : 0 < w)
    (hwx : w < x) (hxy : x < y) (hyz : y < z) (hz : z < Real.pi / 2)
    (h0w : witness (-b) w = 0) (h0x : witness (-b) x = 0)
    (h0y : witness (-b) y = 0) (h0z : witness (-b) z = 0) : False := by
  obtain ⟨c, hc, hcz⟩ := wronskian_zero_between (-b) hw hwx ((hxy.trans hyz).trans hz) h0w h0x
  obtain ⟨d, hd, hdz⟩ := wronskian_zero_between (-b) (hw.trans hwx) hxy (hyz.trans hz) h0x h0y
  obtain ⟨e, he, hez⟩ := wronskian_zero_between (-b) ((hw.trans hwx).trans hxy) hyz hz h0y h0z
  exact negative_wronskian_no_three hb (hw.trans hc.1) (hc.2.trans hd.1)
    (hd.2.trans he.1) (he.2.trans hz) hcz hdz hez

theorem positive_roots_exhaust {b x₁ x₂ : ℝ} (hb : 0 < b) (h1 : 0 < x₁)
    (h12 : x₁ < x₂) (h2 : x₂ < Real.pi / 2)
    (hz1 : witness b x₁ = 0) (hz2 : witness b x₂ = 0)
    {x : ℝ} (hx : x ∈ Ioo 0 (Real.pi / 2)) (hz : witness b x = 0) :
    x = x₁ ∨ x = x₂ := by
  rcases lt_trichotomy x x₁ with h | h | h
  · exact (positive_no_three_roots hb hx.1 h h12 h2 hz hz1 hz2).elim
  · exact Or.inl h
  · rcases lt_trichotomy x x₂ with h' | h' | h'
    · exact (positive_no_three_roots hb h1 h h' h2 hz1 hz hz2).elim
    · exact Or.inr h'
    · exact (positive_no_three_roots hb h1 h12 h' hx.2 hz1 hz2 hz).elim

theorem negative_roots_exhaust {b y₁ y₂ y₃ : ℝ} (hb : 0 < b) (h1 : 0 < y₁)
    (h12 : y₁ < y₂) (h23 : y₂ < y₃) (h3 : y₃ < Real.pi / 2)
    (hz1 : witness (-b) y₁ = 0) (hz2 : witness (-b) y₂ = 0) (hz3 : witness (-b) y₃ = 0)
    {y : ℝ} (hy : y ∈ Ioo 0 (Real.pi / 2)) (hz : witness (-b) y = 0) :
    y = y₁ ∨ y = y₂ ∨ y = y₃ := by
  rcases lt_trichotomy y y₁ with h | h | h
  · exact (negative_no_four_roots hb hy.1 h h12 h23 h3 hz hz1 hz2 hz3).elim
  · exact Or.inl h
  · rcases lt_trichotomy y y₂ with h' | h' | h'
    · exact (negative_no_four_roots hb h1 h h' h23 h3 hz1 hz hz2 hz3).elim
    · exact Or.inr (Or.inl h')
    · rcases lt_trichotomy y y₃ with h'' | h'' | h''
      · exact (negative_no_four_roots hb h1 h12 h' h'' h3 hz1 hz2 hz hz3).elim
      · exact Or.inr (Or.inr h'')
      · exact (negative_no_four_roots hb h1 h12 h23 h'' hy.2 hz1 hz2 hz3 hz).elim

end
end StructuralNote.FixedDualZeroCount
