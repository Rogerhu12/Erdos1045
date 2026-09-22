import StructuralNote.FixedDualEndpointContinuity

/-! Exact integration of the actual witnesses on their sign intervals. -/

namespace StructuralNote.FixedDualIntegral

open Real Set MeasureTheory FixedDualPrimitive
noncomputable section

/-- The normalization of the antiperiodic dual norm: one half of the integral over (0, π). -/
def dualNorm (b : ℝ) : ℝ := (∫ u in (0 : ℝ)..Real.pi, |witness b u|) / 2

theorem abs_integral_nonnegative (b : ℝ) {a c : ℝ}
    (ha : 0 ≤ a) (hc : c ≤ Real.pi) (hac : a ≤ c)
    (hs : ∀ u ∈ Ioo a c, 0 ≤ witness b u) :
    IntervalIntegrable (fun u => |witness b u|) volume a c ∧
      (∫ u in a..c, |witness b u|) = primitive b c - primitive b a := by
  have hi := witness_integral_on_sign_interval b ha hc hac (Or.inl hs)
  refine ⟨hi.1.abs, ?_⟩
  rw [← hi.2]
  exact intervalIntegral.integral_congr_Ioo_of_le hac (fun u hu => abs_of_nonneg (hs u hu))

theorem abs_integral_nonpositive (b : ℝ) {a c : ℝ}
    (ha : 0 ≤ a) (hc : c ≤ Real.pi) (hac : a ≤ c)
    (hs : ∀ u ∈ Ioo a c, witness b u ≤ 0) :
    IntervalIntegrable (fun u => |witness b u|) volume a c ∧
      (∫ u in a..c, |witness b u|) = primitive b a - primitive b c := by
  have hi := witness_integral_on_sign_interval b ha hc hac (Or.inr hs)
  refine ⟨hi.1.abs, ?_⟩
  calc
    _ = ∫ u in a..c, -witness b u :=
      intervalIntegral.integral_congr_Ioo_of_le hac (fun u hu => abs_of_nonpos (hs u hu))
    _ = -(∫ u in a..c, witness b u) := intervalIntegral.integral_neg
    _ = _ := by rw [hi.2]; ring

theorem two_root_integral (b : ℝ) {x₁ x₂ : ℝ}
    (h1 : 0 < x₁) (h12 : x₁ < x₂) (h2 : x₂ < Real.pi / 2)
    (hs0 : ∀ u ∈ Ioo 0 x₁, witness b u ≤ 0)
    (hs1 : ∀ u ∈ Ioo x₁ x₂, 0 ≤ witness b u)
    (hs2 : ∀ u ∈ Ioo x₂ (Real.pi / 2), witness b u ≤ 0) :
    IntervalIntegrable (fun u => |witness b u|) volume 0 (Real.pi / 2) ∧
      (∫ u in (0 : ℝ)..Real.pi / 2, |witness b u|) =
        primitive b 0 - primitive b (Real.pi / 2) + 2 * primitive b x₂ - 2 * primitive b x₁ := by
  have h0 := abs_integral_nonpositive b le_rfl (by linarith [pi_pos]) h1.le hs0
  have h1' := abs_integral_nonnegative b h1.le (by linarith [pi_pos]) h12.le hs1
  have h2' := abs_integral_nonpositive b (h1.trans h12).le (by linarith [pi_pos]) h2.le hs2
  have e1 := intervalIntegral.integral_add_adjacent_intervals h0.1 h1'.1
  have e2 := intervalIntegral.integral_add_adjacent_intervals (h0.1.trans h1'.1) h2'.1
  exact ⟨(h0.1.trans h1'.1).trans h2'.1, by linarith [h0.2, h1'.2, h2'.2]⟩

theorem three_root_integral (b : ℝ) {y₁ y₂ y₃ : ℝ}
    (h1 : 0 < y₁) (h12 : y₁ < y₂) (h23 : y₂ < y₃) (h3 : y₃ < Real.pi / 2)
    (hs0 : ∀ u ∈ Ioo 0 y₁, witness b u ≤ 0)
    (hs1 : ∀ u ∈ Ioo y₁ y₂, 0 ≤ witness b u)
    (hs2 : ∀ u ∈ Ioo y₂ y₃, witness b u ≤ 0)
    (hs3 : ∀ u ∈ Ioo y₃ (Real.pi / 2), 0 ≤ witness b u) :
    IntervalIntegrable (fun u => |witness b u|) volume 0 (Real.pi / 2) ∧
      (∫ u in (0 : ℝ)..Real.pi / 2, |witness b u|) =
        primitive b 0 + primitive b (Real.pi / 2) + 2 * primitive b y₂ -
          2 * primitive b y₁ - 2 * primitive b y₃ := by
  have h0 := abs_integral_nonpositive b le_rfl (by linarith [pi_pos]) h1.le hs0
  have h1' := abs_integral_nonnegative b h1.le (by linarith [pi_pos]) h12.le hs1
  have h2' := abs_integral_nonpositive b (h1.trans h12).le (by linarith [pi_pos]) h23.le hs2
  have h3' := abs_integral_nonnegative b ((h1.trans h12).trans h23).le (by linarith [pi_pos]) h3.le hs3
  have e1 := intervalIntegral.integral_add_adjacent_intervals h0.1 h1'.1
  have e2 := intervalIntegral.integral_add_adjacent_intervals (h0.1.trans h1'.1) h2'.1
  have e3 := intervalIntegral.integral_add_adjacent_intervals ((h0.1.trans h1'.1).trans h2'.1) h3'.1
  exact ⟨((h0.1.trans h1'.1).trans h2'.1).trans h3'.1, by linarith [h0.2, h1'.2, h2'.2, h3'.2]⟩

theorem dualNorm_split (b : ℝ)
    (hp : IntervalIntegrable (fun u => |witness b u|) volume 0 (Real.pi / 2))
    (hn : IntervalIntegrable (fun u => |witness (-b) u|) volume 0 (Real.pi / 2)) :
    dualNorm b = ((∫ u in (0 : ℝ)..Real.pi / 2, |witness b u|) +
      (∫ u in (0 : ℝ)..Real.pi / 2, |witness (-b) u|)) / 2 := by
  have he : Real.pi - Real.pi / 2 = Real.pi / 2 := by ring
  have hr : IntervalIntegrable (fun u => |witness b u|) volume (Real.pi / 2) Real.pi := by
    have h := (hn.comp_sub_left Real.pi).symm
    simpa only [sub_zero, he, witness_reflection, neg_neg, abs_neg] using h
  have hreflect := intervalIntegral.integral_comp_sub_left (fun u => |witness (-b) u|)
    (a := Real.pi / 2) (b := Real.pi) Real.pi
  simp only [sub_self, he, witness_reflection, neg_neg, abs_neg] at hreflect
  unfold dualNorm
  rw [← intervalIntegral.integral_add_adjacent_intervals hp hr, hreflect]

end
end StructuralNote.FixedDualIntegral
