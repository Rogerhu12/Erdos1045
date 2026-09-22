import StructuralNote.FixedDualClassificationRecurrenceWronskian

/-! Finite-kernel sign propagation from a few endpoint values, without a derivative-limit theorem. -/

namespace StructuralNote.FixedDualClassificationKernelSignsPropagation

open Real Finset Erdos1045.EventualExact
open FixedDualClassificationKernel FixedDualClassificationRecurrence
open FixedDualClassificationRecurrenceWronskian
noncomputable section

def gridKernel (m r : ℕ) : ℝ :=
  finiteKernel (2 * m) ((r : ℝ) * (2 * Real.pi / (2 * m : ℕ)))

theorem positive_prefix {m r s : ℕ} (hm : 0 < m) (hrs : r ≤ s)
    (hs : s ≤ (m - 1) / 2) (hK : 0 < gridKernel m s) : 0 < gridKernel m r := by
  have hc := grid_cosine_pos hm (r := r) (by omega)
  have hd := grid_cosine_pos hm (r := s) (by omega)
  have h := ratio_antitone hm (R := (m - 1) / 2) (by omega) hrs hs
  exact (div_pos_iff_of_pos_right hc).mp ((div_pos hK hd).trans_le h)

theorem negative_suffix {m r s : ℕ} (hm : 0 < m) (hrs : r ≤ s)
    (hs : s ≤ (m - 1) / 2) (hK : gridKernel m r < 0) : gridKernel m s < 0 := by
  have hc := grid_cosine_pos hm (r := r) (by omega)
  have hd := grid_cosine_pos hm (r := s) (by omega)
  have h := ratio_antitone hm (R := (m - 1) / 2) (by omega) hrs hs
  have hh := (div_lt_iff₀ hd).mp (h.trans_lt (div_neg_of_neg_of_pos hK hc))
  simpa only [gridKernel, zero_mul] using hh

theorem grid_angle_lt_pi_half {m r : ℕ} (hm : 0 < m) (hr : 2 * r < m) :
    (r : ℝ) * (2 * Real.pi / (2 * m : ℕ)) < Real.pi / 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hrR : 2 * (r : ℝ) < m := by exact_mod_cast hr
  rw [show (r : ℝ) * (2 * Real.pi / (2 * m : ℕ)) = (r : ℝ) * Real.pi / m by push_cast; ring]
  apply (div_lt_iff₀ hmR).mpr
  nlinarith [mul_lt_mul_of_pos_right hrR pi_pos]

theorem positive_decreasing_step {m r s : ℕ} (hm : 0 < m) (hrs : r + 1 ≤ s)
    (hs : s ≤ (m - 1) / 2) (hK : 0 < gridKernel m s) :
    gridKernel m (r + 1) < gridKernel m r := by
  have hKr := positive_prefix hm (show r ≤ s by omega) hs hK
  have hb : 0 < 2 * Real.pi / (2 * m : ℕ) := by positivity
  have hc := grid_cosine_pos hm (r := r) (by omega)
  have hcc : cos (((r : ℝ) + 1) * (2 * Real.pi / (2 * m : ℕ))) <
      cos ((r : ℝ) * (2 * Real.pi / (2 * m : ℕ))) := by
    apply strictAntiOn_cos
    · constructor
      · positivity
      · have ht := grid_angle_lt_pi_half hm (r := r) (by omega); linarith [pi_pos]
    · constructor
      · positivity
      · have ht := grid_angle_lt_pi_half hm (r := r + 1) (by omega)
        simp only [Nat.cast_add, Nat.cast_one] at ht
        linarith [pi_pos]
    · nlinarith
  have hw := wronskian_nonpos hm (R := (m - 1) / 2) (r := r) (by omega) (by omega)
  unfold wronskian at hw
  unfold gridKernel at hKr ⊢
  simp only [Nat.cast_add, Nat.cast_one]
  nlinarith [mul_lt_mul_of_pos_left hcc hKr]

theorem negative_strict_second_difference {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (hrm : 2 * r < m) (hK : gridKernel m r < 0) :
    gridKernel m (r + 1) - gridKernel m r > gridKernel m r - gridKernel m (r - 1) := by
  have hrec := finiteKernel_grid_recurrence hm hr (show r < m by omega)
  dsimp only at hrec
  have he : ((r : ℝ) - 1) = ((r - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
  rw [he] at hrec
  have hc := grid_cosine_pos hm hrm
  have hb0 : 0 < (2 * Real.pi / (2 * m : ℕ)) / 2 := by positivity
  have hbπ : (2 * Real.pi / (2 * m : ℕ)) / 2 < Real.pi := by
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    have hm0 : (0 : ℝ) < m := by linarith
    rw [show (2 * Real.pi / (2 * m : ℕ)) / 2 = Real.pi / (2 * m) by push_cast; ring]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * m)).mpr
    nlinarith [pi_pos]
  have hsb := sin_pos_of_pos_of_lt_pi hb0 hbπ
  have ht0 : 0 < (r : ℝ) * (2 * Real.pi / (2 * m : ℕ)) := by positivity
  have htπ := grid_angle_lt_pi_half hm hrm
  have hst := sin_pos_of_pos_of_lt_pi ht0 (by linarith [pi_pos])
  have hp : 0 < 2 * sin ((2 * Real.pi / (2 * m : ℕ)) / 2) ^ 2 *
      cos ((r : ℝ) * (2 * Real.pi / (2 * m : ℕ))) /
        sin ((r : ℝ) * (2 * Real.pi / (2 * m : ℕ))) ^ 2 := by positivity
  have hn := mul_nonneg (sub_nonneg.mpr (cos_le_one (2 * Real.pi / (2 * m : ℕ)))) (le_of_lt (neg_pos.mpr hK))
  unfold gridKernel at hK hn ⊢
  simp only [Nat.cast_add, Nat.cast_one] at hrec ⊢
  nlinarith

theorem negative_differences_mono {m a u v : ℕ} (hm : 0 < m)
    (ha : a ≤ u + 1) (huv : u ≤ v) (hv : v + 1 ≤ (m - 1) / 2)
    (hK : gridKernel m a < 0) :
    gridKernel m (u + 1) - gridKernel m u ≤ gridKernel m (v + 1) - gridKernel m v := by
  revert hv
  induction v, huv using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ v huv ih =>
    intro hv
    have hneg := negative_suffix hm (show a ≤ v + 1 by omega) (by omega) hK
    have hstep := negative_strict_second_difference hm (r := v + 1) (by omega) (by omega) hneg
    simp only [Nat.add_sub_cancel] at hstep
    exact (ih (by omega)).trans hstep.le

theorem positive_secant_forces_increase {m a b r : ℕ} (hm : 0 < m)
    (hab : a < b) (hbr : b ≤ r) (hr : r + 1 ≤ (m - 1) / 2)
    (hK : gridKernel m a < 0) (hsec : gridKernel m a < gridKernel m b) :
    gridKernel m r < gridKernel m (r + 1) := by
  have hex : ∃ j ∈ Ico a b, 0 < gridKernel m (j + 1) - gridKernel m j := by
    by_contra! hn
    have hh := sum_nonpos (fun j hj => hn j hj)
    rw [sum_Ico_sub (gridKernel m) hab.le] at hh
    linarith
  obtain ⟨j, hj, hpos⟩ := hex
  have hd := negative_differences_mono hm (a := a) (u := j) (v := r)
    (by have := (mem_Ico.mp hj).1; omega)
    (by have := (mem_Ico.mp hj).2; omega) hr hK
  linarith

end
end StructuralNote.FixedDualClassificationKernelSignsPropagation
