import StructuralNote.FixedDualIntervals
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Exact signs of the explicit limiting kernel, and two negative increasing
sample values strictly before Real.pi/4. No numerical sign oracle is used. -/

namespace StructuralNote.KernelSignsEndpoints

open Real Filter Set FixedDualPrimitive FixedDualIntervals
open scoped Topology
noncomputable section

theorem twelfth_trig_bounds :
    (258 : ℝ) / 1000 ≤ sin (Real.pi / 12) ∧ sin (Real.pi / 12) ≤ 259 / 1000 ∧
      0 ≤ cos (Real.pi / 12) ∧ cos (Real.pi / 12) ≤ 97 / 100 := by
  have hs2 := sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs3 := sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have h2 : (1414 : ℝ) / 1000 ≤ sqrt 2 ∧ sqrt 2 ≤ 1415 / 1000 := by
    constructor <;> nlinarith [sqrt_nonneg 2]
  have hp : (sqrt 2 * sqrt 3) ^ 2 = 6 := by rw [mul_pow, hs2, hs3]; norm_num
  have hprod : (2449 : ℝ) / 1000 ≤ sqrt 2 * sqrt 3 ∧ sqrt 2 * sqrt 3 ≤ 2450 / 1000 := by
    have hn := mul_nonneg (sqrt_nonneg 2) (sqrt_nonneg 3)
    constructor <;> nlinarith
  have hsin : sin (Real.pi / 12) = (sqrt 2 * sqrt 3 - sqrt 2) / 4 := by
    rw [show Real.pi / 12 = Real.pi / 4 - Real.pi / 6 by ring, sin_sub,
      sin_pi_div_four, cos_pi_div_six, cos_pi_div_four, sin_pi_div_six]
    ring
  have hcos : cos (Real.pi / 12) = (sqrt 2 * sqrt 3 + sqrt 2) / 4 := by
    rw [show Real.pi / 12 = Real.pi / 4 - Real.pi / 6 by ring, cos_sub,
      cos_pi_div_four, cos_pi_div_six, sin_pi_div_four, sin_pi_div_six]
    ring
  rw [hsin, hcos]
  constructor
  · linarith [hprod.1, h2.2]
  constructor
  · linarith [hprod.2, h2.1]
  constructor <;> linarith [hprod.1, hprod.2, h2.1, h2.2]

theorem kernel_pi_div_twelve_pos : 0 < kernel (Real.pi / 12) := by
  obtain ⟨hslo, hshi, hc0, hchi⟩ := twelfth_trig_bounds
  have hs : 0 < sin (Real.pi / 12) := by linarith
  have hlog := log_le_sub_one_of_pos (show 0 < 2 * (2 * sin (Real.pi / 12)) by positivity)
  rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : 2 * sin (Real.pi / 12) ≠ 0)] at hlog
  have hL : 1 + log (2 * sin (Real.pi / 12)) ≤ 173 / 500 := by
    linarith [log_two_interval.1]
  have hleft : cos (Real.pi / 12) * (1 + log (2 * sin (Real.pi / 12))) ≤ 16781 / 50000 := by
    have h := mul_le_mul_of_nonneg_left hL hc0
    have hh := mul_le_mul_of_nonneg_right hchi (by norm_num : (0 : ℝ) ≤ 173 / 500)
    linarith
  have hpi : (314 : ℝ) / 100 < Real.pi := by linarith [pi_gt_d20]
  have hangle : (157 : ℝ) / 120 ≤ Real.pi / 2 - Real.pi / 12 := by linarith
  have hright := mul_le_mul hangle hslo (by norm_num : (0 : ℝ) ≤ 258 / 1000)
    (by linarith : 0 ≤ Real.pi / 2 - Real.pi / 12)
  unfold kernel
  nlinarith

def kernelFirst (u : ℝ) : ℝ :=
  sin u * log (2 * sin u) / 2 - cos u ^ 2 / (2 * sin u) + (Real.pi / 2 - u) * cos u / 2

theorem kernel_hasDerivAt {u : ℝ} (hu : sin u ≠ 0) :
    HasDerivAt kernel (kernelFirst u) u := by
  have hd := (((hasDerivAt_cos u).mul ((log_sine_hasDerivAt hu).const_add 1)).const_mul (-(1 / 2))).add
    ((((hasDerivAt_const u (Real.pi / 2)).sub (hasDerivAt_id u)).mul (hasDerivAt_sin u)).const_mul (1 / 2))
  convert hd using 1 <;> try rfl
  · funext t
    simp only [kernel, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, id_eq]
    ring
  · simp only [kernelFirst, id_eq, Pi.sub_apply]
    field_simp
    ring

theorem kernelFirst_continuousAt {u : ℝ} (hu : sin u ≠ 0) : ContinuousAt kernelFirst u := by
  unfold kernelFirst
  have hl := (continuousAt_const.mul continuous_sin.continuousAt).log
    (show 2 * sin u ≠ 0 from mul_ne_zero (by norm_num) hu)
  exact ((continuous_sin.continuousAt.mul hl).div_const 2).sub
    ((continuous_cos.continuousAt.pow 2).div (continuousAt_const.mul continuous_sin.continuousAt)
      (mul_ne_zero (by norm_num) hu)) |>.add
        (((continuousAt_const.sub continuousAt_id).mul continuous_cos.continuousAt).div_const 2)

theorem kernel_pi_div_four_formula :
    kernel (Real.pi / 4) = sqrt 2 / 4 * (Real.pi / 4 - 1 - log 2 / 2) := by
  rw [kernel, sin_pi_div_four, cos_pi_div_four]
  have he : 2 * (sqrt 2 / 2) = sqrt 2 := by ring
  rw [he, log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem kernel_pi_div_four_neg : kernel (Real.pi / 4) < 0 := by
  rw [kernel_pi_div_four_formula]
  apply mul_neg_of_pos_of_neg (by positivity)
  linarith [pi_lt_four, log_two_interval.1]

theorem kernelFirst_pi_div_four_formula :
    kernelFirst (Real.pi / 4) = sqrt 2 / 4 * (log 2 / 2 - 1 + Real.pi / 4) := by
  have hs : sqrt 2 ≠ 0 := (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  rw [kernelFirst, sin_pi_div_four, cos_pi_div_four]
  have he : 2 * (sqrt 2 / 2) = sqrt 2 := by ring
  rw [he, log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp
  ring

theorem kernelFirst_pi_div_four_pos : 0 < kernelFirst (Real.pi / 4) := by
  rw [kernelFirst_pi_div_four_formula]
  apply mul_pos (by positivity)
  linarith [pi_gt_three, log_two_interval.1]

theorem kernel_deriv_pi_div_four_pos : 0 < deriv kernel (Real.pi / 4) := by
  rw [(kernel_hasDerivAt (by rw [sin_pi_div_four]; positivity)).deriv]
  exact kernelFirst_pi_div_four_pos

theorem exists_negative_increasing_pair :
    ∃ a b : ℝ, Real.pi / 12 < a ∧ a < b ∧ b < Real.pi / 4 ∧ kernel a < kernel b ∧ kernel b < 0 := by
  have hs : sin (Real.pi / 4) ≠ 0 := by rw [sin_pi_div_four]; positivity
  have hnear : ∀ᶠ t in 𝓝 (Real.pi / 4), Real.pi / 12 < t ∧ t < Real.pi / 2 ∧
      kernel t < 0 ∧ 0 < kernelFirst t := by
    filter_upwards [Ioo_mem_nhds (show Real.pi / 12 < Real.pi / 4 by linarith [pi_pos])
      (show Real.pi / 4 < Real.pi / 2 by linarith [pi_pos]),
      (kernel_hasDerivAt hs).continuousAt.eventually (gt_mem_nhds kernel_pi_div_four_neg),
      (kernelFirst_continuousAt hs).eventually (lt_mem_nhds kernelFirst_pi_div_four_pos)] with t ht hk hd
    exact ⟨ht.1, ht.2, hk, hd⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  let a := Real.pi / 4 - ε / 2
  let b := Real.pi / 4 - ε / 4
  have hab : a < b := by dsimp [a, b]; linarith
  have ha : dist a (Real.pi / 4) < ε := by
    rw [Real.dist_eq, abs_of_neg (by dsimp [a]; linarith)]
    dsimp [a]
    linarith
  have hb : dist b (Real.pi / 4) < ε := by
    rw [Real.dist_eq, abs_of_neg (by dsimp [b]; linarith)]
    dsimp [b]
    linarith
  have hinterval (t : ℝ) (ht : t ∈ Icc a b) : dist t (Real.pi / 4) < ε := by
    have htq : t < Real.pi / 4 := by have := ht.2; dsimp [b] at this; linarith
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr htq)]
    have := ht.1
    dsimp [a] at this
    linarith
  have hder (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt kernel (kernelFirst t) t := by
    have h := hball (hinterval t ht)
    exact kernel_hasDerivAt (sin_pos_of_pos_of_lt_pi (by linarith [h.1, pi_pos])
      (by linarith [h.2.1, pi_pos])).ne'
  have hmono : StrictMonoOn kernel (Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · exact fun t ht => (hder t ht).continuousAt.continuousWithinAt
    · intro t ht
      have ht' : t ∈ Icc a b := interior_subset ht
      rw [(hder t ht').deriv]
      exact (hball (hinterval t ht')).2.2.2
  exact ⟨a, b, (hball ha).1, hab, by dsimp [b]; linarith,
    hmono ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab, (hball hb).2.2.1⟩

theorem exists_negative_increasing_pair_pos :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < Real.pi / 4 ∧ kernel a < kernel b ∧ kernel b < 0 := by
  obtain ⟨a, b, ha, hab, hb, hK, hKb⟩ := exists_negative_increasing_pair
  exact ⟨a, b, by linarith [pi_pos], hab, hb, hK, hKb⟩

end
end StructuralNote.KernelSignsEndpoints
