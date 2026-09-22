import StructuralNote.ExplicitKernelRate
import StructuralNote.FixedDualClassificationKernelUniformIdentification
import StructuralNote.FixedDualClassificationKernelUniformFinal
import StructuralNote.FixedDualClassificationKernelSignsTransfer
import StructuralNote.FixedDualClassificationKernelSignsFinal
import StructuralNote.KernelSignsEndpoints

/-! Explicit transfer of the finite-kernel rate to the identified logarithmic
kernel, including reusable compact sign margins. -/

namespace StructuralNote.ExplicitKernelRateIdentification

open Real Finset Erdos1045.EventualExact Set
open FixedDualPrimitive FixedDualIntervals FixedDualClassificationKernel
open FixedDualClassificationKernelUniformConvergence
open FixedDualClassificationKernelUniformIdentification
open FixedDualClassificationKernelUniformFinal
open FixedDualClassificationKernelSignsPropagation FixedDualClassificationKernelSignsTransfer
open FixedDualClassificationKernelSignsFinal
open FixedDualClassificationRecurrenceWronskian
open KernelSignsEndpoints
open ExplicitKernelRate
noncomputable section

/-- Identification turns the explicit series rate into an explicit kernel rate. -/
theorem explicit_uniform_grid_kernel {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∀ m ≥ gridThreshold η ε, ∀ r : ℕ, ∀ t ∈ Set.Ioo 0 Real.pi,
      (2 * m : ℕ) * t = (r : ℝ) * (2 * Real.pi) → η ≤ |sin t| →
      |finiteKernel (2 * m) t - kernel t| < ε := by
  intro m hm r t ht hgrid hsin
  rw [← seriesLimit_eq_kernel ht]
  exact explicit_uniform_grid_series_limit hη hε m hm r t hgrid hsin

/-- A closed compact-set version; its threshold is the displayed arithmetic expression. -/
theorem explicit_uniform_grid_kernel_on_compact {δ ε : ℝ} (hδ : 0 < δ)
    (hδπ : δ ≤ Real.pi / 2) (hε : 0 < ε) :
    ∀ m ≥ gridThreshold (sin δ) ε, ∀ r : ℕ, ∀ t ∈ Set.Icc δ (Real.pi - δ),
      (2 * m : ℕ) * t = (r : ℝ) * (2 * Real.pi) →
      |finiteKernel (2 * m) t - kernel t| < ε := by
  have hsin : 0 < sin δ := sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  intro m hm r t ht hgrid
  exact explicit_uniform_grid_kernel hsin hε m hm r t
    ⟨hδ.trans_le ht.1, by linarith [ht.2]⟩ hgrid
    (sine_lower_on_compact hδ hδπ ht)

/-- A positive compact margin transfers at the same explicit threshold. -/
theorem explicit_positive_on_compact {δ μ : ℝ} (hδ : 0 < δ)
    (hδπ : δ ≤ Real.pi / 2) (hμ : 0 < μ)
    (hK : ∀ t ∈ Set.Icc δ (Real.pi - δ), μ ≤ kernel t) :
    ∀ m ≥ gridThreshold (sin δ) μ, ∀ r : ℕ, ∀ t ∈ Set.Icc δ (Real.pi - δ),
      (2 * m : ℕ) * t = (r : ℝ) * (2 * Real.pi) → 0 < finiteKernel (2 * m) t := by
  intro m hm r t ht hgrid
  have herr := explicit_uniform_grid_kernel_on_compact hδ hδπ hμ m hm r t ht hgrid
  have habs := (abs_lt.mp herr).1
  linarith [hK t ht]

/-- A negative compact margin transfers at the same explicit threshold. -/
theorem explicit_negative_on_compact {δ μ : ℝ} (hδ : 0 < δ)
    (hδπ : δ ≤ Real.pi / 2) (hμ : 0 < μ)
    (hK : ∀ t ∈ Set.Icc δ (Real.pi - δ), kernel t ≤ -μ) :
    ∀ m ≥ gridThreshold (sin δ) μ, ∀ r : ℕ, ∀ t ∈ Set.Icc δ (Real.pi - δ),
      (2 * m : ℕ) * t = (r : ℝ) * (2 * Real.pi) → finiteKernel (2 * m) t < 0 := by
  intro m hm r t ht hgrid
  have herr := explicit_uniform_grid_kernel_on_compact hδ hδπ hμ m hm r t ht hgrid
  have habs := (abs_lt.mp herr).2
  linarith [hK t ht]

/-- A quantitative negative margin survives with half its size. -/
theorem explicit_negative_half_margin_on_compact {δ μ : ℝ} (hδ : 0 < δ)
    (hδπ : δ ≤ Real.pi / 2) (hμ : 0 < μ)
    (hK : ∀ t ∈ Set.Icc δ (Real.pi - δ), kernel t ≤ -μ) :
    ∀ m ≥ gridThreshold (sin δ) (μ / 2), ∀ r : ℕ,
      ∀ t ∈ Set.Icc δ (Real.pi - δ),
      (2 * m : ℕ) * t = (r : ℝ) * (2 * Real.pi) →
      finiteKernel (2 * m) t ≤ -(μ / 2) := by
  intro m hm r t ht hgrid
  have herr := explicit_uniform_grid_kernel_on_compact hδ hδπ (half_pos hμ)
    m hm r t ht hgrid
  have habs := (abs_lt.mp herr).2
  linarith [hK t ht]

/-- The endpoint certificate has a concrete rational safety margin. -/
theorem kernel_pi_div_twelve_margin :
    (1 : ℝ) / 2000 < kernel (Real.pi / 12) := by
  obtain ⟨hslo, hshi, hc0, hchi⟩ := twelfth_trig_bounds
  have hs : 0 < sin (Real.pi / 12) := by linarith
  have hlog := log_le_sub_one_of_pos (show 0 < 2 * (2 * sin (Real.pi / 12)) by positivity)
  rw [log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (by positivity : 2 * sin (Real.pi / 12) ≠ 0)] at hlog
  have hL : 1 + log (2 * sin (Real.pi / 12)) ≤ 173 / 500 := by
    linarith [log_two_interval.1]
  have hleft : cos (Real.pi / 12) * (1 + log (2 * sin (Real.pi / 12))) ≤
      16781 / 50000 := by
    have h := mul_le_mul_of_nonneg_left hL hc0
    have hh := mul_le_mul_of_nonneg_right hchi (by norm_num : (0 : ℝ) ≤ 173 / 500)
    linarith
  have hangle : (157 : ℝ) / 120 ≤ Real.pi / 2 - Real.pi / 12 := by
    linarith [show (314 : ℝ) / 100 < Real.pi by linarith [pi_gt_d20]]
  have hright := mul_le_mul hangle hslo (by norm_num : (0 : ℝ) ≤ 258 / 1000)
    (by linarith : 0 ≤ Real.pi / 2 - Real.pi / 12)
  unfold kernel
  norm_num at hright ⊢
  nlinarith

/-- A uniform derivative margin on a concrete left neighborhood of `π/4`. -/
theorem kernelFirst_quarter_neighborhood {u : ℝ}
    (hu : u ∈ Set.Icc (Real.pi / 4 - 1 / 500) (Real.pi / 4)) :
    (1 : ℝ) / 100 < kernelFirst u := by
  have hs2 := sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsq : (1414 : ℝ) / 1000 ≤ sqrt 2 ∧ sqrt 2 ≤ 1415 / 1000 := by
    constructor <;> nlinarith [sqrt_nonneg 2]
  have hu0 : 0 ≤ u := by linarith [Real.pi_gt_three, hu.1]
  have hdist : |u - Real.pi / 4| ≤ 1 / 500 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hu.2)]
    linarith [hu.1]
  have hsclose := abs_sin_sub_sin_le u (Real.pi / 4)
  have hcclose := abs_cos_sub_cos_le u (Real.pi / 4)
  rw [sin_pi_div_four] at hsclose
  rw [cos_pi_div_four] at hcclose
  have hslo : (7 : ℝ) / 10 ≤ sin u := by
    have := (abs_le.mp hsclose).1
    linarith [hsq.1, hdist]
  have hclo : (7 : ℝ) / 10 ≤ cos u := by
    have hmono := cos_le_cos_of_nonneg_of_le_pi hu0
      (by linarith [Real.pi_pos] : Real.pi / 4 ≤ Real.pi) hu.2
    rw [cos_pi_div_four] at hmono
    linarith [hsq.1]
  have hchi : cos u ≤ (71 : ℝ) / 100 := by
    have := (abs_le.mp hcclose).2
    linarith [hsq.2, hdist]
  have hspos : 0 < sin u := lt_of_lt_of_le (by norm_num) hslo
  have hx : 0 < 2 * sin u := by positivity
  have hinv : (2 * sin u)⁻¹ ≤ (5 : ℝ) / 7 := by
    have hbase : (7 : ℝ) / 5 ≤ 2 * sin u := by linarith
    calc
      _ ≤ ((7 : ℝ) / 5)⁻¹ :=
        (by simpa only [one_div] using
          one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 7 / 5) hbase)
      _ = _ := by norm_num
  have hlog : (2 : ℝ) / 7 ≤ log (2 * sin u) := by
    have := one_sub_inv_le_log_of_pos hx
    linarith
  have hfirst : (1 : ℝ) / 10 ≤ sin u * log (2 * sin u) / 2 := by
    have := mul_le_mul hslo hlog (by norm_num : (0 : ℝ) ≤ 2 / 7) hspos.le
    nlinarith
  have hsqcos : cos u ^ 2 ≤ ((71 : ℝ) / 100) ^ 2 := by
    nlinarith [sq_nonneg ((71 : ℝ) / 100 - cos u)]
  have hratio : cos u ^ 2 / (2 * sin u) ≤ (5041 : ℝ) / 14000 := by
    apply (div_le_iff₀ hx).2
    nlinarith
  have hangle : (157 : ℝ) / 200 < Real.pi / 2 - u := by
    have hpi : (314 : ℝ) / 100 < Real.pi := by linarith [Real.pi_gt_d20]
    linarith [hu.2]
  have hlast : (1099 : ℝ) / 4000 < (Real.pi / 2 - u) * cos u / 2 := by
    have := mul_lt_mul hangle hclo (by norm_num : (0 : ℝ) < 7 / 10)
      (by linarith [Real.pi_pos, hu.2] : 0 ≤ Real.pi / 2 - u)
    nlinarith
  unfold kernelFirst
  nlinarith

theorem kernel_strictMono_quarter_neighborhood :
    StrictMonoOn kernel (Set.Icc (Real.pi / 4 - 1 / 500) (Real.pi / 4)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · intro u hu
    have hsin : sin u ≠ 0 :=
      (sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_gt_three, hu.1])
        (by linarith [Real.pi_pos, hu.2])).ne'
    exact (kernel_hasDerivAt hsin).continuousAt.continuousWithinAt
  · intro u hu
    have hu' : u ∈ Set.Icc (Real.pi / 4 - 1 / 500) (Real.pi / 4) :=
      interior_subset hu
    have hsin : sin u ≠ 0 :=
      (sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_gt_three, hu'.1])
        (by linarith [Real.pi_pos, hu'.2])).ne'
    rw [(kernel_hasDerivAt hsin).deriv]
    exact (by norm_num : (0 : ℝ) < 1 / 100).trans (kernelFirst_quarter_neighborhood hu')

theorem kernel_secant_quarter_neighborhood {u v : ℝ}
    (hu : u ∈ Set.Icc (Real.pi / 4 - 1 / 500) (Real.pi / 4))
    (hv : v ∈ Set.Icc (Real.pi / 4 - 1 / 500) (Real.pi / 4)) (huv : u < v) :
    (v - u) / 100 < kernel v - kernel u := by
  have hmono : StrictMonoOn (fun x : ℝ => kernel x - x / 100)
      (Set.Icc (Real.pi / 4 - 1 / 500) (Real.pi / 4)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro x hx
      have hsin : sin x ≠ 0 :=
        (sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_gt_three, hx.1])
          (by linarith [Real.pi_pos, hx.2])).ne'
      exact ((kernel_hasDerivAt hsin).sub ((hasDerivAt_id x).div_const 100)).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : x ∈ Set.Icc (Real.pi / 4 - 1 / 500) (Real.pi / 4) :=
        interior_subset hx
      have hsin : sin x ≠ 0 :=
        (sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_gt_three, hx'.1])
          (by linarith [Real.pi_pos, hx'.2])).ne'
      have hd := (kernel_hasDerivAt hsin).sub ((hasDerivAt_id x).div_const 100)
      have he : deriv (fun y : ℝ => kernel y - y / 100) x =
          kernelFirst x - 1 / 100 := by
        have hfun : (fun y : ℝ => kernel y - y / 100) =
            kernel - fun y : ℝ => y / 100 := by
          funext y
          rfl
        rw [hfun]
        simpa only [id_eq] using hd.deriv
      rw [he]
      exact sub_pos.mpr (kernelFirst_quarter_neighborhood hx')
  have := hmono hu hv huv
  dsimp only at this
  linarith

/-- Two concrete anchors replace the former neighborhood-chosen pair. -/
theorem explicit_negative_increasing_pair :
    let a := Real.pi / 4 - 1 / 1000
    let b := Real.pi / 4 - 1 / 2000
    0 < a ∧ a < b ∧ b < Real.pi / 4 ∧ kernel a < kernel b ∧ kernel b < 0 := by
  dsimp
  have hmono := kernel_strictMono_quarter_neighborhood
  have ha_mem : Real.pi / 4 - 1 / 1000 ∈
      Set.Icc (Real.pi / 4 - 1 / 500) (Real.pi / 4) := by
    constructor
    · norm_num
      linarith
    · norm_num
  have hb_mem : Real.pi / 4 - 1 / 2000 ∈
      Set.Icc (Real.pi / 4 - 1 / 500) (Real.pi / 4) := by
    constructor
    · norm_num
      linarith
    · norm_num
  have hq_mem : Real.pi / 4 ∈
      Set.Icc (Real.pi / 4 - 1 / 500) (Real.pi / 4) := by constructor <;> norm_num
  refine ⟨by linarith [Real.pi_gt_three], by norm_num, by norm_num,
    hmono ha_mem hb_mem (by norm_num), ?_⟩
  exact (hmono hb_mem hq_mem (by norm_num)).trans kernel_pi_div_four_neg

theorem kernel_pi_div_four_margin : kernel (Real.pi / 4) < -(1 : ℝ) / 10 := by
  rw [kernel_pi_div_four_formula]
  have hs2 := sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsqrt : (7 : ℝ) / 5 < sqrt 2 := by nlinarith [sqrt_nonneg 2]
  have hfactor : (7 : ℝ) / 20 < sqrt 2 / 4 := by linarith
  have hinner : Real.pi / 4 - 1 - log 2 / 2 < -(3 : ℝ) / 10 := by
    linarith [Real.pi_lt_four, log_two_interval.1]
  have hneg : Real.pi / 4 - 1 - log 2 / 2 < 0 := hinner.trans (by norm_num)
  calc
    sqrt 2 / 4 * (Real.pi / 4 - 1 - log 2 / 2) <
        sqrt 2 / 4 * (-(3 : ℝ) / 10) := mul_lt_mul_of_pos_left hinner (by positivity)
    _ < (7 / 20 : ℝ) * (-(3 : ℝ) / 10) :=
      mul_lt_mul_of_neg_right hfactor (by norm_num)
    _ < -(1 : ℝ) / 10 := by norm_num

theorem sampleAngle_gt_sub_step {m : ℕ} (hm : 0 < m) (θ : ℝ) :
    θ - Real.pi / m < sampleAngle m θ := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hf := Nat.lt_floor_add_one ((θ / Real.pi) * (m : ℝ))
  have hs := mul_lt_mul_of_pos_right hf (div_pos Real.pi_pos hmR)
  unfold sampleAngle sampleIndex
  push_cast at hs ⊢
  field_simp at hs ⊢
  nlinarith [Real.pi_pos]

theorem kernelFirst_twelfth_neighborhood {u : ℝ}
    (hu : u ∈ Set.Icc (Real.pi / 12 - 1 / 100) (Real.pi / 12)) :
    kernelFirst u < 0 := by
  have hu0 : 0 < u := by linarith [Real.pi_gt_three, hu.1]
  have hu13 : u < (1 : ℝ) / 3 := by linarith [Real.pi_lt_four, hu.2]
  have hspos : 0 < sin u := sin_pos_of_pos_of_lt_pi hu0 (by linarith [Real.pi_pos, hu.2])
  have hsin : sin u ≤ (1 : ℝ) / 3 := (sin_le hu0.le).trans hu13.le
  have hcos : (9 : ℝ) / 10 ≤ cos u := by
    have hc : 1 - u ^ 2 / 2 ≤ cos u := one_sub_sq_div_two_le_cos
    nlinarith [sq_nonneg ((1 : ℝ) / 3 - u), sq_nonneg u]
  have hlog : log (2 * sin u) ≤ 0 :=
    log_nonpos (by positivity) (by linarith)
  have hfirst : sin u * log (2 * sin u) / 2 ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hspos.le hlog) (by norm_num)
  have hratio : (6 : ℝ) / 5 ≤ cos u ^ 2 / (2 * sin u) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * sin u)).2
    nlinarith [sq_nonneg (cos u - 9 / 10)]
  have hlast : (Real.pi / 2 - u) * cos u / 2 ≤ 1 := by
    have hangle0 : 0 ≤ Real.pi / 2 - u := by linarith [Real.pi_pos, hu.2]
    have hangle2 : Real.pi / 2 - u < 2 := by linarith [Real.pi_lt_four, hu0]
    have hc1 := cos_le_one u
    have hc0 : 0 ≤ cos u := hcos.trans' (by norm_num)
    have hp := mul_le_mul hangle2.le hc1 hc0 (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  unfold kernelFirst
  linarith

theorem kernel_strictAnti_twelfth_neighborhood :
    StrictAntiOn kernel (Set.Icc (Real.pi / 12 - 1 / 100) (Real.pi / 12)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · intro u hu
    have hsin : sin u ≠ 0 :=
      (sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_gt_three, hu.1])
        (by linarith [Real.pi_pos, hu.2])).ne'
    exact (kernel_hasDerivAt hsin).continuousAt.continuousWithinAt
  · intro u hu
    have hu' : u ∈ Set.Icc (Real.pi / 12 - 1 / 100) (Real.pi / 12) :=
      interior_subset hu
    have hsin : sin u ≠ 0 :=
      (sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_gt_three, hu'.1])
        (by linarith [Real.pi_pos, hu'.2])).ne'
    rw [(kernel_hasDerivAt hsin).deriv]
    exact kernelFirst_twelfth_neighborhood hu'

def positiveIntervalThreshold : ℕ :=
  max 400 (gridThreshold (1 / 5) (1 / 4000))

/-- The positive and decreasing half of `CompressionKernelSigns`, with an explicit cutoff. -/
theorem explicit_positive_decreasing_interval :
    ∀ m ≥ positiveIntervalThreshold,
      (∀ r : ℕ, (r : ℝ) * (2 * Real.pi / (2 * m : ℕ)) ≤ Real.pi / 12 →
          0 < gridKernel m r) ∧
      (∀ r : ℕ, ((r + 1 : ℕ) : ℝ) * (2 * Real.pi / (2 * m : ℕ)) ≤ Real.pi / 12 →
          gridKernel m (r + 1) < gridKernel m r) := by
  intro m hm
  have hm0 : 0 < m := by
    have : 400 ≤ m := (le_max_left 400 _).trans hm
    omega
  have hmrate : gridThreshold (1 / 5) (1 / 4000) ≤ m :=
    (le_max_right 400 _).trans hm
  have hm400 : 400 ≤ m := (le_max_left 400 _).trans hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hstep_small : Real.pi / m < (1 : ℝ) / 100 := by
    apply (div_lt_iff₀ hmR).2
    have hmR' : (400 : ℝ) ≤ m := by exact_mod_cast hm400
    nlinarith [Real.pi_lt_four]
  let θ : ℝ := Real.pi / 12
  let t : ℝ := sampleAngle m θ
  have hθ0 : 0 ≤ θ := by dsimp [θ]; positivity
  have ht_le : t ≤ θ := sampleAngle_le hm0 hθ0
  have ht_lo : θ - Real.pi / m < t := sampleAngle_gt_sub_step hm0 θ
  have ht_mem : t ∈ Set.Icc (Real.pi / 12 - 1 / 100) (Real.pi / 12) := by
    dsimp [θ] at ht_le ht_lo
    constructor <;> dsimp [t] at * <;> linarith
  have htI : t ∈ Set.Ioo 0 Real.pi := by
    constructor
    · linarith [Real.pi_gt_three, ht_mem.1]
    · linarith [Real.pi_pos, ht_mem.2]
  have hs : (1 : ℝ) / 5 ≤ |sin t| := by
    rw [abs_of_pos (sin_pos_of_pos_of_lt_pi htI.1 htI.2)]
    obtain ⟨hslo, _, _, _⟩ := twelfth_trig_bounds
    have hclose := abs_sin_sub_sin_le t (Real.pi / 12)
    have hdist : |t - Real.pi / 12| ≤ 1 / 100 := by
      rw [abs_of_nonpos (sub_nonpos.mpr ht_mem.2)]
      linarith [ht_mem.1]
    have := (abs_le.mp hclose).1
    linarith
  have hconv := explicit_uniform_grid_kernel (by norm_num : (0 : ℝ) < 1 / 5)
    (by norm_num : (0 : ℝ) < 1 / 4000) m hmrate (sampleIndex m θ) t htI
    (by simpa only [t] using sampleAngle_grid hm0 θ) hs
  change |gridKernel m (sampleIndex m θ) - kernel t| < 1 / 4000 at hconv
  have hKlower : kernel (Real.pi / 12) ≤ kernel t := by
    rcases ht_le.eq_or_lt with h | h
    · rw [h]
    · exact (kernel_strictAnti_twelfth_neighborhood ht_mem
        (show Real.pi / 12 ∈ Set.Icc (Real.pi / 12 - 1 / 100) (Real.pi / 12) by
          constructor <;> norm_num) (by simpa only [θ] using h)).le
  have hKpos : 0 < gridKernel m (sampleIndex m θ) := by
    have herr := (abs_lt.mp hconv).1
    linarith [kernel_pi_div_twelve_margin]
  have hmid : sampleIndex m θ ≤ (m - 1) / 2 :=
    index_le_middle_of_angle_lt hm0 (ht_le.trans_lt (by dsimp [θ]; linarith [Real.pi_pos]))
  constructor
  · intro r hr
    exact positive_prefix hm0 (le_sampleIndex_of_angle_le hm0 (by simpa only [θ] using hr)) hmid hKpos
  · intro r hr
    exact positive_decreasing_step hm0
      (le_sampleIndex_of_angle_le hm0 (by simpa only [θ] using hr)) hmid hKpos

/-- One displayed natural number controls the two negative/increasing anchors. -/
def negativeIntervalThreshold : ℕ :=
  max 16000 (gridThreshold (1 / 2) (1 / 1000000))

/-- The negative and increasing half of `CompressionKernelSigns`, with no eventual
quantifier and no chosen anchor. -/
theorem explicit_negative_increasing_interval :
    ∀ m ≥ negativeIntervalThreshold,
      (∀ r : ℕ, Real.pi / 4 ≤ (r : ℝ) * (2 * Real.pi / (2 * m : ℕ)) →
        (r : ℝ) * (2 * Real.pi / (2 * m : ℕ)) ≤ 5 * Real.pi / 12 →
          gridKernel m r ≤ -(1 : ℝ) / 50) ∧
      (∀ r : ℕ, Real.pi / 4 ≤ (r : ℝ) * (2 * Real.pi / (2 * m : ℕ)) →
        ((r + 1 : ℕ) : ℝ) * (2 * Real.pi / (2 * m : ℕ)) ≤ 5 * Real.pi / 12 →
          gridKernel m r < gridKernel m (r + 1)) := by
  intro m hm
  have hm0 : 0 < m := by
    have : 16000 ≤ m := (le_max_left 16000 _).trans hm
    omega
  have hmrate : gridThreshold (1 / 2) (1 / 1000000) ≤ m :=
    (le_max_right 16000 _).trans hm
  have hm16000 : 16000 ≤ m := (le_max_left 16000 _).trans hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hstep_small : Real.pi / m < (1 : ℝ) / 4000 := by
    apply (div_lt_iff₀ hmR).2
    have hmR' : (16000 : ℝ) ≤ m := by exact_mod_cast hm16000
    nlinarith [Real.pi_lt_four]
  let a : ℝ := Real.pi / 4 - 1 / 1000
  let b : ℝ := Real.pi / 4 - 1 / 2000
  let ta : ℝ := sampleAngle m a
  let tb : ℝ := sampleAngle m b
  have ha0 : 0 ≤ a := by dsimp [a]; linarith [Real.pi_gt_three]
  have hb0 : 0 ≤ b := by dsimp [b]; linarith [Real.pi_gt_three]
  have hta_le : ta ≤ a := sampleAngle_le hm0 ha0
  have htb_le : tb ≤ b := sampleAngle_le hm0 hb0
  have hta_lo : a - Real.pi / m < ta := sampleAngle_gt_sub_step hm0 a
  have htb_lo : b - Real.pi / m < tb := sampleAngle_gt_sub_step hm0 b
  have hta_mem : ta ∈ Set.Icc (Real.pi / 4 - 1 / 500) (Real.pi / 4) := by
    dsimp [a] at hta_le hta_lo
    constructor <;> dsimp [ta] at * <;> linarith
  have htb_mem : tb ∈ Set.Icc (Real.pi / 4 - 1 / 500) (Real.pi / 4) := by
    dsimp [b] at htb_le htb_lo
    constructor <;> dsimp [tb] at * <;> linarith
  have hsep : (1 : ℝ) / 4000 < tb - ta := by
    dsimp [a, b] at hta_le htb_lo
    linarith
  have htab : ta < tb := by linarith
  have hKsec : (1 : ℝ) / 400000 < kernel tb - kernel ta := by
    have hs := kernel_secant_quarter_neighborhood hta_mem htb_mem htab
    linarith
  have hq_mem : Real.pi / 4 ∈
      Set.Icc (Real.pi / 4 - 1 / 500) (Real.pi / 4) := by constructor <;> norm_num
  have hKtb : kernel tb < -(1 : ℝ) / 10 :=
    (kernel_strictMono_quarter_neighborhood htb_mem hq_mem
      (by dsimp [b] at htb_le; dsimp [tb]; linarith)).trans kernel_pi_div_four_margin
  have htaI : ta ∈ Set.Ioo 0 Real.pi := by
    constructor
    · linarith [Real.pi_gt_three, hta_mem.1]
    · linarith [Real.pi_pos, hta_mem.2]
  have htbI : tb ∈ Set.Ioo 0 Real.pi := by
    constructor
    · linarith [Real.pi_gt_three, htb_mem.1]
    · linarith [Real.pi_pos, htb_mem.2]
  have hsin (t : ℝ) (ht : t ∈ Set.Icc (Real.pi / 4 - 1 / 500) (Real.pi / 4)) :
      (1 : ℝ) / 2 ≤ |sin t| := by
    have ht0 : 0 < t := by linarith [Real.pi_gt_three, ht.1]
    rw [abs_of_pos (sin_pos_of_pos_of_lt_pi ht0 (by linarith [Real.pi_pos, ht.2]))]
    have hs2 := sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hsqrt : (1414 : ℝ) / 1000 ≤ sqrt 2 := by nlinarith [sqrt_nonneg 2]
    have hclose := abs_sin_sub_sin_le t (Real.pi / 4)
    rw [sin_pi_div_four] at hclose
    have hdist : |t - Real.pi / 4| ≤ 1 / 500 := by
      rw [abs_of_nonpos (sub_nonpos.mpr ht.2)]
      linarith [ht.1]
    have := (abs_le.mp hclose).1
    linarith
  have hfa := explicit_uniform_grid_kernel (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 1000000) m hmrate (sampleIndex m a) ta htaI
    (by simpa only [ta] using sampleAngle_grid hm0 a) (hsin ta hta_mem)
  have hfb := explicit_uniform_grid_kernel (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 1000000) m hmrate (sampleIndex m b) tb htbI
    (by simpa only [tb] using sampleAngle_grid hm0 b) (hsin tb htb_mem)
  change |gridKernel m (sampleIndex m a) - kernel ta| < 1 / 1000000 at hfa
  change |gridKernel m (sampleIndex m b) - kernel tb| < 1 / 1000000 at hfb
  have hKfb : gridKernel m (sampleIndex m b) < 0 := by
    have := (abs_lt.mp hfb).2
    linarith
  have hKfb_margin : gridKernel m (sampleIndex m b) ≤ -(9 : ℝ) / 100 := by
    have := (abs_lt.mp hfb).2
    linarith
  have hKsec_fin : gridKernel m (sampleIndex m a) < gridKernel m (sampleIndex m b) := by
    have haerr := (abs_lt.mp hfa).2
    have hberr := (abs_lt.mp hfb).1
    linarith
  have hidx : sampleIndex m a < sampleIndex m b := by
    have hstep : 0 < 2 * Real.pi / (2 * m : ℕ) := by positivity
    have hiR : (sampleIndex m a : ℝ) < sampleIndex m b := by
      apply (mul_lt_mul_iff_left₀ hstep).mp
      simpa only [ta, tb, sampleAngle] using htab
    exact_mod_cast hiR
  constructor
  · intro r hlo hhi
    have hsr := sampleIndex_le_of_lt_angle hm0 hb0
      (show b < (r : ℝ) * (2 * Real.pi / (2 * m : ℕ)) by
        dsimp [b]
        linarith)
    have hrm := index_le_middle_of_angle_lt hm0 (hhi.trans_lt (by linarith [Real.pi_pos]))
    have hKr := negative_suffix hm0 hsr hrm hKfb
    have hcr := grid_cosine_pos hm0 (r := r) (by omega)
    have hcs := grid_cosine_pos hm0 (r := sampleIndex m b) (by omega)
    have hratio := ratio_antitone hm0 (R := (m - 1) / 2) (by omega) hsr hrm
    have hcross := (div_le_div_iff₀ hcr hcs).mp hratio
    change gridKernel m r * cos ((sampleIndex m b : ℝ) *
        (2 * Real.pi / (2 * m : ℕ))) ≤
      gridKernel m (sampleIndex m b) *
        cos ((r : ℝ) * (2 * Real.pi / (2 * m : ℕ))) at hcross
    have hcosr : (1 : ℝ) / 4 ≤
        cos ((r : ℝ) * (2 * Real.pi / (2 * m : ℕ))) := by
      have hcos := cos_le_cos_of_nonneg_of_le_pi (by positivity)
        (by linarith [Real.pi_pos] : 5 * Real.pi / 12 ≤ Real.pi) hhi
      rw [show 5 * Real.pi / 12 = Real.pi / 2 - Real.pi / 12 by ring,
        cos_pi_div_two_sub] at hcos
      linarith [twelfth_trig_bounds.1]
    calc
      gridKernel m r ≤ gridKernel m r * cos ((sampleIndex m b : ℝ) *
          (2 * Real.pi / (2 * m : ℕ))) := by
        nlinarith [cos_le_one ((sampleIndex m b : ℝ) *
          (2 * Real.pi / (2 * m : ℕ)))]
      _ ≤ gridKernel m (sampleIndex m b) *
          cos ((r : ℝ) * (2 * Real.pi / (2 * m : ℕ))) := hcross
      _ ≤ (-(9 : ℝ) / 100) *
          cos ((r : ℝ) * (2 * Real.pi / (2 * m : ℕ))) :=
        mul_le_mul_of_nonneg_right hKfb_margin hcr.le
      _ ≤ (-(9 : ℝ) / 100) * (1 / 4) :=
        mul_le_mul_of_nonpos_left hcosr (by norm_num)
      _ ≤ -(1 : ℝ) / 50 := by norm_num
  · intro r hlo hhi
    have hsr := sampleIndex_le_of_lt_angle hm0 hb0
      (show b < (r : ℝ) * (2 * Real.pi / (2 * m : ℕ)) by
        dsimp [b]
        linarith)
    have hrm := index_le_middle_of_angle_lt hm0 (hhi.trans_lt (by linarith [Real.pi_pos]))
    exact positive_secant_forces_increase hm0 hidx hsr hrm (hKsec_fin.trans hKfb) hKsec_fin

/-- A single explicit cutoff for all four finite-kernel sign and monotonicity clauses. -/
def compressionKernelSignsThreshold : ℕ :=
  max positiveIntervalThreshold negativeIntervalThreshold

theorem explicit_compressionKernelSigns :
    ∀ m ≥ compressionKernelSignsThreshold, CompressionKernelSigns m := by
  intro m hm
  have hp := explicit_positive_decreasing_interval m
    ((le_max_left positiveIntervalThreshold negativeIntervalThreshold).trans hm)
  have hn := explicit_negative_increasing_interval m
    ((le_max_right positiveIntervalThreshold negativeIntervalThreshold).trans hm)
  exact ⟨hp.1, hp.2,
    fun r hlo hhi => (hn.1 r hlo hhi).trans_lt (by norm_num), hn.2⟩

theorem explicit_cross_negative_margin :
    ∀ m ≥ compressionKernelSignsThreshold, ∀ r : ℕ,
      Real.pi / 4 ≤ (r : ℝ) * (2 * Real.pi / (2 * m : ℕ)) →
      (r : ℝ) * (2 * Real.pi / (2 * m : ℕ)) ≤ 5 * Real.pi / 12 →
      gridKernel m r ≤ -(1 : ℝ) / 50 := by
  intro m hm
  exact (explicit_negative_increasing_interval m
    ((le_max_right positiveIntervalThreshold negativeIntervalThreshold).trans hm)).1

end
end StructuralNote.ExplicitKernelRateIdentification
