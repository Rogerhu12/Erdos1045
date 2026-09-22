import StructuralNote.CommonDomainClosure

/-! Quantitative smallness and strictly positive lens width on the actual common
energy domain. The bounds include the nonlinear closure correction. -/

namespace StructuralNote.CommonFiberBounds

open Erdos1045.EventualExact Complex Filter
open FiniteFourierLift SchurSpectrum LensClosure CommonClosureEnergy
open CommonDomainRadius CommonDomainClosure CommonTangentialParameters
open scoped BigOperators Topology
noncomputable section

theorem difference_of_scaled_energy {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ)
    {L : ℝ} (hL : 0 ≤ L) (hA : pairEnergy hn c ≤ L ^ 2 / (n : ℝ) ^ 2) (j : Fin n) :
    ‖difference hn c j‖ ≤ 10 * L / (n : ℝ) ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hb := (difference_sq_of_energy hn c j).trans
    (mul_le_mul_of_nonneg_left hA (by positivity : 0 ≤ 8 * Real.pi ^ 2))
  have hpi : 8 * Real.pi ^ 2 ≤ 100 := by nlinarith [Real.pi_lt_d4, Real.pi_pos]
  have hscaled : (n : ℝ) ^ 4 * ‖difference hn c j‖ ^ 2 ≤ 100 * L ^ 2 := by
    calc
      _ = (n : ℝ) ^ 2 * ((n : ℝ) ^ 2 * ‖difference hn c j‖ ^ 2) := by ring
      _ ≤ (n : ℝ) ^ 2 * (8 * Real.pi ^ 2 * (L ^ 2 / (n : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hb (sq_nonneg _)
      _ = 8 * Real.pi ^ 2 * L ^ 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hpi (sq_nonneg L)
  apply (le_div_iff₀ (sq_pos_of_pos hnR)).mpr
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  nlinarith only [hscaled]

theorem domain_energy_bounds {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (hdom : InDomain hm θ v) :
    pairEnergy (by omega) (fun j => (θ j : ℂ)) ≤ energyRadius (2 * m) ∧
      pairEnergy (by omega) v ≤ energyRadius (2 * m) := by
  have hθ := pairEnergy_nonneg (by omega) (fun j => (θ j : ℂ))
  have hv := pairEnergy_nonneg (by omega) v
  constructor <;> linarith [hdom.2.2.2]

theorem domain_angle_difference {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (hdom : InDomain hm θ v) (j : Fin (2 * m)) :
    |angleDifference (by omega) θ j| ≤ 10 * logOrder (2 * m) / (2 * m : ℝ) ^ 2 := by
  have h := difference_of_scaled_energy (by omega) (fun j => (θ j : ℂ))
    (Nat.cast_nonneg (logOrder (2 * m))) (domain_energy_bounds hm θ v hdom).1 j
  simpa only [angleDifference, difference, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, Nat.cast_mul, Nat.cast_ofNat] using h

theorem domain_coordinate_bound {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (hdom : InDomain hm θ v) (j : Fin m) :
    |coordinates hm v j| ≤ 10 * logOrder (2 * m) / (2 * m : ℝ) ^ 2 := by
  have h := difference_of_scaled_energy (by omega) v
    (Nat.cast_nonneg (logOrder (2 * m))) (domain_energy_bounds hm θ v hdom).2 (halfIndex j)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at h
  exact (coordinates_abs_le hm v j).trans h

theorem domain_height_bound {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (hdom : InDomain hm θ v) {ξ : ℂ}
    (hξ : ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2) (j : Fin m) :
    |heightParameter (coordinates hm v) ξ j| ≤
      (10 * logOrder (2 * m) + 1024) / (2 * m : ℝ) ^ 2 := by
  calc
    _ ≤ |coordinates hm v j| + |harmonicFunctional (LensClosure.midpoint m j) ξ| := abs_add_le _ _
    _ ≤ 10 * logOrder (2 * m) / (2 * m : ℝ) ^ 2 + 1024 / (2 * m : ℝ) ^ 2 :=
      add_le_add (domain_coordinate_bound hm θ v hdom j) ((harmonicFunctional_le_norm _ ξ).trans hξ)
    _ = _ := by ring

theorem eventual_order_bound : ∀ᶠ n : ℕ in atTop, 10 * (logOrder n : ℝ) + 1024 ≤ n := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hl := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hn).const_mul 40
  have hi := (tendsto_inv_atTop_zero.comp hn).const_mul 1024
  have ht : Tendsto (fun n : ℕ => (40 * Real.log n + 1024) / (n : ℝ)) atTop (𝓝 0) := by
    convert hl.add hi using 1 <;> simp only [Function.comp_def, id_eq, mul_zero, add_zero]
    funext n
    ring
  filter_upwards [ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    eventually_ge_atTop 2] with n hb hn2
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := (div_lt_iff₀ hnR).mp hb
  have hL := logOrder_le hn2
  nlinarith

theorem positive_lens_from_sizes {n a t : ℝ} (hn : 16 ≤ n)
    (ha : 2 / n ≤ a ∧ a ≤ 5 / n) (ht : |t| ≤ 1 / n) :
    0 < 2 * Real.cos a ∧ t ^ 2 ≤ 4 ∧ 1 / (2 * n ^ 2) ≤ Lens.width (2 * Real.cos a) t := by
  have hn0 : 0 < n := by linarith
  have ha0 : 0 < a := (by positivity : 0 < 2 / n).trans_le ha.1
  have ha1 : a ≤ 1 := ha.2.trans ((div_le_one hn0).mpr (by linarith))
  have hc : 0 < 2 * Real.cos a := by
    apply mul_pos (by norm_num)
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_gt_three]⟩
  have ht1 : |t| ≤ 1 := ht.trans ((div_le_one hn0).mpr (by linarith))
  have ht4 : t ^ 2 ≤ 4 := by nlinarith [(abs_le.mp ht1).1, (abs_le.mp ht1).2]
  have hcos := Real.cos_le_one_sub_mul_cos_sq (show |a| ≤ Real.pi by rw [abs_of_pos ha0]; linarith [Real.pi_gt_three])
  have hcoeff : (1 / 4 : ℝ) ≤ 4 / Real.pi ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr
    nlinarith [Real.pi_lt_four, Real.pi_pos]
  have hprod := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg a)
  have ha2 : (2 / n) ^ 2 ≤ a ^ 2 := (sq_le_sq₀ (by positivity) ha0.le).mpr ha.1
  have ht2 : t ^ 2 ≤ 1 / n ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg t) (by positivity)).mpr ht
    simpa only [sq_abs, div_pow, one_pow] using h
  have hh := BoxLensLift.height_defect ht4
  have hh' := (abs_le.mp hh).1
  refine ⟨hc, ht4, ?_⟩
  unfold Lens.width
  have ha2' : 4 / n ^ 2 ≤ a ^ 2 := by norm_num [div_pow] at ha2 ⊢; exact ha2
  have he : 1 / (2 * n ^ 2) = (1 / n ^ 2) / 2 := by ring
  rw [he]
  simp only [div_eq_mul_inv] at hcos hprod ha2' ht2 hh' ⊢
  nlinarith only [hcos, hprod, ha2', ht2, hh']

theorem domain_lens_positive {m : ℕ} (hm : 8 ≤ m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (hdom : InDomain (by omega) θ v) {ξ : ℂ}
    (hξ : ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2)
    (horder : 10 * (logOrder (2 * m) : ℝ) + 1024 ≤ 2 * m) (j : Fin m) :
    0 < 2 * Real.cos (halfAngle (by omega) θ j) ∧
      (heightParameter (coordinates (by omega) v) ξ j) ^ 2 ≤ 4 ∧
      1 / (2 * (2 * m : ℝ) ^ 2) ≤ Lens.width (2 * Real.cos (halfAngle (by omega) θ j))
        (heightParameter (coordinates (by omega) v) ξ j) := by
  have hn : (16 : ℝ) ≤ 2 * m := by exact_mod_cast (show 16 ≤ 2 * m by omega)
  have hn0 : (0 : ℝ) < 2 * m := by linarith
  have hsmall : 10 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2 ≤ 1 / (2 * m) := by
    have he : 1 / (2 * m : ℝ) = (2 * m) / (2 * m) ^ 2 := by field_simp
    rw [he]
    exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
  have hη := (domain_angle_difference (by omega) θ v hdom (halfIndex j)).trans hsmall
  have ha : 2 / (2 * m : ℝ) ≤ halfAngle (by omega) θ j ∧
      halfAngle (by omega) θ j ≤ 5 / (2 * m) := by
    have hlow : (3 : ℝ) / (2 * m) < Real.pi / (2 * m) := div_lt_div_of_pos_right Real.pi_gt_three hn0
    have hhigh : Real.pi / (2 * m) < (4 : ℝ) / (2 * m) := div_lt_div_of_pos_right Real.pi_lt_four hn0
    unfold halfAngle
    simp only [div_eq_mul_inv] at hlow hhigh hη ⊢
    constructor <;> linarith [(abs_le.mp hη).1, (abs_le.mp hη).2]
  have ht := domain_height_bound (by omega) θ v hdom hξ j
  have ht' : |heightParameter (coordinates (by omega) v) ξ j| ≤ 1 / (2 * m) := by
    have hb := div_le_div_of_nonneg_right horder (sq_nonneg (2 * m : ℝ))
    have he : (2 * m : ℝ) / (2 * m) ^ 2 = 1 / (2 * m) := by field_simp
    rw [he] at hb
    exact ht.trans hb
  exact positive_lens_from_sizes hn ha ht'

end
end StructuralNote.CommonFiberBounds
