import StructuralNote.CommonFiberBounds

/-! Quantitative bounds placing every point of the common energy domain in
the rational small-angle chart, uniformly over its constructed closure root. -/

namespace StructuralNote.CommonRationalWindowBounds

open Erdos1045.EventualExact SchurSpectrum LensClosure Filter
open CommonDomainRadius CommonDomainClosure CommonClosureEnergy CommonTangentialParameters CommonFiberBounds
open scoped BigOperators Topology
noncomputable section

theorem eventual_radius_le_small_inverse :
    ∀ᶠ n : ℕ in atTop, energyRadius n ≤ 1 / (1024 * (n : ℝ)) := by
  have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  have ht : Tendsto (fun n : ℕ => 16384 * (Real.log n ^ 2 / (n : ℝ))) atTop (𝓝 0) := by
    simpa only [Real.rpow_two, Real.rpow_one, Function.comp_def, mul_zero] using
      (h.comp tendsto_natCast_atTop_atTop).const_mul 16384
  filter_upwards [ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    eventually_ge_atTop 2] with n hb hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hL := logOrder_le hn
  have hsq : (logOrder n : ℝ) ^ 2 ≤ 16 * Real.log n ^ 2 := by
    have hc := pow_le_pow_left₀ (Nat.cast_nonneg (logOrder n)) hL 2
    nlinarith only [hc]
  have hb' : 16384 * Real.log n ^ 2 < n := by
    have hb' : (16384 * Real.log n ^ 2) / n < 1 := by
      simpa only [mul_div_assoc] using hb
    simpa only [one_mul] using (div_lt_iff₀ hnR).mp hb'
  have htarget : 1024 * (logOrder n : ℝ) ^ 2 ≤ n := by nlinarith
  unfold energyRadius
  apply (div_le_div_iff₀ (sq_pos_of_pos hnR) (by positivity : 0 < 1024 * (n : ℝ))).2
  have he := mul_le_mul_of_nonneg_right htarget hnR.le
  nlinarith only [he]

theorem pointwise_of_tiny_energy {n : ℕ} (hn : 2 ≤ n) (c : Fin n → ℂ)
    (hmean : ∑ j, c j = 0) (hA : pairEnergy (by omega) c ≤ 1 / (1024 * (n : ℝ))) (j : Fin n) :
    ‖c j‖ < 1 / (8 * (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hlog : Real.log n ≤ n := by linarith [Real.log_le_sub_one_of_pos hnR]
  have hsq := DiscreteSobolev.pointwise_sq_le hn c hmean j
  have hB : 12 * Real.log n / (n : ℝ) ^ 2 * pairEnergy (by omega) c ≤
      12 / (1024 * (n : ℝ) ^ 2) := by
    calc
      _ ≤ 12 * Real.log n / (n : ℝ) ^ 2 * (1 / (1024 * (n : ℝ))) :=
        mul_le_mul_of_nonneg_left hA (by positivity)
      _ ≤ 12 * (n : ℝ) / (n : ℝ) ^ 2 * (1 / (1024 * (n : ℝ))) := by gcongr
      _ = _ := by field_simp
  apply (sq_lt_sq₀ (norm_nonneg _) (by positivity)).mp
  apply lt_of_le_of_lt (hsq.trans hB)
  field_simp
  nlinarith [sq_pos_of_pos hnR]

theorem difference_of_tiny_energy {n : ℕ} (hn : 64 ≤ n) (c : Fin n → ℂ)
    (hA : pairEnergy (by omega) c ≤ 1 / (1024 * (n : ℝ))) (j : Fin n) :
    ‖FiniteFourierLift.difference (by omega) c j‖ ≤ 1 / (8 * (n : ℝ)) := by
  have hnR : (64 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hB := (difference_sq_of_energy (by omega) c j).trans
    (mul_le_mul_of_nonneg_left hA (by positivity : 0 ≤ 8 * Real.pi ^ 2))
  have he : 8 * Real.pi ^ 2 * (1 / (1024 * (n : ℝ))) ≤ 1 / 64 := by
    apply (le_of_mul_le_mul_right ?_ (by positivity : 0 < 1024 * (n : ℝ)))
    field_simp
    nlinarith [Real.pi_lt_four, Real.pi_pos]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  apply (le_of_mul_le_mul_left ?_ (sq_pos_of_pos hn0))
  calc
    _ ≤ 1 / 64 := hB.trans he
    _ = (n : ℝ) ^ 2 * (1 / (8 * (n : ℝ))) ^ 2 := by field_simp; norm_num

theorem eventual_domain_chart_bounds :
    ∃ N : ℕ, ∀ (m : ℕ) (hm : N + 4096 ≤ m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → ∀ (ξ : ℂ), ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2 →
      (∀ j, |θ j| < 1 / (8 * (2 * m : ℝ))) ∧
        ∀ j, |heightParameter (coordinates (by omega) v) ξ j| ≤ 1 / (4 * (2 * m : ℝ)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp eventual_radius_le_small_inverse
  refine ⟨N, ?_⟩
  intro m hm θ v hdom ξ hξ
  have hmR : (4096 : ℝ) ≤ m := by exact_mod_cast (show 4096 ≤ m by omega)
  have hn0 : (0 : ℝ) < 2 * m := by positivity
  have hr := hN (2 * m) (show N ≤ 2 * m by omega)
  have hA := domain_energy_bounds (by omega) θ v hdom
  have hθA := hA.1.trans hr
  have hvA := hA.2.trans hr
  constructor
  · intro j
    simpa only [Complex.norm_real, Real.norm_eq_abs, Nat.cast_mul, Nat.cast_ofNat] using
      pointwise_of_tiny_energy (by omega : 2 ≤ 2 * m) (fun j => (θ j : ℂ)) hdom.2.1 hθA j
  · intro j
    have ht := (coordinates_abs_le (by omega) v j).trans
      (difference_of_tiny_energy (by omega : 64 ≤ 2 * m) v hvA (BoxLensLift.halfIndex j))
    simp only [Nat.cast_mul, Nat.cast_ofNat] at ht
    have hc : 1024 / (2 * m : ℝ) ^ 2 ≤ 1 / (8 * (2 * m : ℝ)) := by
      apply (le_of_mul_le_mul_right ?_ (sq_pos_of_pos hn0))
      field_simp
      linarith
    have hs := (abs_add_le (coordinates (by omega) v j) (harmonicFunctional (midpoint m j) ξ)).trans
      (add_le_add ht ((harmonicFunctional_le_norm _ _).trans (hξ.trans hc)))
    change |coordinates (by omega) v j + harmonicFunctional (midpoint m j) ξ| ≤ _
    exact hs.trans_eq (by ring)

end
end StructuralNote.CommonRationalWindowBounds
