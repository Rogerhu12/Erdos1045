import StructuralNote.ThreeBlockBalancedMaximum
import StructuralNote.FixedDualClassificationMultiplierLimit
import StructuralNote.FixedDualClassificationStepEnergy

/-! Fixed-frequency limits of the actual balanced three-block vertices, using
their exact finite coefficient formula rather than an assumed sampling limit. -/

namespace StructuralNote.RewrittenBalancedCoefficientLimit

open Real Complex Filter Erdos1045.EventualExact FourierMultiplier
open FiniteBox ThreeBlockBalancedMaximum SolThreeBlockEnergy SolThreeBlockWord
open FixedDualClassificationStep FixedDualClassificationMultiplierLimit
open scoped BigOperators Topology
noncomputable section

def balancedVertex (m : ℕ) : Fin (2 * m) → ℝ :=
  if hm : 3 ≤ m then threeBlockVertex (by omega) (canonical_pos hm)
    (canonical_sum m) (amplitude (2 * m)) else 0

def coefficientFormula (m p : ℕ) : ℝ :=
  (2 * amplitude (2 * m) /
    (Real.pi * p * Real.sinc (Real.pi * p / (2 * m)))) ^ 2 *
    (3 - 2 * Real.cos (Real.pi * p * ((m / 3 : ℕ) : ℝ) / m) -
      2 * Real.cos (Real.pi * p * (((m + 1) / 3 : ℕ) : ℝ) / m) -
      2 * Real.cos (Real.pi * p * (((m + 2) / 3 : ℕ) : ℝ) / m))

theorem third_ratio_tendsto (r : ℕ) :
    Tendsto (fun m : ℕ => (((m + r) / 3 : ℕ) : ℝ) / m) atTop (𝓝 (1 / 3 : ℝ)) := by
  have hr : Tendsto (fun m : ℕ => ((m + r) % 3 : ℕ) / (m : ℝ)) atTop (𝓝 0) := by
    apply tendsto_bdd_div_atTop_nhds_zero
      (Filter.Eventually.of_forall (fun m : ℕ => Nat.cast_nonneg ((m + r) % 3)))
      (Filter.Eventually.of_forall (fun m : ℕ => show (((m + r) % 3 : ℕ) : ℝ) ≤ 3 from
        by exact_mod_cast (Nat.mod_lt (m + r) (by norm_num : 0 < 3)).le))
      tendsto_natCast_atTop_atTop
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).add
    (tendsto_const_div_atTop_nhds_zero_nat (r : ℝ))).sub hr
  have hh := h.div_const 3
  norm_num at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have he : 3 * (((m + r) / 3 : ℕ) : ℝ) + ((m + r) % 3 : ℕ) = (m : ℝ) + r := by
    exact_mod_cast Nat.div_add_mod (m + r) 3
  field_simp
  linarith

theorem even_amplitude_tendsto :
    Tendsto (fun m : ℕ => amplitude (2 * m)) atTop (𝓝 (Real.pi / 2)) := by
  apply amplitude_tendsto.comp
  exact tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 2 * m) tendsto_id

theorem coefficientFormula_tendsto {p : ℕ} (hp : p ≠ 0) :
    Tendsto (fun m => coefficientFormula m p) atTop
      (𝓝 ((3 - 6 * Real.cos (Real.pi * p / 3)) / (p : ℝ) ^ 2)) := by
  have hx : Tendsto (fun m : ℕ => Real.pi * p / (2 * m)) atTop (𝓝 0) := by
    convert tendsto_const_div_atTop_nhds_zero_nat (Real.pi * p / 2) using 1
    funext m
    ring
  have hs := continuous_sinc.continuousAt.tendsto.comp hx
  have hden := hs.const_mul (Real.pi * p)
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  have hr := (even_amplitude_tendsto.const_mul 2).div hden (by simpa using mul_ne_zero Real.pi_ne_zero hpR)
  have hc (r : ℕ) : Tendsto (fun m : ℕ =>
      Real.cos (Real.pi * p * (((m + r) / 3 : ℕ) : ℝ) / m)) atTop
      (𝓝 (Real.cos (Real.pi * p / 3))) := by
    have hh := continuous_cos.continuousAt.tendsto.comp
      ((third_ratio_tendsto r).const_mul (Real.pi * p))
    convert hh using 1
    · funext m
      dsimp only [Function.comp_apply]
      congr 1
      ring
    · congr 1
      ring
  have h := (hr.pow 2).mul ((((tendsto_const_nhds (x := (3 : ℝ))).sub
    ((hc 0).const_mul 2)).sub ((hc 1).const_mul 2)).sub ((hc 2).const_mul 2))
  convert h using 1
  · funext m
    simp only [coefficientFormula, Nat.add_zero, Pi.div_apply, Function.comp_apply]
  · simp only [sinc_zero, mul_one]
    field_simp
    ring

theorem actual_coefficient_formula {m : ℕ} (hm : 3 ≤ m)
    (p : Fin (2 * m)) (hp : SchurWeights.Active (2 * m) p) :
    ‖signedMidpointCoefficient (balancedVertex m) p.val‖ ^ 2 =
      coefficientFormula m p.val := by
  rw [signedMidpointCoefficient_nat, ← Complex.normSq_eq_norm_sq,
    midpointCoefficient_normSq]
  rw [balancedVertex, dif_pos hm,
    active_threeBlockCoefficient_normSq (by omega) (canonical_pos hm) (canonical_sum m) p hp]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hpR : (p.val : ℝ) ≠ 0 := by exact_mod_cast (show p.val ≠ 0 by have := hp.2.1; omega)
  have hx : Real.pi * p.val / (2 * m) ≠ 0 := by positivity
  unfold coefficientFormula
  rw [Real.sinc_of_ne_zero hx]
  have hc (r : ℕ) : 2 * Real.pi * (p : ℕ) * (r : ℝ) / (2 * m) =
      Real.pi * p * r / m := by field_simp
  simp_rw [hc]
  field_simp

end
end StructuralNote.RewrittenBalancedCoefficientLimit
