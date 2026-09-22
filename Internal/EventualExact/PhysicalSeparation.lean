import Erdos1045.ClosedLevelActual
import Erdos1045.ClosedHolder

/-! Physical point separation, before passing to any angular parameter. -/

namespace Erdos1045.EventualExact.PhysicalSeparation

open ExteriorClassical ExteriorBoundary Configuration
noncomputable section

theorem separated {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (hn : 3 ≤ n)
    (hinj : Function.Injective z) (hfek : Fekete z)
    {C A : ℝ} (hA : 0 < A) (hc : (1 / 2 : ℝ) ≤ d.capacity)
    (henergy : (n : ℝ) * d.energySquared ≤ C) (hlarge : 256 * C ≤ A)
    (i j : Fin n) (hij : i ≠ j) :
    (A / (8 * Real.exp A)) / n ≤ ‖z i - z j‖ := by
  let HL := remainingLevelAnalysis_proved.toClassical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hr : 1 < 1 + A / (n : ℝ) := by linarith [div_pos hA hn0]
  have hh : 0 < A / (4 * (n : ℝ)) := by positivity
  have hH : ∀ u v : ℂ, 1 ≤ ‖u‖ → 1 ≤ ‖v‖ →
      ‖laurent d.coefficient u - laurent d.coefficient v‖ ≤
        4 * Real.sqrt d.energySquared * Real.sqrt ‖u - v‖ := by
    intro u v hu hv
    exact ClosedSeries.laurent_holder_bound d.coefficient d.sobolev u v hu hv
  obtain ⟨p, hpdeg, hpval, hpbound⟩ := HL.interpolation n (by omega) z hinj hfek
  have hsep := d.level_separation (by omega) (by norm_num : (0 : ℝ) ≤ 4)
    hA hc henergy (by norm_num; exact hlarge) hH
  have hder := HL.cauchy_bernstein_walsh n z d HF (1 + A / n) (A / (4 * n))
    hr hh hsep (p i) (hpbound i)
  have hx (k : Fin n) : z k ∈ hull z := subset_convexHull ℝ (Set.range z) (Set.mem_range_self k)
  have hmv := HL.polynomial_mean_value n z (p i)
    (2 * (1 + A / n) ^ (p i).natDegree / (A / (4 * n))) hder
    (z i) (hx i) (z j) (hx j)
  simp [hpval, hij] at hmv
  have hp : (1 + A / (n : ℝ)) ^ (p i).natDegree ≤ Real.exp A :=
    (pow_le_pow_right₀ hr.le (hpdeg i)).trans
      (ExteriorEstimates.radius_power_bound (by omega) hA.le)
  have hconst : 2 * (1 + A / (n : ℝ)) ^ (p i).natDegree / (A / (4 * n)) ≤
      8 * n * Real.exp A / A := by
    have h := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)) hh.le
    convert h using 1 <;> first | rfl | (field_simp; ring)
  have hCauchy := hmv.trans (mul_le_mul_of_nonneg_right hconst (norm_nonneg _))
  have hm := mul_le_mul_of_nonneg_right hCauchy hA.le
  have heq : (8 * (n : ℝ) * Real.exp A / A * ‖z i - z j‖) * A =
      ‖z i - z j‖ * n * (8 * Real.exp A) := by field_simp
  rw [one_mul, heq] at hm
  apply (div_le_iff₀ hn0).mpr
  exact (div_le_iff₀ (by positivity : 0 < 8 * Real.exp A)).mpr hm

theorem exists_uniform_constant {N : ℕ → ℕ} {z : ∀ k, Points (N k)}
    (d : ∀ k, ExteriorData (z k)) (HF : ∀ k, FaberIdentities (d k))
    (hN : ∀ k, 3 ≤ N k) (hinj : ∀ k, Function.Injective (z k))
    (hfek : ∀ k, Fekete (z k)) {C : ℝ}
    (hc : ∀ k, (1 / 2 : ℝ) ≤ (d k).capacity)
    (henergy : ∀ k, (N k : ℝ) * (d k).energySquared ≤ C) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ k (i j : Fin (N k)), i ≠ j →
      γ / N k ≤ ‖z k i - z k j‖ := by
  let A : ℝ := max 1 (256 * C)
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨A / (8 * Real.exp A), by positivity, ?_⟩
  intro k i j hij
  exact separated (d k) (HF k) (hN k) (hinj k) (hfek k) hA (hc k)
    (henergy k) (le_max_right _ _) i j hij

end
end Erdos1045.EventualExact.PhysicalSeparation
