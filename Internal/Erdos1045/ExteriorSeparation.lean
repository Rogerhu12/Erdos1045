import Erdos1045.ExteriorClassical
import Erdos1045.DirectBoundary
import Erdos1045.ExteriorEstimates

/-! # From the initial energy bound to uniform conformal angle separation

The inputs below are generic Fekete interpolation, the Cauchy estimate on
an exterior level curve combined with Bernstein--Walsh, and the mean value
inequality. All choices of radii and constants, the absorption of the
Laurent error, and the final `γ/n` separation are proved in this file.
-/

namespace Erdos1045.ExteriorClassical

open scoped BigOperators
open ExteriorBoundary Configuration
noncomputable section

structure ClassicalLevelAnalysis : Prop where
  interpolation : ∀ n, 2 ≤ n → ∀ z : Points n, Function.Injective z → Fekete z →
    ∃ p : Fin n → Polynomial ℂ,
      (∀ i, (p i).natDegree ≤ n - 1) ∧
      (∀ i j, (p i).eval (z j) = if i = j then 1 else 0) ∧
      ∀ i x, x ∈ hull z → ‖(p i).eval x‖ ≤ 1
  cauchy_bernstein_walsh : ∀ n (z : Points n) (d : ExteriorData z),
    FaberIdentities d → ∀ r h : ℝ, 1 < r → 0 < h →
    (∀ u v : ℂ, ‖u‖ = r → ‖v‖ = 1 → h ≤ ‖d.map u - d.map v‖) →
    ∀ p : Polynomial ℂ, (∀ x ∈ hull z, ‖p.eval x‖ ≤ 1) →
      ∀ x ∈ hull z, ‖p.derivative.eval x‖ ≤ 2 * r ^ p.natDegree / h
  polynomial_mean_value : ∀ n (z : Points n) (p : Polynomial ℂ) (B : ℝ),
    (∀ x ∈ hull z, ‖p.derivative.eval x‖ ≤ B) →
      ∀ x ∈ hull z, ∀ y ∈ hull z, ‖p.eval x - p.eval y‖ ≤ B * ‖x - y‖

theorem ExteriorData.map_difference_lower {n : ℕ} {z : Points n} (d : ExteriorData z)
    {H : ℝ} (hH : ∀ u v : ℂ, 1 ≤ ‖u‖ → 1 ≤ ‖v‖ →
      ‖laurent d.coefficient u - laurent d.coefficient v‖ ≤
        H * Real.sqrt d.energySquared * Real.sqrt ‖u - v‖)
    {u v : ℂ} (hu : 1 ≤ ‖u‖) (hv : 1 ≤ ‖v‖) :
    d.capacity * ‖u - v‖ - H * Real.sqrt d.energySquared * Real.sqrt ‖u - v‖ ≤
      ‖d.map u - d.map v‖ := by
  have heq : (d.capacity : ℂ) * (u - v) =
      (d.map u - d.map v) - (laurent d.coefficient u - laurent d.coefficient v) := by
    unfold ExteriorData.map
    ring
  have h := norm_sub_le (d.map u - d.map v)
    (laurent d.coefficient u - laurent d.coefficient v)
  rw [← heq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos d.capacity_pos] at h
  linarith [hH u v hu hv]

theorem ExteriorData.level_separation {n : ℕ} {z : Points n} (d : ExteriorData z)
    (hn : 0 < n) {H C A : ℝ} (hH0 : 0 ≤ H) (hA : 0 < A)
    (hc : (1 / 2 : ℝ) ≤ d.capacity)
    (henergy : (n : ℝ) * d.energySquared ≤ C) (hlarge : 16 * H ^ 2 * C ≤ A)
    (hH : ∀ u v : ℂ, 1 ≤ ‖u‖ → 1 ≤ ‖v‖ →
      ‖laurent d.coefficient u - laurent d.coefficient v‖ ≤
        H * Real.sqrt d.energySquared * Real.sqrt ‖u - v‖) :
    ∀ u v : ℂ, ‖u‖ = 1 + A / n → ‖v‖ = 1 →
      A / (4 * n) ≤ ‖d.map u - d.map v‖ := by
  intro u v hu hv
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hfar : A / (n : ℝ) ≤ ‖u - v‖ := by
    have h := norm_sub_norm_le u v
    rw [hu, hv] at h
    linarith
  have hu1 : 1 ≤ ‖u‖ := by rw [hu]; linarith [div_pos hA hn0]
  apply ExteriorEstimates.map_separation hn0 hH0
    (Real.sqrt_nonneg d.energySquared) (norm_nonneg (u - v))
    hc (E := Real.sqrt d.energySquared) (C := C)
  · simpa only [Real.sq_sqrt d.energySquared_nonneg] using henergy
  · exact hlarge
  · exact hfar
  · exact d.map_difference_lower hH hu1 hv.ge

theorem ExteriorData.node_lipschitz {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (i j : Fin n) :
    ‖z i - z j‖ ≤ 4 * min |d.angles.angle i - d.angles.angle j|
      (2 * Real.pi - |d.angles.angle i - d.angles.angle j|) := by
  let g : ℝ := min |d.angles.angle i - d.angles.angle j|
    (2 * Real.pi - |d.angles.angle i - d.angles.angle j|)
  have hgap : |d.angles.angle i - d.angles.angle j| ≤ 2 * Real.pi := by
    apply abs_le.mpr
    constructor <;> linarith [(d.angle_range i).1, (d.angle_range i).2,
      (d.angle_range j).1, (d.angle_range j).2]
  have hg : 0 ≤ g := le_min (abs_nonneg _) (by linarith)
  have h := d.boundary_short_arc_bound HF _ _ hgap
  have heq (k : Fin n) : d.map (unit (d.angles.angle k)) = z k := (d.node_identity k).symm
  rw [heq i, heq j] at h
  have hb := mul_le_mul_of_nonneg_right d.capacity_le_one (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hg)
  dsimp only [g] at hb
  nlinarith

/-- The separation constant is uniform in the dimension and in the extremizer. -/
theorem ExteriorData.separated {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (HL : ClassicalLevelAnalysis) (hn : 3 ≤ n)
    (hinj : Function.Injective z) (hfek : Fekete z)
    {H C A : ℝ} (hH0 : 0 ≤ H) (hA : 0 < A)
    (hc : (1 / 2 : ℝ) ≤ d.capacity)
    (henergy : (n : ℝ) * d.energySquared ≤ C) (hlarge : 16 * H ^ 2 * C ≤ A)
    (hH : ∀ u v : ℂ, 1 ≤ ‖u‖ → 1 ≤ ‖v‖ →
      ‖laurent d.coefficient u - laurent d.coefficient v‖ ≤
        H * Real.sqrt d.energySquared * Real.sqrt ‖u - v‖) :
    FaberFourier.Separated (fun i : Fin n => d.angles.angle i)
      (A / (32 * Real.exp A)) := by
  refine ⟨d.angle_range, ?_⟩
  intro i j hij
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hr : 1 < 1 + A / (n : ℝ) := by linarith [div_pos hA hn0]
  have hh : 0 < A / (4 * (n : ℝ)) := by positivity
  obtain ⟨p, hpdeg, hpval, hpbound⟩ := HL.interpolation n (by omega) z hinj hfek
  have hsep := d.level_separation (by omega) hH0 hA hc henergy hlarge hH
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
  exact ExteriorEstimates.angle_separation hn0 hA hCauchy (d.node_lipschitz HF i j)

end
end Erdos1045.ExteriorClassical
