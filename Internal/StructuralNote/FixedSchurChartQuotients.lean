import StructuralNote.FixedSchurChartSizes
import StructuralNote.CommonFiberRelativeRemainderGeometry

/-! The scalar remainder arguments are small for the actual fixed-Schur chart. -/

namespace StructuralNote.FixedSchurChartQuotients

open Complex Filter Erdos1045 Erdos1045.EventualExact
open CommonDomainClosure CommonDomainRadius FixedSchurChart FixedSchurLinear
open CommonFiberGeometry GeometricRelativeRemainder SignedPressureAngular
open CommonFiberHessianGeometryChord CommonFiberHessianGeometryEnergy
open CommonFiberRelativeRemainderGeometry
open scoped Topology

noncomputable section

theorem domain_center_quotient {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (hdom : InDomain (by omega) θ v) (q : Fin (2 * m) → ℝ) (hq : ‖q‖ ≤ 5)
    (p : Fin (2 * m) × Fin (2 * m)) :
    ‖quotient (FixedSchurLinear.center q v) (root (2 * m)) p‖ ≤
      36 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) := by
  have h := quotient_of_step (show 0 < 2 * m by omega) (FixedSchurLinear.center q v)
    (by positivity) (FixedSchurChartSizes.center_step_bound hm θ v hdom q hq) p.1 p.2
  simp only [Nat.cast_mul, Nat.cast_ofNat] at h
  convert h using 1
  field_simp
  ring

theorem eventual_quotient_properties : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      Function.Injective (diameterVector θ) ∧
      (∀ p, ‖quotient (FixedSchurLinear.center (coordinate (by omega) s θ v) v)
          (root (2 * m)) p‖ ≤ 1 / 4) ∧
      (∀ p, ‖quotient (diameterVector θ - root (2 * m)) (root (2 * m)) p‖ ≤ 1 / 4) ∧
      (∀ p, ‖quotient (FixedSchurLinear.center (coordinate (by omega) s θ v) v)
          (diameterVector θ) p‖ ≤ 1 / 2) := by
  have hnat : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 2 * m) tendsto_id
  have hlim : Tendsto
      (fun m : ℕ => (logOrder (2 * m) : ℝ) / (2 * m : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv]
      using (HessianErrorLimits.logOrder_div_tendsto.comp hnat)
  filter_upwards [eventual_coordinate_properties,
    hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 144 by norm_num))] with m hp hsmall
  intro hm s θ v hdom
  have hratio : 36 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ≤ 1 / 4 := by
    rw [mul_div_assoc]
    linarith
  have hangle : 11 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ≤ 1 / 4 := by
    rw [mul_div_assoc]
    linarith
  have ha (p : Fin (2 * m) × Fin (2 * m)) :
      ‖quotient (angularError θ) (root (2 * m)) p‖ ≤ 1 / 4 :=
    (domain_angularError_ratio (by omega) θ v hdom p.1 p.2).trans hangle
  have hc (p : Fin (2 * m) × Fin (2 * m)) :
      ‖quotient (FixedSchurLinear.center (coordinate (by omega) s θ v) v)
          (root (2 * m)) p‖ ≤ 1 / 4 :=
    (domain_center_quotient hm θ v hdom _ (hp hm s θ v hdom).norm_le p).trans hratio
  refine ⟨domain_diameter_injective hm θ v hdom (by linarith), hc, ha, ?_⟩
  intro p
  have h := quotient_true_le θ (FixedSchurLinear.center (coordinate (by omega) s θ v) v)
    (HessianAngularReference.root_injective (by omega))
    (fun i j => (ha (i, j)).trans (by norm_num)) p
  linarith [hc p]

end
end StructuralNote.FixedSchurChartQuotients
