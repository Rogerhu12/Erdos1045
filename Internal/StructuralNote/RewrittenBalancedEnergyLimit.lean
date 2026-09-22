import StructuralNote.RewrittenBalancedEnergyPartial
import StructuralNote.FiniteWordClassification

/-! The actual finite-box maximum converges to an explicit summable series.
The proof uses exact finite coefficients and a uniform spectral tail. -/

namespace StructuralNote.RewrittenBalancedEnergyLimit

open Real Filter Erdos1045.EventualExact FourierMultiplier FiniteBox
open RewrittenBalancedCoefficientLimit RewrittenBalancedEnergyPartial
open ThreeBlockBalancedMaximum SolThreeBlockEnergy
open scoped BigOperators Topology
noncomputable section

def limitEnergy : ℝ := ∑' k, limitTerm k

theorem limitTerm_summable : Summable limitTerm :=
  summable_of_sum_range_le limitTerm_nonneg limitPartial_le

theorem limitPartial_tendsto : Tendsto limitPartial atTop (𝓝 limitEnergy) :=
  limitTerm_summable.hasSum.tendsto_sum_nat

theorem finiteEnergy_tendsto : Tendsto finiteEnergy atTop (𝓝 limitEnergy) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have ht : Tendsto (fun P : ℕ => 16 / ((P : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 16
  have hs : Tendsto (fun P => |limitPartial P - limitEnergy|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using (limitPartial_tendsto.sub_const limitEnergy).abs
  obtain ⟨P, hPt, hPs⟩ := ((ht.eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 3))).and
      (hs.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 3)))).exists
  have hf : Tendsto (fun m => |finitePartial m P - limitPartial P|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using
      ((finitePartial_tendsto P).sub_const (limitPartial P)).abs
  obtain ⟨M, hM⟩ := eventually_atTop.1
    (hf.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 3)))
  refine ⟨max M (2 * P + 3), ?_⟩
  intro m hm
  have hpart := hM m (by omega)
  have htail := finitePartial_tail (P := P) (by omega : 3 ≤ m) (by omega)
  have htail' : finiteEnergy m - finitePartial m P < ε / 3 := by
    apply htail.2.trans_lt
    apply lt_of_le_of_lt _ hPt
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (by have := Nat.cast_nonneg (α := ℝ) P; linarith)
  rw [Real.dist_eq]
  have h1 := abs_lt.mp hpart
  have h2 := abs_lt.mp hPs
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

theorem eventual_B_eq_finiteEnergy : ∀ᶠ m : ℕ in atTop, ∀ hm : 0 < m,
    B hm = finiteEnergy m := by
  filter_upwards [FiniteWordClassification.eventually_B_eq_balancedEnergy,
    eventually_ge_atTop 3] with m hB hm3 hm
  rw [hB hm3]
  simp only [finiteEnergy, balancedVertex, dif_pos hm3,
    balancedEnergy, actualThreeBlockEnergy]

/-- Totalized only at the irrelevant index zero. -/
def boxMaximum (m : ℕ) : ℝ := if hm : 0 < m then B hm else 0

theorem boxMaximum_tendsto : Tendsto boxMaximum atTop (𝓝 limitEnergy) := by
  apply finiteEnergy_tendsto.congr'
  filter_upwards [eventual_B_eq_finiteEnergy, eventually_gt_atTop 0] with m hB hm
  exact (hB hm).symm.trans (by simp only [boxMaximum, dif_pos hm])

end
end StructuralNote.RewrittenBalancedEnergyLimit
