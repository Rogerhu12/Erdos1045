import StructuralNote.FiniteCompressionBackground
import StructuralNote.FiniteCompressionConvolutionDifference

/-! Exact decomposition of a half-circle into a background jump and two
uncertain transition arcs, followed by a quantitative actual potential bound. -/

namespace StructuralNote.FiniteCompressionArcPartition

open Finset Erdos1045.EventualExact FourierMultiplier
open FiniteCompressionBackground FiniteCompressionConvolutionBase
open FiniteCompressionConvolutionDifference FiniteCompressionRanked
open scoped BigOperators
noncomputable section

theorem sum_Icc_eq_contribution {L R : ℕ} (hLR : L ≤ R) (φ b : ℕ → ℝ) :
    (∑ s ∈ Icc L R, φ s * (b (s + 1) - b s)) =
      contribution (R - L) (fun t => φ (L + t)) (fun t => b (L + t)) := by
  rw [← Ico_succ_right_eq_Icc, sum_Ico_eq_sum_range]
  have he : R + 1 - L = R - L + 1 := by omega
  change (∑ s ∈ range (R + 1 - L), φ (L + s) * (b (L + s + 1) - b (L + s))) = _
  simp only [he, contribution, Nat.add_assoc]

theorem shifted_ascending_bound {L R : ℕ} (hLR : L ≤ R) (φ b : ℕ → ℝ) {A : ℝ}
    (hφ : MonotoneOn φ (Set.Icc L R)) (hb : ∀ s ∈ Set.Icc L (R + 1), |b s| ≤ A)
    (hleft : b L = -A) (hright : b (R + 1) = A) :
    (∑ s ∈ Icc L R, φ s * (b (s + 1) - b s)) ≤ 2 * A * φ R := by
  rw [sum_Icc_eq_contribution hLR]
  have hh := ascending_arc_bound (R - L) (fun t => φ (L + t)) (fun t => b (L + t))
    (by intro i hi j hj hij; apply hφ <;> simp only [Set.mem_Icc] at * <;> omega)
    (by intro s hs; apply hb; constructor <;> omega)
    (by simpa using hleft) (by simpa only [show L + (R - L + 1) = R + 1 by omega] using hright)
  simpa [Nat.add_sub_of_le hLR] using hh

theorem shifted_descending_bound {L R : ℕ} (hLR : L ≤ R) (φ b : ℕ → ℝ) {A : ℝ}
    (hφ : MonotoneOn φ (Set.Icc L R)) (hb : ∀ s ∈ Set.Icc L (R + 1), |b s| ≤ A)
    (hleft : b L = A) (hright : b (R + 1) = -A) :
    (∑ s ∈ Icc L R, φ s * (b (s + 1) - b s)) ≤ -2 * A * φ L := by
  rw [sum_Icc_eq_contribution hLR]
  have hh := descending_arc_bound (R - L) (fun t => φ (L + t)) (fun t => b (L + t))
    (by intro i hi j hj hij; apply hφ <;> simp only [Set.mem_Icc] at * <;> omega)
    (by intro s hs; apply hb; constructor <;> omega)
    (by simpa using hleft) (by simpa only [show L + (R - L + 1) = R + 1 by omega] using hright)
  simpa using hh

theorem sum_supported_on_three_arcs {a m u L₁ R₁ L₂ R₂ : ℕ} (f : ℕ → ℝ)
    (hau : a ≤ u) (huL : u < L₁) (h₁ : L₁ ≤ R₁) (hgap : R₁ < L₂)
    (h₂ : L₂ ≤ R₂) (hRm : R₂ < a + m)
    (hzero : ∀ s ∈ Ico a (a + m), s ≠ u → s ∉ Icc L₁ R₁ → s ∉ Icc L₂ R₂ → f s = 0) :
    (∑ s ∈ Ico a (a + m), f s) = f u + (∑ s ∈ Icc L₁ R₁, f s) +
      ∑ s ∈ Icc L₂ R₂, f s := by
  let U := insert u (Icc L₁ R₁ ∪ Icc L₂ R₂)
  have hsub : U ⊆ Ico a (a + m) := by
    intro s hs
    simp only [U, mem_insert, mem_union, mem_Icc, mem_Ico] at *
    omega
  have hz : ∀ s ∈ Ico a (a + m), s ∉ U → f s = 0 := by
    intro s hs hn
    simp only [U, mem_insert, mem_union, not_or] at hn
    exact hzero s hs hn.1 hn.2.1 hn.2.2
  have hnot : u ∉ Icc L₁ R₁ ∪ Icc L₂ R₂ := by
    simp only [mem_union, mem_Icc]
    omega
  have hd : Disjoint (Icc L₁ R₁) (Icc L₂ R₂) := by
    apply disjoint_left.mpr
    intro s hs ht
    simp only [mem_Icc] at hs ht
    omega
  rw [← sum_subset hsub hz]
  simp only [U, sum_insert hnot, sum_union hd]
  ring

/-- The actual half-circle convolution has a uniform negative increment even
when either uncertain arc has arbitrarily many internal sign changes. -/
theorem operator_step_le {m : ℕ} (hm : 0 < m) (b : Fin (2 * m) → ℝ)
    (hb : FiniteBox.Antiperiodic hm b) {A δ : ℝ} (hA : 0 ≤ A)
    (hbox : ∀ i, |b i| ≤ A) {j a u L₁ R₁ L₂ R₂ : ℕ}
    (hau : a ≤ u) (huL : u < L₁) (h₁ : L₁ ≤ R₁) (hgap : R₁ < L₂)
    (h₂ : L₂ ≤ R₂) (hRm : R₂ < a + m)
    (hzero : ∀ s ∈ Ico a (a + m), s ≠ u → s ∉ Icc L₁ R₁ → s ∉ Icc L₂ R₂ →
      sequence hm b (s + 1) = sequence hm b s)
    (hu : sequence hm b u = A) (hu' : sequence hm b (u + 1) = -A)
    (hL₁ : sequence hm b L₁ = -A) (hR₁ : sequence hm b (R₁ + 1) = A)
    (hL₂ : sequence hm b L₂ = A) (hR₂ : sequence hm b (R₂ + 1) = -A)
    (hKu : 0 ≤ kernelAt m j u)
    (hK₁ : MonotoneOn (kernelAt m j) (Set.Icc L₁ R₁))
    (hK₂ : MonotoneOn (kernelAt m j) (Set.Icc L₂ R₂))
    (hmargin : kernelAt m j R₁ ≤ -δ) (hKpos : 0 ≤ kernelAt m j L₂) :
    operator (2 * m) b (site hm (j + 1)) - operator (2 * m) b (site hm j) ≤
      -(8 * A * δ / (2 * m : ℕ)) := by
  have hsum := sum_supported_on_three_arcs (incrementContribution hm b j)
    hau huL h₁ hgap h₂ hRm (by
      intro s hs hsu hs₁ hs₂
      simp only [incrementContribution, hzero s hs hsu hs₁ hs₂, sub_self, mul_zero])
  have hfirst : incrementContribution hm b j u ≤ 0 := by
    simp only [incrementContribution, hu, hu']
    exact mul_nonpos_of_nonneg_of_nonpos hKu (by linarith)
  have hasc := shifted_ascending_bound h₁ (kernelAt m j) (sequence hm b) hK₁
    (fun s _ => hbox (site hm s)) hL₁ hR₁
  have hdesc := shifted_descending_bound h₂ (kernelAt m j) (sequence hm b) hK₂
    (fun s _ => hbox (site hm s)) hL₂ hR₂
  have htotal : (∑ s ∈ Ico a (a + m), incrementContribution hm b j s) ≤ -2 * A * δ := by
    rw [hsum]
    have hneg := mul_le_mul_of_nonneg_left hmargin (show 0 ≤ 2 * A by positivity)
    have hnonpos : -2 * A * kernelAt m j L₂ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hKpos
    dsimp only [incrementContribution]
    dsimp only [incrementContribution] at hfirst
    linarith
  rw [operator_difference_half hm b hb j a]
  have hshift : (∑ s ∈ range m, kernelAt m j (a + s) *
      (sequence hm b (a + s + 1) - sequence hm b (a + s))) =
      ∑ s ∈ Ico a (a + m), incrementContribution hm b j s := by
    rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    rfl
  rw [hshift]
  have hmul := mul_le_mul_of_nonneg_left htotal (show 0 ≤ (4 / (2 * m : ℕ) : ℝ) by positivity)
  calc
    _ ≤ (4 / (2 * m : ℕ) : ℝ) * (-2 * A * δ) := hmul
    _ = _ := by ring

end
end StructuralNote.FiniteCompressionArcPartition
