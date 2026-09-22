import StructuralNote.FiniteCompressionGap

/-! A quantitative self-interaction gain from a single internal gap. The
kernel hypotheses are restricted to the actual finite interval of distances. -/

namespace StructuralNote.FiniteCompressionGain

open Finset FiniteCompressionGap
open scoped BigOperators
noncomputable section

def rankPairs (ℓ : ℕ) : Finset (ℕ × ℕ) := ((range ℓ) ×ˢ range ℓ).filter (fun p => p.1 < p.2)

def interaction (ℓ : ℕ) (K : ℕ → ℝ) (e : ℕ → ℕ) : ℝ :=
  (ℓ : ℝ) * K 0 + 2 * ∑ p ∈ rankPairs ℓ, K (e p.2 - e p.1)

theorem distance_le_span {ℓ N : ℕ} (hℓ : 0 < ℓ) (e : ℕ → ℕ)
    (he : StrictMonoOn e (Set.Iio ℓ)) (hspan : e (ℓ - 1) - e 0 ≤ N)
    {i j : ℕ} (hi : i < ℓ) (hj : j < ℓ) : e j - e i ≤ N := by
  have hfirst := he.monotoneOn (show 0 ∈ Set.Iio ℓ from hℓ) (show i ∈ Set.Iio ℓ from hi) (Nat.zero_le i)
  have hlast := he.monotoneOn (show j ∈ Set.Iio ℓ from hj)
    (show ℓ - 1 ∈ Set.Iio ℓ by change ℓ - 1 < ℓ; omega) (by omega : j ≤ ℓ - 1)
  omega

theorem gap_self_gain {ℓ a N : ℕ} (ha : a + 1 < ℓ) (e : ℕ → ℕ)
    (he : StrictMonoOn e (Set.Iio ℓ)) (hgap : e a + 2 ≤ e (a + 1))
    (hspan : e (ℓ - 1) - e 0 ≤ N) (K : ℕ → ℝ)
    (hmono : AntitoneOn K (Set.Icc 1 N)) :
    2 * (K 1 - K ℓ) ≤ interaction ℓ K id - interaction ℓ K e := by
  have hℓN : ℓ ≤ N := by
    have hh := gap_spacing e he ha hgap (i := 0) (j := ℓ - 1) (by omega) (by omega) (by omega)
    omega
  have hrank (p : ℕ × ℕ) (hp : p ∈ rankPairs ℓ) :
      0 ≤ K (p.2 - p.1) - K (e p.2 - e p.1) := by
    rcases mem_filter.mp hp with ⟨hp, hij⟩
    rcases mem_product.mp hp with ⟨hi, hj⟩
    have hi' := mem_range.mp hi
    have hj' := mem_range.mp hj
    have hs := rank_spacing e he (by omega : p.1 ≤ p.2) hj'
    have hb := distance_le_span (by omega : 0 < ℓ) e he hspan hi' hj'
    exact sub_nonneg.mpr (hmono ⟨by omega, by omega⟩ ⟨by omega, hb⟩ hs)
  have hcross (p : ℕ × ℕ) (hp : p ∈ crossPairs ℓ a) :
      K (p.2 - p.1) - K (p.2 - p.1 + 1) ≤ K (p.2 - p.1) - K (e p.2 - e p.1) := by
    rcases mem_product.mp hp with ⟨hi, hj⟩
    have hi' := mem_range.mp hi
    have hj' := mem_Ico.mp hj
    have hs := gap_spacing e he ha hgap (by omega : p.1 ≤ a) (by omega : a < p.2) hj'.2
    have hb := distance_le_span (by omega : 0 < ℓ) e he hspan (by omega : p.1 < ℓ) hj'.2
    have hh := hmono (show p.2 - p.1 + 1 ∈ Set.Icc 1 N by constructor <;> omega)
      (show e p.2 - e p.1 ∈ Set.Icc 1 N by constructor <;> omega) hs
    linarith
  have hsub : crossPairs ℓ a ⊆ rankPairs ℓ := by
    intro p hp
    rcases mem_product.mp hp with ⟨hi, hj⟩
    have hi' := mem_range.mp hi
    have hj' := mem_Ico.mp hj
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (by omega), mem_range.mpr hj'.2⟩, by omega⟩
  have hsum := (sum_le_sum hcross).trans
    (sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => hrank p hp))
  have htel := cross_telescoping ha K (hmono.mono (by intro d hd; exact ⟨hd.1, hd.2.trans hℓN⟩))
  have htotal := htel.trans hsum
  unfold interaction
  simp only [id_eq, sum_sub_distrib] at htotal ⊢
  linarith

theorem background_gain {ℓ L R : ℕ} (hℓ : 0 < ℓ) (e : ℕ → ℕ)
    (he : StrictMonoOn e (Set.Iio ℓ)) (hfirst : e 0 = L) (hlast : e (ℓ - 1) ≤ R)
    (b : ℕ → ℝ) (hb : AntitoneOn b (Set.Icc L R)) :
    (∑ j ∈ range ℓ, b (e j)) ≤ ∑ j ∈ range ℓ, b (L + j) := by
  apply sum_le_sum
  intro j hj
  have hj' := mem_range.mp hj
  have hs := rank_spacing e he (Nat.zero_le j) hj'
  have hfirst' := he.monotoneOn (show 0 ∈ Set.Iio ℓ from hℓ)
    (show j ∈ Set.Iio ℓ from hj') (Nat.zero_le j)
  have hlast' := he.monotoneOn (show j ∈ Set.Iio ℓ from hj')
    (show ℓ - 1 ∈ Set.Iio ℓ by change ℓ - 1 < ℓ; omega) (by omega : j ≤ ℓ - 1)
  rw [hfirst] at hs hfirst'
  exact hb ⟨by omega, by omega⟩ ⟨hfirst', hlast'.trans hlast⟩ (by omega)

end
end StructuralNote.FiniteCompressionGain
