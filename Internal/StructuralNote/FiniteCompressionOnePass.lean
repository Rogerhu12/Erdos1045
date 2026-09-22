import StructuralNote.FiniteCompressionGain

/-! Direct rigidity from one compression. A left buffer supplies the anchored
first site; an internal hole then contradicts the allowed energy deficit.
No transport distance or second localization appears. -/

namespace StructuralNote.FiniteCompressionOnePass

open Finset FiniteCompressionGap FiniteCompressionGain
open scoped BigOperators
noncomputable section

def score (ℓ : ℕ) (K b : ℕ → ℝ) (c d : ℝ) (e : ℕ → ℕ) : ℝ :=
  c * (∑ j ∈ range ℓ, b (e j)) + d * interaction ℓ K e

theorem interaction_translate (ℓ L : ℕ) (K : ℕ → ℝ) :
    interaction ℓ K (fun j => L + j) = interaction ℓ K id := by
  simp only [interaction, Nat.add_sub_add_left, id_eq]

theorem one_gap_score_gain {ℓ a L R N : ℕ} (ha : a + 1 < ℓ) (e : ℕ → ℕ)
    (he : StrictMonoOn e (Set.Iio ℓ)) (hfirst : e 0 = L) (hlast : e (ℓ - 1) ≤ R)
    (hgap : e a + 2 ≤ e (a + 1)) (hspan : e (ℓ - 1) - e 0 ≤ N)
    (K b : ℕ → ℝ) (hK : AntitoneOn K (Set.Icc 1 N)) (hb : AntitoneOn b (Set.Icc L R))
    {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) :
    2 * d * (K 1 - K ℓ) ≤ score ℓ K b c d (fun j => L + j) - score ℓ K b c d e := by
  have hs := mul_le_mul_of_nonneg_left (gap_self_gain ha e he hgap hspan K hK) hd
  have hg := mul_le_mul_of_nonneg_left (background_gain (by omega : 0 < ℓ) e he hfirst hlast b hb) hc
  unfold score
  rw [interaction_translate]
  linarith

/-- Once the kernel gain exceeds the permitted deficit, the original positive
sites are already the leftmost interval. -/
theorem prefix_of_small_deficit {ℓ L R N : ℕ} (e : ℕ → ℕ)
    (he : StrictMonoOn e (Set.Iio ℓ)) (hfirst : e 0 = L) (hlast : e (ℓ - 1) ≤ R)
    (hspan : e (ℓ - 1) - e 0 ≤ N) (K b : ℕ → ℝ)
    (hK : AntitoneOn K (Set.Icc 1 N)) (hb : AntitoneOn b (Set.Icc L R))
    {c d B ε : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hmax : score ℓ K b c d (fun j => L + j) ≤ B)
    (hdeficit : B - score ℓ K b c d e ≤ ε)
    (hgain : ε < 2 * d * (K 1 - K ℓ)) : ∀ j < ℓ, e j = L + j := by
  intro j hj
  by_contra hne
  obtain ⟨a, ha, hgap⟩ := exists_internal_gap e he hfirst ⟨j, hj, hne⟩
  have hg := one_gap_score_gain ha e he hfirst hlast hgap hspan K b hK hb hc hd
  linarith

end
end StructuralNote.FiniteCompressionOnePass
