import StructuralNote.FiniteCompressionRanked

/-! One-pass rigidity for the actual finite Schur box energy. Only local
kernel and background monotonicity remain to be supplied by the arc geometry. -/

namespace StructuralNote.FiniteCompressionActual

open Erdos1045.EventualExact FourierMultiplier
open FiniteCompressionEnergy FiniteCompressionRanked FiniteCompressionOnePass
open FiniteCompressionGap
open scoped BigOperators
noncomputable section

theorem prefix_of_near_max {m ℓ L R N : ℕ} (hm : 0 < m) (hR : R < 2 * m)
    {A C₀ : ℝ} (hA : 0 ≤ A) (e : ℕ → ℕ)
    (he : StrictMonoOn e (Set.Iio ℓ)) (hfirst : e 0 = L) (hlast : e (ℓ - 1) ≤ R)
    (hspan : e (ℓ - 1) - e 0 ≤ N) (b : Fin (2 * m) → ℝ)
    (hb : b ∈ FiniteBox.box hm A)
    (hbase : ∀ k ∈ Set.Icc L R, b (site hm k) = -A)
    (hK : AntitoneOn (gridKernel (2 * m)) (Set.Icc 1 N))
    (hbackground : AntitoneOn (fun k => operator (2 * m) b (site hm k)) (Set.Icc L R))
    (hdeficit : FiniteBox.maximum hm A -
      normalizedBoxEnergy (operator (2 * m)) (b + patch hm A (sites hm ℓ e)) ≤
        C₀ / (2 * m : ℝ) ^ 2)
    (hgain : C₀ < 32 * A ^ 2 * (gridKernel (2 * m) 1 - gridKernel (2 * m) ℓ)) :
    ∀ j < ℓ, e j = L + j := by
  have hbounds (j : ℕ) (hj : j < ℓ) : L + j ≤ e j ∧ e j ≤ R := by
    have hrank := rank_spacing e he (Nat.zero_le j) hj
    have hleft := he.monotoneOn (show 0 ∈ Set.Iio ℓ by exact Nat.zero_lt_of_lt hj)
      (show j ∈ Set.Iio ℓ from hj) (Nat.zero_le j)
    have hright := he.monotoneOn (show j ∈ Set.Iio ℓ from hj)
      (show ℓ - 1 ∈ Set.Iio ℓ by change ℓ - 1 < ℓ; omega) (by omega : j ≤ ℓ - 1)
    rw [hfirst] at hrank hleft
    constructor <;> omega
  have he_bound (j : ℕ) (hj : j < ℓ) : e j < 2 * m := (hbounds j hj).2.trans_lt hR
  have hp_bound (j : ℕ) (hj : j < ℓ) : L + j < 2 * m :=
    (hbounds j hj).1.trans_lt (he_bound j hj)
  have hp_mono : StrictMonoOn (fun j => L + j) (Set.Iio ℓ) := by
    intro i _ j _ hij
    change L + i < L + j
    omega
  have hpbox := add_patch_mem_box hm A (sites hm ℓ (fun j => L + j)) b hb (by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    apply hbase
    exact ⟨Nat.le_add_right L j, (hbounds j (Finset.mem_range.mp hj)).1.trans
      (hbounds j (Finset.mem_range.mp hj)).2⟩)
  have hmax := FiniteBox.energy_le_maximum hm _ hpbox.2
  rw [energy_eq_score hm A _ hp_mono hp_bound b] at hmax
  have hdef := hdeficit
  rw [energy_eq_score hm A e he he_bound b] at hdef
  have hn : 0 < (2 * m : ℝ) := by positivity
  apply prefix_of_small_deficit e he hfirst hlast hspan _ _ hK hbackground
    (show 0 ≤ 4 * A / (2 * m : ℝ) by positivity)
    (show 0 ≤ 16 * A ^ 2 / (2 * m : ℝ) ^ 2 by positivity)
    (B := FiniteBox.maximum hm A - normalizedBoxEnergy (operator (2 * m)) b)
    (ε := C₀ / (2 * m : ℝ) ^ 2)
  · linarith
  · linarith
  · have h := div_lt_div_of_pos_right hgain (sq_pos_of_pos hn)
    calc
      _ < (32 * A ^ 2 * (gridKernel (2 * m) 1 - gridKernel (2 * m) ℓ)) /
          (2 * m : ℝ) ^ 2 := h
      _ = _ := by ring

end
end StructuralNote.FiniteCompressionActual
