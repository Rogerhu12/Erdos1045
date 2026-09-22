import EventualExact.ExtremalLocalization
import EventualExact.SchurLiftBounds

/-! Actual antipodal centers, half-diameters and the matching-deficit budget. -/

namespace Erdos1045.EventualExact.AntipodalDecomposition

open Complex Configuration FourierMultiplier SchurLift CommonLocalization
open scoped BigOperators
noncomputable section

def evenPart {ι : Type*} (p : ι → ι) (u : ι → ℂ) (j : ι) : ℂ := (u j + u (p j)) / 2

def oddPart {ι : Type*} (p : ι → ι) (u : ι → ℂ) (j : ι) : ℂ := (u j - u (p j)) / 2

theorem parts_add {ι : Type*} (p : ι → ι) (u : ι → ℂ) (j : ι) :
    evenPart p u j + oddPart p u j = u j := by unfold evenPart oddPart; ring

theorem evenPart_invariant {ι : Type*} (p : ι → ι) (hp : Function.Involutive p)
    (u : ι → ℂ) (j : ι) : evenPart p u (p j) = evenPart p u j := by
  simp only [evenPart, hp j]
  ring

theorem oddPart_antiperiodic {ι : Type*} (p : ι → ι) (hp : Function.Involutive p)
    (u : ι → ℂ) (j : ι) : oddPart p u (p j) = -oddPart p u j := by
  simp only [oddPart, hp j]
  ring

theorem oddPart_weighted_sum {ι : Type*} [Fintype ι] (p : ι → ι)
    (hp : Function.Involutive p) (u w : ι → ℂ) (hw : ∀ j, w (p j) = -w j) :
    (∑ j, oddPart p u j * (starRingEnd ℂ) (w j)) = ∑ j, u j * (starRingEnd ℂ) (w j) := by
  have hi : (∑ j, u (p j) * (starRingEnd ℂ) (w j)) =
      ∑ j, u j * (starRingEnd ℂ) (w (p j)) := by
    calc
      _ = ∑ j, u (p j) * (starRingEnd ℂ) (w (p (p j))) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hp j]
      _ = _ := Equiv.sum_comp (Equiv.ofBijective p hp.bijective)
        (fun j => u j * (starRingEnd ℂ) (w (p j)))
  simp only [hw, map_neg, mul_neg, Finset.sum_neg_distrib] at hi
  simp only [oddPart, div_mul_eq_mul_div, sub_mul, ← Finset.sum_div,
    Finset.sum_sub_distrib]
  rw [hi]
  ring

theorem oddPart_affine {ι : Type*} (p : ι → ι) (u w : ι → ℂ)
    (hw : ∀ j, w (p j) = -w j) (α β : ℂ) (j : ι) :
    oddPart p (fun i => α + β * (w i + u i)) j = β * (w j + oddPart p u j) := by
  simp only [oddPart, hw]
  ring

theorem matching_square_sum {ι : Type*} [Fintype ι] (p : ι → ι)
    (hp : Function.Involutive p) (u w : ι → ℂ) (hw : ∀ j, w (p j) = -w j)
    (hunit : ∀ j, normSq (w j) = 1)
    (hsim : (∑ j, u j * (starRingEnd ℂ) (w j)) = 0) (α β : ℂ) :
    (∑ j, normSq (oddPart p (fun i => α + β * (w i + u i)) j)) =
      normSq β * ((Fintype.card ι : ℝ) + ∑ j, normSq (oddPart p u j)) := by
  have ho : (∑ j, oddPart p u j * (starRingEnd ℂ) (w j)) = 0 := by
    rw [oddPart_weighted_sum p hp u w hw, hsim]
  have hre : (∑ j, (oddPart p u j * (starRingEnd ℂ) (w j)).re) = 0 := by
    rw [← Complex.re_sum, ho, zero_re]
  simp only [oddPart_affine p u w hw, normSq_mul, ← Finset.mul_sum]
  congr 1
  simp_rw [add_comm (w _) (oddPart p u _), normSq_add, hunit]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hre]
  simp [add_comm]

theorem matching_norm_le {n : ℕ} (p : Fin n → Fin n) (z : Points n)
    (hz : DiameterAtMost 2 z) (j : Fin n) : ‖oddPart p z j‖ ≤ 1 := by
  have h := hz j (p j)
  unfold oddPart
  rw [norm_div]
  norm_num
  linarith

theorem scale_and_matching_deficit {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ι → ι) (hp : Function.Involutive p) (u w : ι → ℂ)
    (hw : ∀ j, w (p j) = -w j) (hunit : ∀ j, normSq (w j) = 1)
    (hsim : (∑ j, u j * (starRingEnd ℂ) (w j)) = 0) (α β : ℂ)
    (hd : ∀ j, ‖oddPart p (fun i => α + β * (w i + u i)) j‖ ≤ 1) :
    ‖β‖ ≤ 1 ∧
      (Fintype.card ι : ℝ) * (∑ j, (1 - ‖oddPart p (fun i => α + β * (w i + u i)) j‖)) ≤
        (Fintype.card ι : ℝ) ^ 2 * (1 - ‖β‖ ^ 2) := by
  let d := oddPart p (fun i => α + β * (w i + u i))
  have he := matching_square_sum p hp u w hw hunit hsim α β
  have hlow : (Fintype.card ι : ℝ) * ‖β‖ ^ 2 ≤ ∑ j, normSq (d j) := by
    rw [he, normSq_eq_norm_sq]
    have hs : 0 ≤ ∑ j, normSq (oddPart p u j) := Finset.sum_nonneg (fun _ _ => normSq_nonneg _)
    nlinarith [sq_nonneg ‖β‖]
  have hup : (∑ j, normSq (d j)) ≤ (Fintype.card ι : ℝ) := by
    calc
      _ ≤ ∑ _j : ι, (1 : ℝ) := Finset.sum_le_sum fun j _ => by
        rw [normSq_eq_norm_sq]
        have h := hd j
        have h0 := norm_nonneg (d j)
        change ‖d j‖ ≤ 1 at h
        nlinarith
      _ = _ := by simp
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  constructor
  · have hb : ‖β‖ ^ 2 ≤ 1 := le_of_mul_le_mul_left (by simpa using hlow.trans hup) hn
    nlinarith [norm_nonneg β]
  · have hsum : (∑ j, (1 - ‖d j‖)) ≤ (Fintype.card ι : ℝ) - ∑ j, normSq (d j) := by
      calc
        _ ≤ ∑ j, (1 - normSq (d j)) := Finset.sum_le_sum fun j _ => by
          rw [normSq_eq_norm_sq]
          have h := hd j
          have h0 := norm_nonneg (d j)
          change ‖d j‖ ≤ 1 at h
          nlinarith
        _ = _ := by simp [Finset.sum_sub_distrib]
    have hm := mul_le_mul_of_nonneg_left (hsum.trans (sub_le_sub_left hlow _)) hn.le
    change (Fintype.card ι : ℝ) * (∑ j, (1 - ‖d j‖)) ≤ _
    nlinarith

theorem normalized_model_scale_deficit {m : ℕ} (hm : 2 ≤ m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hz : DiameterAtMost 2 z) :
    ‖β‖ ≤ 1 ∧
      (2 * m : ℝ) * (∑ j, (1 - ‖oddPart (halfTurn (by omega)) (z ∘ σ) j‖)) ≤
        (2 * m : ℝ) ^ 2 * (1 - ‖β‖ ^ 2) := by
  let : NeZero (2 * m) := ⟨by omega⟩
  let w : Fin (2 * m) → ℂ := fun j => LocalPhase.regularRoot (2 * m) ^ (j : ℕ)
  have hw (j : Fin (2 * m)) : w (halfTurn (by omega) j) = -w j := by
    simpa only [character, mul_one] using character_halfTurn (by omega : 0 < m) (by decide : Odd 1) j
  have hu (j : Fin (2 * m)) : normSq (w j) = 1 := by
    simp only [w, normSq_eq_norm_sq, norm_pow, LocalChord.root_norm, one_pow]
  have hs : (∑ j : Fin (2 * m), u j * (starRingEnd ℂ) (w j)) = 0 := by
    change (∑ j : Fin (2 * m), u j * (starRingEnd ℂ) (LocalPhase.regularRoot (2 * m) ^ (j : ℕ))) = 0
    rw [Fin.sum_univ_eq_sum_range (fun j => u j * (starRingEnd ℂ) (LocalPhase.regularRoot (2 * m) ^ j)) (2 * m)]
    exact h.similarity_zero
  have he : (z ∘ σ) = (fun j => α + β * (w j + u j)) := funext h.coordinates
  have hd : DiameterAtMost 2 (z ∘ σ) := fun i j => hz (σ i) (σ j)
  have hb := scale_and_matching_deficit (halfTurn (by omega)) (halfTurn_involutive (by omega))
    (fun j : Fin (2 * m) => u j) w hw hu hs α β (by
      rw [← he]
      exact matching_norm_le _ _ hd)
  rw [← he] at hb
  simpa only [Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] using hb

end
end Erdos1045.EventualExact.AntipodalDecomposition
