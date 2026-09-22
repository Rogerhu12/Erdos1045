import Mathlib.Data.Nat.Dist
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

/-! Natural-valued distances and actual forward neighbor sets on `Fin n`. -/

namespace Erdos1045.EventualExact

variable {n : ℕ}

def cyclicForwardDistance (i j : Fin n) : ℕ := (j.val + n - i.val) % n

def cyclicDistance (i j : Fin n) : ℕ :=
  min (cyclicForwardDistance i j) (cyclicForwardDistance j i)

def cyclicAdvance (i : Fin n) (k : ℕ) : Fin n :=
  ⟨(i.val + k) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

@[simp] theorem cyclicAdvance_val (i : Fin n) (k : ℕ) :
    (cyclicAdvance i k).val = (i.val + k) % n := rfl

@[simp] theorem cyclicForwardDistance_self (i : Fin n) : cyclicForwardDistance i i = 0 := by
  simp [cyclicForwardDistance]

theorem cyclicForwardDistance_of_le {i j : Fin n} (h : i.val ≤ j.val) :
    cyclicForwardDistance i j = j.val - i.val := by
  have he : j.val + n - i.val = (j.val - i.val) + n := by omega
  simp [cyclicForwardDistance, he, Nat.mod_eq_of_lt (show j.val - i.val < n by omega)]

theorem cyclicForwardDistance_of_lt {i j : Fin n} (h : j.val < i.val) :
    cyclicForwardDistance i j = n - (i.val - j.val) := by
  rw [cyclicForwardDistance, Nat.mod_eq_of_lt (show j.val + n - i.val < n by omega)]
  omega

theorem cyclicDistance_eq_min_dist (i j : Fin n) :
    cyclicDistance i j = min (Nat.dist i.val j.val) (n - Nat.dist i.val j.val) := by
  by_cases he : i = j
  · subst j
    simp [cyclicDistance, Nat.dist_self]
  · have hne : i.val ≠ j.val := fun h => he (Fin.ext h)
    rcases lt_or_gt_of_ne hne with h | h
    · rw [cyclicDistance, cyclicForwardDistance_of_le h.le,
        cyclicForwardDistance_of_lt h, Nat.dist_eq_sub_of_le h.le]
    · rw [cyclicDistance, cyclicForwardDistance_of_lt h,
        cyclicForwardDistance_of_le h.le, Nat.dist_eq_sub_of_le_right h.le, min_comm]

@[simp] theorem cyclicDistance_self (i : Fin n) : cyclicDistance i i = 0 := by
  simp [cyclicDistance]

theorem cyclicDistance_comm (i j : Fin n) : cyclicDistance i j = cyclicDistance j i :=
  min_comm _ _

theorem cyclicDistance_of_le {i j : Fin n} (h : i.val ≤ j.val) :
    cyclicDistance i j = min (j.val - i.val) (n - (j.val - i.val)) := by
  rw [cyclicDistance_eq_min_dist, Nat.dist_eq_sub_of_le h]

theorem cyclicDistance_pos {i j : Fin n} (h : i ≠ j) : 0 < cyclicDistance i j := by
  have hne : i.val ≠ j.val := fun he => h (Fin.ext he)
  have hd := Nat.dist_pos_of_ne hne
  rw [cyclicDistance_eq_min_dist]
  unfold Nat.dist at *
  omega

theorem two_mul_cyclicDistance_le (i j : Fin n) : 2 * cyclicDistance i j ≤ n := by
  rw [cyclicDistance_eq_min_dist]
  unfold Nat.dist
  omega

theorem cyclicForwardDistance_advance (i : Fin n) {k : ℕ} (hk : k < n) :
    cyclicForwardDistance i (cyclicAdvance i k) = k := by
  by_cases hs : i.val + k < n
  · have he : (i.val + k) % n + n - i.val = n + k := by
      rw [Nat.mod_eq_of_lt hs]
      omega
    simp [cyclicForwardDistance, cyclicAdvance, he, Nat.mod_eq_of_lt hk]
  · have hm : (i.val + k) % n = i.val + k - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (show i.val + k - n < n by omega)]
    have he : (i.val + k) % n + n - i.val = k := by rw [hm]; omega
    simp [cyclicForwardDistance, cyclicAdvance, he, Nat.mod_eq_of_lt hk]

theorem cyclicAdvance_ne_self (i : Fin n) {k : ℕ} (h0 : 0 < k) (hk : k < n) :
    cyclicAdvance i k ≠ i := by
  intro h
  have hd := cyclicForwardDistance_advance i hk
  rw [h, cyclicForwardDistance_self] at hd
  omega

theorem cyclicDistance_advance_le (i : Fin n) {k : ℕ} (hk : k < n) :
    cyclicDistance i (cyclicAdvance i k) ≤ k := by
  exact (min_le_left _ _).trans_eq (cyclicForwardDistance_advance i hk)

def cyclicNeighbors (i : Fin n) (R : ℕ) : Finset (Fin n) :=
  (Finset.Icc 1 R).image (cyclicAdvance i)

theorem cyclicNeighbors_card (i : Fin n) {R : ℕ} (hR : R < n) :
    (cyclicNeighbors i R).card = R := by
  have hinj : Set.InjOn (cyclicAdvance i) (↑(Finset.Icc 1 R) : Set ℕ) := by
    intro k hk l hl hkl
    have hk' := Finset.mem_Icc.mp hk
    have hl' := Finset.mem_Icc.mp hl
    have he := congrArg (cyclicForwardDistance i) hkl
    rwa [cyclicForwardDistance_advance i (by omega),
      cyclicForwardDistance_advance i (by omega)] at he
  rw [cyclicNeighbors, Finset.card_image_of_injOn hinj]
  simp

theorem mem_cyclicNeighbors_ne {i j : Fin n} {R : ℕ} (hR : R < n)
    (hj : j ∈ cyclicNeighbors i R) : j ≠ i := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
  have hk' := Finset.mem_Icc.mp hk
  exact cyclicAdvance_ne_self i (by omega) (by omega)

theorem mem_cyclicNeighbors_distance_le {i j : Fin n} {R : ℕ} (hR : R < n)
    (hj : j ∈ cyclicNeighbors i R) : cyclicDistance i j ≤ R := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
  have hk' := Finset.mem_Icc.mp hk
  exact (cyclicDistance_advance_le i (by omega)).trans hk'.2

end Erdos1045.EventualExact
