import StructuralNote.IntegerBalance
import Mathlib.Algebra.Order.SuccPred

/-! Local discrete strong convexity gives the fixed-sum balancing gap in (8.25). -/

namespace StructuralNote.DiscreteConvexBalance

open Set IntegerBalance
noncomputable section

def firstDifference (f : ℤ → ℝ) (j : ℤ) : ℝ := f (j + 1) - f j

def secondDifference (f : ℤ → ℝ) (j : ℤ) : ℝ := f (j + 1) - 2 * f j + f (j - 1)

theorem firstDifference_monotoneOn {f : ℤ → ℝ} {l u : ℤ}
    (hconv : ∀ j, l < j → j < u → 0 ≤ secondDifference f j) :
    MonotoneOn (firstDifference f) (Icc l (u - 1)) := by
  apply monotoneOn_of_le_add_one ordConnected_Icc
  intro j _ hj hj1
  simp only [mem_Icc] at hj hj1
  have hh := hconv (j + 1) (by omega) (by omega)
  simp only [secondDifference, show j + 1 - 1 = j by omega] at hh
  dsimp only [firstDifference]
  linarith

/-- A support line at the integer cut `k,k+1`, proved only on the supplied interval. -/
theorem discrete_support_line {f : ℤ → ℝ} {l u k x : ℤ}
    (hconv : ∀ j, l < j → j < u → 0 ≤ secondDifference f j)
    (hkl : l ≤ k) (hku : k + 1 ≤ u) (hx : x ∈ Icc l u) :
    f k + firstDifference f k * ((x : ℝ) - k) ≤ f x := by
  let q : ℤ → ℝ := fun j => f j - firstDifference f k * (j : ℝ)
  have hd := firstDifference_monotoneOn hconv
  have hleft : AntitoneOn q (Icc l k) := by
    apply antitoneOn_of_add_one_le ordConnected_Icc
    intro j _ hj hj1
    simp only [mem_Icc] at hj hj1
    have hh := hd ⟨hj.1, by omega⟩ ⟨hkl, by omega⟩ (by omega)
    dsimp only [q, firstDifference] at hh ⊢
    simp only [Int.cast_add, Int.cast_one]
    nlinarith only [hh]
  have hright : MonotoneOn q (Icc k u) := by
    apply monotoneOn_of_le_add_one ordConnected_Icc
    intro j _ hj hj1
    simp only [mem_Icc] at hj hj1
    have hh := hd ⟨hkl, by omega⟩ ⟨by omega, by omega⟩ hj.1
    dsimp only [q, firstDifference] at hh ⊢
    simp only [Int.cast_add, Int.cast_one]
    nlinarith only [hh]
  have hh : q k ≤ q x := by
    rcases le_total x k with h | h
    · exact hleft ⟨hx.1, h⟩ ⟨hkl, le_rfl⟩ h
    · exact hright ⟨le_rfl, by omega⟩ ⟨h, hx.2⟩ h
  dsimp only [q] at hh
  nlinarith only [hh]

theorem balanced_entry_on_support (f : ℤ → ℝ) {k b : ℤ} (hb : b = k ∨ b = k + 1) :
    f b = f k + firstDifference f k * ((b : ℝ) - k) := by
  rcases hb with rfl | rfl
  · simp
  · simp only [firstDifference, Int.cast_add, Int.cast_one]
    ring

theorem three_point_convex_minimum {f : ℤ → ℝ} {l u k a b c p q r : ℤ}
    (hconv : ∀ j, l < j → j < u → 0 ≤ secondDifference f j)
    (hkl : l ≤ k) (hku : k + 1 ≤ u)
    (ha : a ∈ Icc l u) (hb : b ∈ Icc l u) (hc : c ∈ Icc l u)
    (hbal : BalancedAt k p q r) (hsum : a + b + c = p + q + r) :
    f p + f q + f r ≤ f a + f b + f c := by
  have hsa := discrete_support_line hconv hkl hku ha
  have hsb := discrete_support_line hconv hkl hku hb
  have hsc := discrete_support_line hconv hkl hku hc
  have hp := balanced_entry_on_support f hbal.1
  have hq := balanced_entry_on_support f hbal.2.1
  have hr := balanced_entry_on_support f hbal.2.2
  have hs : (a : ℝ) + b + c = (p : ℝ) + q + r := by exact_mod_cast hsum
  have hw := congrArg (fun t : ℝ => firstDifference f k * t) hs
  nlinarith only [hsa, hsb, hsc, hp, hq, hr, hw]

def subtractQuadratic (f : ℤ → ℝ) (κ : ℝ) (j : ℤ) : ℝ := f j - κ / 2 * (j : ℝ) ^ 2

theorem secondDifference_subtractQuadratic (f : ℤ → ℝ) (κ : ℝ) (j : ℤ) :
    secondDifference (subtractQuadratic f κ) j = secondDifference f j - κ := by
  simp only [secondDifference, subtractQuadratic, Int.cast_add, Int.cast_sub, Int.cast_one]
  ring

/-- The quantitative comparison uses second differences only inside `(l,u)`, not on all integers. -/
theorem three_point_strong_convex_gap {f : ℤ → ℝ} {κ : ℝ} {l u k a b c p q r : ℤ}
    (hconv : ∀ j, l < j → j < u → κ ≤ secondDifference f j)
    (hkl : l ≤ k) (hku : k + 1 ≤ u)
    (ha : a ∈ Icc l u) (hb : b ∈ Icc l u) (hc : c ∈ Icc l u)
    (hbal : BalancedAt k p q r) (hsum : a + b + c = p + q + r) :
    κ / 2 * (((a : ℝ) ^ 2 + (b : ℝ) ^ 2 + (c : ℝ) ^ 2) -
      ((p : ℝ) ^ 2 + (q : ℝ) ^ 2 + (r : ℝ) ^ 2)) ≤
      (f a + f b + f c) - (f p + f q + f r) := by
  have hg : ∀ j, l < j → j < u → 0 ≤ secondDifference (subtractQuadratic f κ) j := by
    intro j hjl hju
    rw [secondDifference_subtractQuadratic]
    exact sub_nonneg.mpr (hconv j hjl hju)
  have hh := three_point_convex_minimum hg hkl hku ha hb hc hbal hsum
  dsimp only [subtractQuadratic] at hh
  nlinarith only [hh]

/-- The integral square-sum gap from `IntegerBalance` gives a uniform positive price. -/
theorem three_point_nonbalanced_gap {f : ℤ → ℝ} {κ : ℝ} {l u k a b c p q r : ℤ}
    (hκ : 0 ≤ κ) (hconv : ∀ j, l < j → j < u → κ ≤ secondDifference f j)
    (hkl : l ≤ k) (hku : k + 1 ≤ u)
    (ha : a ∈ Icc l u) (hb : b ∈ Icc l u) (hc : c ∈ Icc l u)
    (hbal : BalancedAt k p q r) (hsum : a + b + c = p + q + r)
    (hne : ¬ BalancedAt k a b c) : κ ≤ (f a + f b + f c) - (f p + f q + f r) := by
  have hsa : a + b + c = 3 * k + (p + q + r - 3 * k) := by omega
  have hsb : p + q + r = 3 * k + (p + q + r - 3 * k) := by ring
  have he := (square_sum_eq_minimum_iff hsb).mpr hbal
  have hg := square_sum_gap hsa hne
  have hs : (2 : ℤ) ≤ a ^ 2 + b ^ 2 + c ^ 2 - (p ^ 2 + q ^ 2 + r ^ 2) := by omega
  have hsR : (2 : ℝ) ≤ ((a : ℝ) ^ 2 + (b : ℝ) ^ 2 + (c : ℝ) ^ 2) -
      ((p : ℝ) ^ 2 + (q : ℝ) ^ 2 + (r : ℝ) ^ 2) := by exact_mod_cast hs
  have hm := mul_le_mul_of_nonneg_left hsR (div_nonneg hκ (by norm_num : (0 : ℝ) ≤ 2))
  have hh := three_point_strong_convex_gap hconv hkl hku ha hb hc hbal hsum
  linarith only [hm, hh]

def threeBlockValue (C : ℝ) (f : ℤ → ℝ) (a b c : ℤ) : ℝ := C - 2 * (f a + f b + f c)

/-- The factor two in `V = C - 2 Σ f` gives exactly the coefficient in (8.25). -/
theorem three_block_value_gap {C κ : ℝ} {f : ℤ → ℝ} {l u k a b c p q r : ℤ}
    (hconv : ∀ j, l < j → j < u → κ ≤ secondDifference f j)
    (hkl : l ≤ k) (hku : k + 1 ≤ u)
    (ha : a ∈ Icc l u) (hb : b ∈ Icc l u) (hc : c ∈ Icc l u)
    (hbal : BalancedAt k p q r) (hsum : a + b + c = p + q + r) :
    κ * (((a : ℝ) ^ 2 + (b : ℝ) ^ 2 + (c : ℝ) ^ 2) -
      ((p : ℝ) ^ 2 + (q : ℝ) ^ 2 + (r : ℝ) ^ 2)) ≤
      threeBlockValue C f p q r - threeBlockValue C f a b c := by
  have hh := three_point_strong_convex_gap hconv hkl hku ha hb hc hbal hsum
  dsimp only [threeBlockValue]
  linarith only [hh]

theorem three_block_value_nonbalanced_gap {C κ : ℝ} {f : ℤ → ℝ} {l u k a b c p q r : ℤ}
    (hκ : 0 ≤ κ) (hconv : ∀ j, l < j → j < u → κ ≤ secondDifference f j)
    (hkl : l ≤ k) (hku : k + 1 ≤ u)
    (ha : a ∈ Icc l u) (hb : b ∈ Icc l u) (hc : c ∈ Icc l u)
    (hbal : BalancedAt k p q r) (hsum : a + b + c = p + q + r)
    (hne : ¬ BalancedAt k a b c) :
    2 * κ ≤ threeBlockValue C f p q r - threeBlockValue C f a b c := by
  have hh := three_point_nonbalanced_gap hκ hconv hkl hku ha hb hc hbal hsum hne
  dsimp only [threeBlockValue]
  linarith only [hh]

/-- Taking the center to be one third of the common sum gives the manuscript's `D²`. -/
def imbalanceSquare (center : ℝ) (a b c : ℤ) : ℝ :=
  ((a : ℝ) - center) ^ 2 + ((b : ℝ) - center) ^ 2 + ((c : ℝ) - center) ^ 2

theorem imbalanceSquare_sub_eq (center : ℝ) {a b c p q r : ℤ}
    (hsum : a + b + c = p + q + r) :
    imbalanceSquare center a b c - imbalanceSquare center p q r =
      ((a : ℝ) ^ 2 + (b : ℝ) ^ 2 + (c : ℝ) ^ 2) -
      ((p : ℝ) ^ 2 + (q : ℝ) ^ 2 + (r : ℝ) ^ 2) := by
  have hs : (a : ℝ) + b + c = (p : ℝ) + q + r := by exact_mod_cast hsum
  have hh := congrArg (fun t : ℝ => 2 * center * t) hs
  dsimp only [imbalanceSquare]
  nlinarith only [hh]

/-- The local three-block estimate in exactly the centered-square form of (8.25). -/
theorem three_block_value_imbalance_gap {C κ center : ℝ} {f : ℤ → ℝ}
    {l u k a b c p q r : ℤ}
    (hconv : ∀ j, l < j → j < u → κ ≤ secondDifference f j)
    (hkl : l ≤ k) (hku : k + 1 ≤ u)
    (ha : a ∈ Icc l u) (hb : b ∈ Icc l u) (hc : c ∈ Icc l u)
    (hbal : BalancedAt k p q r) (hsum : a + b + c = p + q + r) :
    κ * (imbalanceSquare center a b c - imbalanceSquare center p q r) ≤
      threeBlockValue C f p q r - threeBlockValue C f a b c := by
  rw [imbalanceSquare_sub_eq center hsum]
  exact three_block_value_gap hconv hkl hku ha hb hc hbal hsum

theorem three_block_value_lt_of_nonbalanced {C κ : ℝ} {f : ℤ → ℝ}
    {l u k a b c p q r : ℤ}
    (hκ : 0 < κ) (hconv : ∀ j, l < j → j < u → κ ≤ secondDifference f j)
    (hkl : l ≤ k) (hku : k + 1 ≤ u)
    (ha : a ∈ Icc l u) (hb : b ∈ Icc l u) (hc : c ∈ Icc l u)
    (hbal : BalancedAt k p q r) (hsum : a + b + c = p + q + r)
    (hne : ¬ BalancedAt k a b c) :
    threeBlockValue C f a b c < threeBlockValue C f p q r := by
  have hh := three_block_value_nonbalanced_gap (C := C) hκ.le hconv hkl hku ha hb hc hbal hsum hne
  linarith only [hh, hκ]

end
end StructuralNote.DiscreteConvexBalance
