import StructuralNote.DiscreteConvexBalance

namespace StructuralNote.SolUnitTransfer

open Set DiscreteConvexBalance
noncomputable section

/-- Moving one unit from a longer coordinate to a shorter one gains at least
`2κ` in the manuscript's normalized three-block value. -/
theorem one_unit_transfer {C κ : ℝ} {f : ℤ → ℝ} {l u ri rj rk : ℤ}
    (hκ : 0 ≤ κ) (hconv : ∀ x, l < x → x < u → κ ≤ secondDifference f x)
    (hi : ri ∈ Icc l u) (hj : rj ∈ Icc l u) (_hk : rk ∈ Icc l u)
    (hgap : rj + 2 ≤ ri) :
    rj + 1 ∈ Icc l u ∧ ri - 1 ∈ Icc l u ∧
      ri + rj + rk = (ri - 1) + (rj + 1) + rk ∧
      2 * κ ≤ threeBlockValue C f (ri - 1) (rj + 1) rk - threeBlockValue C f ri rj rk := by
  simp only [Set.mem_Icc] at hi hj _hk
  have hj' : rj + 1 ∈ Icc l u := ⟨by omega, by omega⟩
  have hi' : ri - 1 ∈ Icc l u := ⟨by omega, by omega⟩
  refine ⟨hj', hi', by ring, ?_⟩
  dsimp only [threeBlockValue]
  have hd : κ ≤ firstDifference f (ri - 1) - firstDifference f rj := by
    have hc := hconv (rj + 1) (by omega) (by omega)
    have hm := firstDifference_monotoneOn
      (fun x hx hx' => (hconv x hx hx').trans' hκ)
    have hmono : firstDifference f (rj + 1) ≤ firstDifference f (ri - 1) :=
      hm ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
    simp only [secondDifference, firstDifference,
      show rj + 1 - 1 = rj by omega] at hc hmono ⊢
    linarith
  dsimp only [firstDifference] at hd
  rw [show ri - 1 + 1 = ri by omega] at hd
  nlinarith only [hd]

end
end StructuralNote.SolUnitTransfer
