import FinitePerimeterDense
import Mathlib.Data.Finset.Sort

namespace ExteriorReduction.Reinhardt
open Set
noncomputable section

/-- A finite family of connected real cells is constant between its right endpoints. -/
theorem interval_covered_by_cell {ι : Type*} [Finite ι]
    (C : ι → Set ℝ) (hc : ∀ i, (C i).OrdConnected)
    (hb : ∀ i, BddAbove (C i)) {a b : ℝ} (hab : a < b)
    (hcover : Ioo a b ⊆ closure (⋃ i, C i))
    (hend : ∀ i, (C i).Nonempty → sSup (C i) ∉ Ioo a b) :
    ∃ i, Ioo a b ⊆ C i := by
  have hh : Ioo a b ⊆ closure (Ioo a b ∩ ⋃ i, C i) := by
    intro t ht
    exact isOpen_Ioo.inter_closure ⟨ht, hcover ht⟩
  have ha : a ∈ closure (Ioo a b ∩ ⋃ i, C i) := by
    have H := closure_mono hh
    rw [closure_Ioo hab.ne, closure_closure] at H
    exact H ⟨le_rfl, hab.le⟩
  rw [inter_iUnion, closure_iUnion_of_finite] at ha
  obtain ⟨i, hi⟩ := mem_iUnion.mp ha
  have hne : (Ioo a b ∩ C i).Nonempty :=
    Set.Nonempty.of_closure ⟨a, hi⟩
  obtain ⟨x, hx, hxi⟩ := hne
  have hin : (C i).Nonempty := ⟨x, hxi⟩
  have has : a < sSup (C i) := hx.1.trans_le (le_csSup (hb i) hxi)
  have hbs : b ≤ sSup (C i) := by
    by_contra h
    exact hend i hin ⟨has, lt_of_not_ge h⟩
  refine ⟨i, fun t ht => ?_⟩
  have hai : a ∈ closure (C i) := closure_mono inter_subset_right hi
  obtain ⟨l, hlt, hli⟩ := (mem_closure_iff.mp hai) (Iio t) isOpen_Iio ht.1
  obtain ⟨r, hri, htr⟩ := exists_lt_of_lt_csSup hin (ht.2.trans_le hbs)
  exact (hc i).out hli hri ⟨hlt.le, htr.le⟩

/-- Any endpoint of an interval covered by closures is the right endpoint of
one of the cells when all cells lie to its left. -/
theorem endpoint_eq_cell_sup {ι : Type*} [Finite ι]
    (C : ι → Set ℝ) {b : ℝ} (hb : ∀ i, ∀ t ∈ C i, t ≤ b)
    (hcover : b ∈ closure (⋃ i, C i)) :
    ∃ i, (C i).Nonempty ∧ sSup (C i) = b := by
  rw [closure_iUnion_of_finite] at hcover
  obtain ⟨i, hi⟩ := mem_iUnion.mp hcover
  have hn : (C i).Nonempty := Set.Nonempty.of_closure ⟨b, hi⟩
  refine ⟨i, hn, le_antisymm (csSup_le hn (hb i)) ?_⟩
  have hsub : C i ⊆ Iic (sSup (C i)) := fun _ ht => le_csSup ⟨b, hb i⟩ ht
  have H := closure_mono hsub hi
  simpa only [closure_Iic, mem_Iic] using H

#print axioms interval_covered_by_cell
#print axioms endpoint_eq_cell_sup
end
end ExteriorReduction.Reinhardt

