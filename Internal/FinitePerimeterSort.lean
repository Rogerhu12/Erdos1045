import FinitePerimeterIntervals

namespace ExteriorReduction.Reinhardt
open Set
noncomputable section

/-- Sort a bounded endpoint set and repeat its last value to obtain exactly
`n` intervals, allowing zero lengths. -/
theorem finite_endpoint_partition {n : ℕ} {a b : ℝ} (hab : a < b)
    (s : Finset ℝ) (hs : ∀ x ∈ s, x ∈ Ioc a b) (hb : b ∈ s)
    (hcard : s.card ≤ n) :
    ∃ p : ℕ → ℝ, p 0 = a ∧ p n = b ∧ Monotone p ∧
      (∀ k, p k ∈ Icc a b) ∧
      ∀ k, ∀ x ∈ s, x ∉ Ioo (p k) (p (k + 1)) := by
  classical
  let S := insert a s
  have hS : ∀ x ∈ S, x ∈ Icc a b := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨le_rfl, hab.le⟩
    · exact ⟨(hs x hx).1.le, (hs x hx).2⟩
  have haS : a ∈ S := Finset.mem_insert_self _ _
  have hbS : b ∈ S := Finset.mem_insert_of_mem hb
  have hm : 0 < S.card := Finset.card_pos.mpr ⟨a, haS⟩
  have hmn : S.card - 1 ≤ n := by
    have hh : S.card ≤ s.card + 1 := Finset.card_insert_le _ _
    omega
  let e := S.orderIsoOfFin rfl
  let idx (k : ℕ) : Fin S.card :=
    ⟨min k (S.card - 1), lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)⟩
  let p (k : ℕ) : ℝ := e (idx k)
  have hpS (k : ℕ) : p k ∈ S := (e (idx k)).2
  have hpmono : Monotone p := by
    intro k l hkl
    exact e.monotone (show idx k ≤ idx l from min_le_min_right _ hkl)
  have hp0 : p 0 = a := by
    apply le_antisymm _ (hS _ (hpS 0)).1
    have hh : idx 0 ≤ e.symm ⟨a, haS⟩ := by
      change min 0 (S.card - 1) ≤ _
      simp
    have he := e.monotone hh
    change (e _ : ℝ) ≤ (e _ : ℝ) at he
    simpa [p] using he
  have hpn : p n = b := by
    apply le_antisymm (hS _ (hpS n)).2
    have hh : e.symm ⟨b, hbS⟩ ≤ idx n := by
      change (e.symm ⟨b, hbS⟩).val ≤ min n (S.card - 1)
      rw [Nat.min_eq_right hmn]
      exact Nat.le_pred_of_lt (e.symm ⟨b, hbS⟩).isLt
    have he := e.monotone hh
    change (e _ : ℝ) ≤ (e _ : ℝ) at he
    simpa [p] using he
  refine ⟨p, hp0, hpn, hpmono, fun k => hS _ (hpS k), ?_⟩
  intro k x hx hgap
  let j := e.symm ⟨x, Finset.mem_insert_of_mem hx⟩
  have hleft : idx k < j := by
    apply e.lt_iff_lt.mp
    change (e (idx k) : ℝ) < (e j : ℝ)
    simpa [p, j] using hgap.1
  have hright : j < idx (k + 1) := by
    apply e.lt_iff_lt.mp
    change (e j : ℝ) < (e (idx (k + 1)) : ℝ)
    simpa [p, j] using hgap.2
  have h1 : min k (S.card - 1) < j.val := hleft
  have h2 : j.val < min (k + 1) (S.card - 1) := hright
  omega

#print axioms finite_endpoint_partition
end
end ExteriorReduction.Reinhardt


