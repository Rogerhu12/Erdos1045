import OrderedBoundaryAngles
import Mathlib.Topology.Order.IntermediateValue

/-! Ordered finite preimages of a continuous lift with one full turn of drift.
Monotonicity of the lift is not assumed. -/

namespace Erdos1045.EventualExact.PhysicalBoundaryOrder

open Set CyclicAngles
noncomputable section

/-- First crossings select an ordered set of preimages even for a nonmonotone map. -/
theorem ordered_interval_preimages {n : ℕ} {f : ℝ → ℝ}
    (hf : Continuous f) {l r : ℝ} (hlr : l < r) (y : Fin n → ℝ)
    (hy : StrictMono y) (hlo : ∀ i, f l ≤ y i) (hhi : ∀ i, y i < f r) :
    ∃ t : Fin n → ℝ, StrictMono t ∧ (∀ i, l ≤ t i ∧ t i < r) ∧
      ∀ i, f (t i) = y i := by
  classical
  let S : Fin n → Set ℝ := fun i => Icc l r ∩ f ⁻¹' {y i}
  have hcompact (i) : IsCompact (S i) :=
    isCompact_Icc.inter_right (isClosed_singleton.preimage hf)
  have hnonempty (i) : (S i).Nonempty := by
    obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hlr.le hf.continuousOn
      ⟨hlo i, (hhi i).le⟩
    exact ⟨t, ht, hft⟩
  let t : Fin n → ℝ := fun i => sInf (S i)
  have ht (i) : t i ∈ S i := (hcompact i).sInf_mem (hnonempty i)
  have hvalue (i) : f (t i) = y i := (ht i).2
  refine ⟨t, ?_, ?_, hvalue⟩
  · intro i j hij
    have htarget : y i < y j := hy hij
    have hlt : l ≤ t j := (ht j).1.1
    obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc hlt hf.continuousOn
      (show y i ∈ Icc (f l) (f (t j)) by rw [hvalue]; exact ⟨hlo i, htarget.le⟩)
    have huS : u ∈ S i := ⟨⟨hu.1, hu.2.trans (ht j).1.2⟩, hfu⟩
    have hle : t i ≤ t j :=
      (csInf_le (hcompact i).bddBelow huS).trans hu.2
    apply lt_of_le_of_ne hle
    intro heq
    have hh : y i = y j := by rw [← hvalue i, ← hvalue j, heq]
    exact htarget.ne hh
  · intro i
    refine ⟨(ht i).1.1, lt_of_le_of_ne (ht i).1.2 ?_⟩
    intro heq
    have hh := hhi i
    rw [← hvalue i, heq] at hh
    exact (lt_irrefl _ hh)

/-- A degree-one real lift admits ordered preimages of every finite cyclic tuple. -/
theorem ordered_lift_preimages {n : ℕ} (hn : 0 < n) (a : Angles n)
    {f : ℝ → ℝ} (hf : Continuous f) (hsurj : Function.Surjective f)
    (hperiod : ∀ t, f (t + 2 * Real.pi) = f t + 2 * Real.pi) :
    ∃ b : Angles n, ∀ i : Fin n, f (b.angle i) = a.angle i := by
  obtain ⟨t₀, ht₀⟩ := hsurj (a.angle 0)
  obtain ⟨t, hmono, hrange, hvalue⟩ := ordered_interval_preimages hf
    (show t₀ < t₀ + 2 * Real.pi by linarith [Real.pi_pos])
    (fun i : Fin n => a.angle i)
    (fun i j hij => a.increasing (by exact_mod_cast hij))
    (fun i => by rw [ht₀]; exact a.increasing.monotone (by omega))
    (fun i => by
      rw [hperiod, ht₀, ← show a.angle n = a.angle 0 + 2 * Real.pi by
        simpa using a.period 0]
      exact a.increasing (by omega))
  let b₀ := ExteriorReduction.anglesOfFinite hn (fun i => t i - t₀)
    (fun i j hij => sub_lt_sub_right (hmono hij) t₀)
    (fun i => ⟨sub_nonneg.mpr (hrange i).1, by linarith [(hrange i).2]⟩)
  let b : Angles n :=
    { angle := fun j => b₀.angle j + t₀
      increasing := fun i j hij => by dsimp; linarith [b₀.increasing hij]
      period := fun j => by rw [b₀.period]; ring }
  refine ⟨b, fun i => ?_⟩
  have hb : b.angle i = t i := by
    change ExteriorReduction.periodicAngle hn (fun i => t i - t₀) i + t₀ = t i
    rw [ExteriorReduction.periodicAngle_fin]
    ring
  rw [hb]
  exact hvalue i

end
end Erdos1045.EventualExact.PhysicalBoundaryOrder

