import StructuralNote.FixedDualClassificationMidpointSynthesis
import Mathlib.Order.Filter.AtTopBot.Interval

/-! Symmetric cutoffs for the actual continuous odd spectrum and finite grid. -/

namespace StructuralNote.FixedDualClassificationSignedCutoff

open Real Complex Filter Erdos1045.EventualExact FourierMultiplier
open FixedDualClassificationStep FixedDualClassificationStepPotential
open FixedDualClassificationOddSpectrum FixedDualClassificationKernelTail
open FixedDualClassificationFiniteTail FixedDualClassificationMidpointSynthesis
open scoped BigOperators ComplexConjugate Topology
noncomputable section

def signedCutoff (P : ℕ) : Finset ℤ := Finset.Ico (-(P : ℤ)) P

theorem signedCutoff_tendsto : Tendsto signedCutoff atTop atTop :=
  Finset.tendsto_Ico_neg

theorem sum_signedCutoff {M : Type*} [AddCommMonoid M] (f : ℤ → M) (P : ℕ) :
    ∑ k ∈ signedCutoff P, f k = ∑ k ∈ Finset.range P, (f k + f (Int.negSucc k)) := by
  classical
  let e : Fin P ⊕ Fin P → ℤ := Sum.elim (fun k => (k : ℤ)) (fun k => Int.negSucc k)
  have he : (∑ a : Fin P ⊕ Fin P, f (e a)) = ∑ k ∈ signedCutoff P, f k := by
    apply Finset.sum_bij (fun a _ => e a)
    · intro a _
      cases a with
      | inl k => simp only [e, Sum.elim_inl, signedCutoff, Finset.mem_Ico]; omega
      | inr k => simp only [e, Sum.elim_inr, signedCutoff, Finset.mem_Ico]; omega
    · intro a _ b _ h
      cases a <;> cases b <;> simp only [e, Sum.elim_inl, Sum.elim_inr] at h
      · congr 1; apply Fin.ext; omega
      · omega
      · omega
      · congr 1; apply Fin.ext; omega
    · intro k hk
      have hk' := Finset.mem_Ico.mp hk
      by_cases h : 0 ≤ k
      · refine ⟨Sum.inl ⟨k.toNat, by omega⟩, Finset.mem_univ _, ?_⟩
        simp only [e, Sum.elim_inl]
        omega
      · refine ⟨Sum.inr ⟨(-k - 1).toNat, by omega⟩, Finset.mem_univ _, ?_⟩
        simp only [e, Sum.elim_inr]
        omega
    · intro a _
      rfl
  rw [← he, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  exact Fin.sum_univ_eq_sum_range (fun k => f k + f (Int.negSucc k)) P

theorem stepTerm_negSucc {n : ℕ} (q : Fin n → ℝ) (scale θ : ℝ) (k : ℕ) :
    stepTerm q scale θ (Int.negSucc k) = conj (stepTerm q scale θ k) := by
  have hi : (2 * Int.negSucc k + 1 : ℤ) = -(2 * (k : ℤ) + 1) := by omega
  have hr : (2 * (Int.negSucc k : ℝ) + 1) = -(2 * (k : ℝ) + 1) := by
    simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one]
    ring
  simp only [stepTerm, kernelCoefficient, hi, hr, neg_mul, neg_div, sinc_neg,
    neg_neg, signedMidpointCoefficient_neg, oscillation_neg, map_mul,
    Complex.conj_ofReal, starRingEnd_self_apply, Int.cast_natCast]

theorem step_sum_signedCutoff {n : ℕ} (q : Fin n → ℝ) (scale θ : ℝ) (P : ℕ) :
    ∑ k ∈ signedCutoff P, stepTerm q scale θ k =
      ∑ k ∈ Finset.range P, (stepTerm q scale θ k + conj (stepTerm q scale θ k)) := by
  rw [sum_signedCutoff]
  simp only [stepTerm_negSucc]

def positiveFrequency {n P : ℕ} (hn : 4 * P < n) (k : Fin P) : Fin n :=
  ⟨2 * k + 1, by omega⟩

theorem sum_low_odd {n P : ℕ} [NeZero n] (hn : 4 * P < n) (heven : Even n)
    (f : Fin n → ℂ) (hf : ∀ p : Fin n, ¬ Odd (p : ℕ) → f p = 0) :
    ∑ p ∈ lowFrequencies n (2 * P), f p =
      ∑ k : Fin P, (f (positiveFrequency hn k) + f (-positiveFrequency hn k)) := by
  classical
  let e : Fin P ⊕ Fin P → Fin n :=
    Sum.elim (positiveFrequency hn) (fun k => -positiveFrequency hn k)
  have hnmod : n % 2 = 0 := Nat.even_iff.mp heven
  have hv (k : Fin P) : (-positiveFrequency hn k : Fin n).val = n - (2 * k + 1) := by
    rw [Fin.val_neg, if_neg]
    · rfl
    · simp [positiveFrequency]
  have ep (k : Fin P) : (e (Sum.inl k)).val = 2 * k + 1 := rfl
  have en (k : Fin P) : (e (Sum.inr k)).val = n - (2 * k + 1) := hv k
  have he : (∑ a : Fin P ⊕ Fin P, f (e a)) = ∑ p ∈ lowFrequencies n (2 * P), f p := by
    apply Finset.sum_bij_ne_zero (fun a _ _ => e a)
    · intro a _ _
      cases a with
      | inl k =>
        simp only [e, Sum.elim_inl, lowFrequencies, Finset.mem_filter, Finset.mem_univ,
          true_and, positiveFrequency]
        omega
      | inr k =>
        simp only [e, Sum.elim_inr, lowFrequencies, Finset.mem_filter, Finset.mem_univ,
          true_and, hv]
        omega
    · intro a _ _ b _ _ h
      have hval := congrArg Fin.val h
      cases a <;> cases b <;> simp only [ep, en] at hval
      · congr 1; apply Fin.ext; omega
      · omega
      · omega
      · congr 1; apply Fin.ext; omega
    · intro p hp hne
      have ho : Odd (p : ℕ) := by by_contra h; exact hne (hf p h)
      have homod := Nat.odd_iff.mp ho
      have hlow : min (p : ℕ) (n - p) ≤ 2 * P := (Finset.mem_filter.mp hp).2
      have hpbound := p.isLt
      by_cases h : p.val ≤ 2 * P
      · let k : Fin P := ⟨p.val / 2, by omega⟩
        have hek : e (Sum.inl k) = p := by
          apply Fin.ext
          simp only [e, Sum.elim_inl, positiveFrequency, Fin.val_mk, k]
          omega
        refine ⟨Sum.inl k, Finset.mem_univ _, ?_, hek⟩
        simpa only [hek] using hne
      · let k : Fin P := ⟨(n - p.val) / 2, by omega⟩
        have hek : e (Sum.inr k) = p := by
          apply Fin.ext
          simp only [e, Sum.elim_inr, hv, k]
          omega
        refine ⟨Sum.inr k, Finset.mem_univ _, ?_, hek⟩
        simpa only [hek] using hne
    · intro a _ _
      rfl
  rw [← he, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  rfl

theorem finite_sum_low {n P : ℕ} [NeZero n] (hn : 4 * P < n) (heven : Even n)
    (q : Fin n → ℝ) (j : Fin n) :
    ∑ p ∈ lowFrequencies n (2 * P), finiteTerm q j p =
      ∑ k ∈ Finset.range P, (finiteTerm q j (2 * k + 1) + conj (finiteTerm q j (2 * k + 1))) := by
  rw [sum_low_odd hn heven]
  · simp_rw [finiteTerm_neg heven]
    exact Fin.sum_univ_eq_sum_range (fun k => finiteTerm q j (2 * k + 1) +
      conj (finiteTerm q j (2 * k + 1))) P
  · intro p hp
    rw [finiteTerm, SchurWeights.weight_eq_zero (fun h => hp h.1)]
    simp

end
end StructuralNote.FixedDualClassificationSignedCutoff
