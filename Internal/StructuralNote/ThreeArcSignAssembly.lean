import StructuralNote.FiniteCompressionLocalizedBackground

/-! Finite assembly of three actual sign arcs and the exterior platform signs. -/

namespace StructuralNote.ThreeArcSignAssembly

open Set
open Erdos1045.EventualExact FiniteBox
open StructuralNote.FiniteCompressionLocalizedBackground
open StructuralNote.FiniteCompressionRanked

noncomputable section

theorem three_arc_cut_order {L₀ R₀ L₁ R₁ L₂ R₂ a b c : ℕ}
    (_hL₀R₀ : L₀ < R₀) (hR₀L₁ : R₀ < L₁) (_hL₁R₁ : L₁ ≤ R₁)
    (hR₁L₂ : R₁ < L₂) (_hL₂R₂ : L₂ ≤ R₂) (hR₂span : R₂ < L₀ + m)
    (ha : a ∈ Icc L₀ R₀) (hb : b ∈ Icc L₁ R₁) (hc : c ∈ Icc L₂ R₂) :
    L₀ ≤ a ∧ a < b ∧ b < c ∧ c < L₀ + m := by
  rcases (mem_Icc.mp ha) with ⟨hLa, haR⟩
  rcases (mem_Icc.mp hb) with ⟨hLb, hbR⟩
  rcases (mem_Icc.mp hc) with ⟨hLc, hcR⟩
  omega

theorem three_arc_sign_formula {m : ℕ} (hm : 0 < m) (s : SignPattern hm)
    {L₀ R₀ L₁ R₁ L₂ R₂ a b c : ℕ}
    (hL₀R₀ : L₀ < R₀) (hR₀L₁ : R₀ < L₁) (hL₁R₁ : L₁ ≤ R₁)
    (hR₁L₂ : R₁ < L₂) (hL₂R₂ : L₂ ≤ R₂) (hR₂span : R₂ < L₀ + m)
    (hsigns : ExteriorSigns hm s L₀ R₀ L₁ R₁ L₂ R₂)
    (ha : a ∈ Icc L₀ R₀) (hb : b ∈ Icc L₁ R₁) (hc : c ∈ Icc L₂ R₂)
    (hArc₀ : ∀ j ∈ Icc L₀ (R₀ + 1),
      patternSign s (site hm j) = if j ≤ a then 1 else -1)
    (hArc₁ : ∀ j ∈ Icc L₁ (R₁ + 1),
      patternSign s (site hm j) = if j ≤ b then -1 else 1)
    (hArc₂ : ∀ j ∈ Icc L₂ (R₂ + 1),
      patternSign s (site hm j) = if j ≤ c then 1 else -1) :
    L₀ ≤ a ∧ a < b ∧ b < c ∧ c < L₀ + m ∧
      (∀ j ∈ Icc L₀ (L₀ + m),
        patternSign s (site hm j) =
          if j ≤ a then 1 else if j ≤ b then -1 else
            if j ≤ c then 1 else -1) := by
  have hcuts := three_arc_cut_order hL₀R₀ hR₀L₁ hL₁R₁ hR₁L₂ hL₂R₂
    hR₂span ha hb hc
  rcases (mem_Icc.mp ha) with ⟨hLa, haR⟩
  rcases (mem_Icc.mp hb) with ⟨hLb, hbR⟩
  rcases (mem_Icc.mp hc) with ⟨hLc, hcR⟩
  refine ⟨hcuts.1, hcuts.2.1, hcuts.2.2.1, hcuts.2.2.2, ?_⟩
  intro j hj
  rcases (mem_Icc.mp hj) with ⟨hjL, hjU⟩
  by_cases hja : j ≤ a
  · have hjArc : j ∈ Icc L₀ (R₀ + 1) := by
      exact ⟨by omega, by omega⟩
    simpa [hja] using hArc₀ j hjArc
  · by_cases hjb : j ≤ b
    · rw [if_neg hja, if_pos hjb]
      by_cases hjR₀ : j ≤ R₀ + 1
      · have hjArc : j ∈ Icc L₀ (R₀ + 1) := by
          exact ⟨by omega, hjR₀⟩
        simpa [hja] using hArc₀ j hjArc
      · by_cases hjL₁ : L₁ ≤ j
        · have hjArc : j ∈ Icc L₁ (R₁ + 1) := by
            exact ⟨hjL₁, by omega⟩
          simpa [hjb] using hArc₁ j hjArc
        · have hExt := hsigns.2.1 j (by omega) (by omega)
          exact hExt
    · by_cases hjc : j ≤ c
      · rw [if_neg hja, if_neg hjb, if_pos hjc]
        by_cases hjR₁ : j ≤ R₁ + 1
        · have hjArc : j ∈ Icc L₁ (R₁ + 1) := by
            exact ⟨by omega, hjR₁⟩
          simpa [hjb] using hArc₁ j hjArc
        · by_cases hjL₂ : L₂ ≤ j
          · have hjArc : j ∈ Icc L₂ (R₂ + 1) := by
              exact ⟨hjL₂, by omega⟩
            simpa [hjc] using hArc₂ j hjArc
          · have hExt := hsigns.2.2.1 j (by omega) (by omega)
            exact hExt
      · rw [if_neg hja, if_neg hjb, if_neg hjc]
        by_cases hjR₂ : j ≤ R₂ + 1
        · have hjArc : j ∈ Icc L₂ (R₂ + 1) := by
            exact ⟨by omega, hjR₂⟩
          simpa [hjc] using hArc₂ j hjArc
        · exact hsigns.2.2.2 j (by omega) (by omega)

end
end StructuralNote.ThreeArcSignAssembly
