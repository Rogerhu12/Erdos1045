import StructuralNote.FiniteCompressionBackgroundUniform
import StructuralNote.FiniteCompressionEnergy
import StructuralNote.SolTerminalActualGain

/-! Exact local values of a word background after patching the positive sites
on an initial interval.  The sign hypotheses are deliberately only platform
hypotheses; no constancy is assumed inside the selected interval. -/

namespace StructuralNote.FiniteCompressionLocalizedBackground

open Real Set Finset Erdos1045.EventualExact FourierMultiplier FiniteBox
open FiniteCompressionEnergy FiniteCompressionRanked
open FiniteCompressionBackgroundUniform FiniteCompressionConvolutionBase
open SolTerminalActualGain
open scoped BigOperators
noncomputable section

def ExteriorSigns {m : ℕ} (hm : 0 < m) (s : SignPattern hm)
    (L₀ R₀ L₁ R₁ L₂ R₂ : ℕ) : Prop :=
  patternSign s (site hm L₀) = 1 ∧
    (∀ j, R₀ < j → j ≤ L₁ → patternSign s (site hm j) = -1) ∧
    (∀ j, R₁ < j → j ≤ L₂ → patternSign s (site hm j) = 1) ∧
    (∀ j, R₂ < j → j ≤ L₀ + m → patternSign s (site hm j) = -1)

def localizedPositiveSites {m : ℕ} (hm : 0 < m) (s : SignPattern hm)
    (L₀ R₀ : ℕ) : Finset ℕ :=
  (Finset.Icc (L₀ + 1) R₀).filter (fun j => patternSign s (site hm j) = 1)

def localizedBackground {m : ℕ} (hm : 0 < m) (A : ℝ) (s : SignPattern hm)
    (L₀ R₀ : ℕ) : Fin (2 * m) → ℝ :=
  vertex A s - patch hm A (gridSites hm (localizedPositiveSites hm s L₀ R₀))

private theorem localizedPositiveSites_mem_bounds {m : ℕ} (hm : 0 < m)
    (s : SignPattern hm) {L₀ R₀ : ℕ}
    {x : ℕ} (hx : x ∈ localizedPositiveSites hm s L₀ R₀) :
    L₀ + 1 ≤ x ∧ x ≤ R₀ := by
  rw [localizedPositiveSites] at hx
  exact Finset.mem_Icc.mp (mem_filter.mp hx).1

private theorem localizedPositiveSites_lt_two_mul {m : ℕ} (hm : 0 < m)
    (s : SignPattern hm) {L₀ R₀ : ℕ} (hR₀m : R₀ < m)
    {x : ℕ} (hx : x ∈ localizedPositiveSites hm s L₀ R₀) : x < 2 * m := by
  have h := (localizedPositiveSites_mem_bounds hm s hx).2
  omega

private theorem site_mem_localizedPositiveSites_iff {m : ℕ} (hm : 0 < m)
    (s : SignPattern hm) {L₀ R₀ j : ℕ} (hR₀m : R₀ < m)
    (hj : j < 2 * m) :
    site hm j ∈ gridSites hm (localizedPositiveSites hm s L₀ R₀) ↔
      j ∈ localizedPositiveSites hm s L₀ R₀ := by
  constructor
  · intro h
    obtain ⟨x, hx, heq⟩ := mem_image.mp h
    have hxl : x < 2 * m := localizedPositiveSites_lt_two_mul hm s hR₀m hx
    have hv := congrArg Fin.val heq
    rw [site_val hm hxl, site_val hm hj] at hv
    simpa only [hv] using hx
  · intro h
    exact mem_image.mpr ⟨j, h, rfl⟩

private theorem halfTurn_site_not_mem_localizedPositiveSites
    {m : ℕ} (hm : 0 < m) (s : SignPattern hm) {L₀ R₀ j : ℕ}
    (hL₀R₀ : L₀ < R₀) (hR₀m : R₀ < m) (hj : j ≤ L₀ + m) :
    halfTurn hm (site hm j) ∉
      gridSites hm (localizedPositiveSites hm s L₀ R₀) := by
  have hL₀m : L₀ < m := by omega
  have hj2m : j < 2 * m := by omega
  intro h
  obtain ⟨x, hx, heq⟩ := mem_image.mp h
  have hxbounds := localizedPositiveSites_mem_bounds hm s hx
  have hxm : x < m := lt_of_le_of_lt hxbounds.2 hR₀m
  have hxm2 : x + m < 2 * m := by omega
  have hsite : site hm j = site hm (x + m) := by
    calc
      site hm j = halfTurn hm (halfTurn hm (site hm j)) :=
        (SchurLift.halfTurn_involutive hm _).symm
      _ = halfTurn hm (site hm x) := by rw [← heq]
      _ = site hm (x + m) := site_halfTurn hm x
  have hv := congrArg Fin.val hsite
  rw [site_val hm hj2m, site_val hm hxm2] at hv
  omega

private theorem patch_localized_at_site {m : ℕ} (hm : 0 < m) (A : ℝ)
    (s : SignPattern hm) {L₀ R₀ j : ℕ} (hL₀R₀ : L₀ < R₀)
    (hR₀m : R₀ < m) (hj : j ≤ L₀ + m) :
    patch hm A (gridSites hm (localizedPositiveSites hm s L₀ R₀)) (site hm j) =
      if j ∈ localizedPositiveSites hm s L₀ R₀ then 2 * A else 0 := by
  have hL₀m : L₀ < m := by omega
  have hj2m : j < 2 * m := by omega
  rw [patch_apply]
  have hsite := site_mem_localizedPositiveSites_iff (L₀ := L₀) (R₀ := R₀)
    (j := j) hm s hR₀m hj2m
  have hhalf := halfTurn_site_not_mem_localizedPositiveSites
    (L₀ := L₀) (R₀ := R₀) (j := j) hm s hL₀R₀ hR₀m hj
  simp only [hsite, hhalf]
  by_cases h : j ∈ localizedPositiveSites hm s L₀ R₀ <;> simp [h]

theorem localizedBackground_at_site {m : ℕ} (hm : 0 < m) (A : ℝ)
    (s : SignPattern hm) {L₀ R₀ j : ℕ} (hL₀R₀ : L₀ < R₀)
    (hR₀m : R₀ < m) (hj : j ≤ L₀ + m) :
    localizedBackground hm A s L₀ R₀ (site hm j) =
      A * patternSign s (site hm j) -
        (if j ∈ localizedPositiveSites hm s L₀ R₀ then 2 * A else 0) := by
  simp only [localizedBackground, Pi.sub_apply, vertex, boxVertex]
  rw [patch_localized_at_site hm A s hL₀R₀ hR₀m hj]

theorem localized_background_values {m : ℕ} (hm : 0 < m) (A : ℝ)
    (s : SignPattern hm) {L₀ R₀ L₁ R₁ L₂ R₂ : ℕ}
    (hL₀R₀ : L₀ < R₀) (hR₀L₁ : R₀ < L₁) (hL₁R₁ : L₁ ≤ R₁)
    (hR₁L₂ : R₁ < L₂) (hL₂R₂ : L₂ ≤ R₂) (hR₂span : R₂ < L₀ + m)
    (hR₀m : R₀ < m) (hsigns : ExteriorSigns hm s L₀ R₀ L₁ R₁ L₂ R₂) :
    (∀ j, L₀ + 1 ≤ j → j ≤ L₁ →
      localizedBackground hm A s L₀ R₀ (site hm j) = -A) ∧
    (∀ j, R₁ + 1 ≤ j → j ≤ L₂ →
      localizedBackground hm A s L₀ R₀ (site hm j) = A) ∧
    (∀ j, R₂ + 1 ≤ j → j ≤ L₀ + m →
      localizedBackground hm A s L₀ R₀ (site hm j) = -A) ∧
    localizedBackground hm A s L₀ R₀ (site hm L₀) = A := by
  have hL₀m : L₀ < m := by omega
  have hfirst : ∀ j, L₀ + 1 ≤ j → j ≤ L₁ →
      localizedBackground hm A s L₀ R₀ (site hm j) = -A := by
    intro j hjlo hjhi
    have hjspan : j ≤ L₀ + m := by omega
    rw [localizedBackground_at_site hm A s hL₀R₀ hR₀m hjspan]
    by_cases hjR₀ : j ≤ R₀
    · rcases patternSign_is_sign s (site hm j) with hsgn | hsgn
      · have hjE : j ∈ localizedPositiveSites hm s L₀ R₀ := by
          unfold localizedPositiveSites
          apply mem_filter.mpr
          constructor
          · simp only [Finset.mem_Icc]
            exact ⟨hjlo, hjR₀⟩
          · exact hsgn
        simp only [if_pos hjE, hsgn]
        ring
      · have hjE : j ∉ localizedPositiveSites hm s L₀ R₀ := by
          intro h
          rw [localizedPositiveSites] at h
          have hmem := (mem_filter.mp h).2
          linarith
        simp only [if_neg hjE, hsgn]
        ring
    · have hsj := hsigns.2.1 j (by omega) hjhi
      have hjE : j ∉ localizedPositiveSites hm s L₀ R₀ := by
        intro h
        exact hjR₀ (localizedPositiveSites_mem_bounds hm s h).2
      simp only [if_neg hjE, hsj]
      ring
  refine ⟨hfirst, ?_⟩
  constructor
  · intro j hjlo hjhi
    have hjspan : j ≤ L₀ + m := by omega
    have hsj := hsigns.2.2.1 j (by omega) hjhi
    have hjE : j ∉ localizedPositiveSites hm s L₀ R₀ := by
      intro h
      have hXR := (localizedPositiveSites_mem_bounds hm s h).2
      omega
    rw [localizedBackground_at_site hm A s hL₀R₀ hR₀m hjspan]
    simp only [if_neg hjE, hsj]
    ring
  constructor
  · intro j hjlo hjhi
    have hjspan : j ≤ L₀ + m := hjhi
    have hsj := hsigns.2.2.2 j (by omega) hjhi
    have hjE : j ∉ localizedPositiveSites hm s L₀ R₀ := by
      intro h
      have hXR := (localizedPositiveSites_mem_bounds hm s h).2
      omega
    rw [localizedBackground_at_site hm A s hL₀R₀ hR₀m hjspan]
    simp only [if_neg hjE, hsj]
    ring
  · have hjspan : L₀ ≤ L₀ + m := by omega
    have hjE : L₀ ∉ localizedPositiveSites hm s L₀ R₀ := by
      intro h
      have hX := (localizedPositiveSites_mem_bounds hm s h).1
      omega
    rw [localizedBackground_at_site hm A s hL₀R₀ hR₀m hjspan]
    simp only [if_neg hjE, hsigns.1]
    ring

theorem localized_background_increment_support {m : ℕ} (hm : 0 < m) (A : ℝ)
    (s : SignPattern hm) {L₀ R₀ L₁ R₁ L₂ R₂ : ℕ}
    (hL₀R₀ : L₀ < R₀) (hR₀L₁ : R₀ < L₁) (hL₁R₁ : L₁ ≤ R₁)
    (hR₁L₂ : R₁ < L₂) (hL₂R₂ : L₂ ≤ R₂) (hR₂span : R₂ < L₀ + m)
    (hR₀m : R₀ < m) (hsigns : ExteriorSigns hm s L₀ R₀ L₁ R₁ L₂ R₂) :
    ∀ t ∈ Set.Ico L₀ (L₀ + m), t ≠ L₀ →
      t ∉ Set.Icc L₁ R₁ → t ∉ Set.Icc L₂ R₂ →
      sequence hm (localizedBackground hm A s L₀ R₀) (t + 1) =
        sequence hm (localizedBackground hm A s L₀ R₀) t := by
  have hvals := localized_background_values hm A s hL₀R₀ hR₀L₁ hL₁R₁
    hR₁L₂ hL₂R₂ hR₂span hR₀m hsigns
  intro t ht hne hnot₁ hnot₂
  change L₀ ≤ t ∧ t < L₀ + m at ht
  change ¬(L₁ ≤ t ∧ t ≤ R₁) at hnot₁
  change ¬(L₂ ≤ t ∧ t ≤ R₂) at hnot₂
  have htlo : L₀ + 1 ≤ t := by omega
  have htup : t + 1 ≤ L₀ + m := by omega
  have hcases : t + 1 ≤ L₁ ∨
      (R₁ + 1 ≤ t ∧ t + 1 ≤ L₂) ∨ R₂ + 1 ≤ t := by
    omega
  change localizedBackground hm A s L₀ R₀ (site hm (t + 1)) =
    localizedBackground hm A s L₀ R₀ (site hm t)
  rcases hcases with hfirst | hmiddle | hlast
  · rw [hvals.1 (t + 1) (by omega) hfirst,
      hvals.1 t htlo (by omega)]
  · rw [hvals.2.1 (t + 1) (by omega) hmiddle.2,
      hvals.2.1 t (by omega) (by omega)]
  · rw [hvals.2.2.1 (t + 1) (by omega) htup,
      hvals.2.2.1 t hlast (by omega)]

end
end StructuralNote.FiniteCompressionLocalizedBackground
