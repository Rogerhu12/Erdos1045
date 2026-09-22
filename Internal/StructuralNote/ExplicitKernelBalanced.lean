import StructuralNote.ExplicitKernelCompression
import StructuralNote.FiniteWordClassification

/-! Pointwise finite-word classification from the explicit kernel cutoff.

The sole input not supplied here is the pointwise localization certificate.
All kernel, terminal-slide, arc, and three-block estimates use the displayed
cutoff and the common improvement constant `16 / 25`.
-/

namespace StructuralNote.ExplicitKernelBalanced

open Real Set Finset Erdos1045.EventualExact FourierMultiplier FiniteBox
open ExplicitKernelRateIdentification ExplicitKernelCompression
open FixedDualClassificationKernelSignsPropagation FixedDualClassificationKernelSignsFinal
open FiniteCompressionKernelGeometry FiniteCompressionBackgroundUniform
open FiniteCompressionConvolutionBase FiniteCompressionArcPartition
open FiniteCompressionRanked FiniteCompressionEnergy FixedDualClassificationFinite
open SolTerminalActualGain SolTerminalComponent SolTerminalTranslate
open SolTerminalBoxMove SolWordFlips SolWordHamming
open TerminalSlideUniform LocalizedTerminalImprovement LocalizedThreeArcDichotomy
open ArcTransitionTransport
open FixedDualClassificationExteriorGaps FixedDualClassificationArcGrid
open FixedDualClassificationArcRecenter
open FiniteCompressionLocalizedBackground FiniteCompressionStandardArcs
open FiniteCompressionArcAngles LocalizedArcDichotomy
open SignPatternGridShift SignPatternSymmetry SignPatternEnergySymmetry
open FixedDualClassificationNormalizedSigns
open ThreeArcCanonicalWord ThreeBlockKernelMargin ThreeBlockLocalImprovement
open SolThreeBlockWord SolThreeBlockEnergy SolIntegratedKernel
open DiscreteConvexBalance IntegerBalance
open FiniteWordClassification
open scoped BigOperators Topology
noncomputable section

/-- One fixed elementary cutoff makes the standard grid-step estimate explicit. -/
def wordClassificationThreshold : ℕ :=
  max compressionKernelSignsThreshold 1000

theorem explicit_small_grid_step :
    ∀ m ≥ wordClassificationThreshold,
      Real.pi / m ≤ (Real.pi - 3) / 24 := by
  intro m hm
  have hm1000 : 1000 ≤ m := (le_max_right _ _).trans hm
  have hmR : (1000 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1000
  have hmpos : (0 : ℝ) < (m : ℝ) := by positivity
  calc
    Real.pi / (m : ℝ) ≤ Real.pi / 1000 := by
      apply (div_le_div_iff₀ hmpos (by norm_num : (0 : ℝ) < 1000)).2
      nlinarith [mul_le_mul_of_nonneg_left hmR Real.pi_pos.le]
    _ ≤ 4 / 1000 := div_le_div_of_nonneg_right Real.pi_le_four (by norm_num)
    _ ≤ (Real.pi - 3) / 24 := by linarith [Real.pi_gt_d2]

/-- Pointwise replacement for `eventually_actual_grid_kernel_antitone`. -/
theorem explicit_actual_grid_kernel_antitone :
    ∀ m ≥ wordClassificationThreshold, ∀ N : ℕ,
      2 * Real.pi * N / (2 * m : ℝ) ≤ Real.pi / 12 →
      AntitoneOn (FiniteCompressionRanked.gridKernel (2 * m)) (Set.Icc 0 N) := by
  intro m hm N hN
  have hs := explicit_compressionKernelSigns m ((le_max_left _ _).trans hm)
  intro i hi j hj hij
  rw [FiniteCompressionGeometric.gridKernel_eq,
    FiniteCompressionGeometric.gridKernel_eq]
  apply near_antitone hs hij
  have hangle : (j : ℝ) * (2 * Real.pi / (2 * m : ℕ)) ≤
      (N : ℝ) * (2 * Real.pi / (2 * m : ℕ)) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hj.2) (by positivity)
  have he : (N : ℝ) * (2 * Real.pi / (2 * m : ℕ)) =
      2 * Real.pi * N / (2 * m : ℝ) := by push_cast; ring
  rw [he] at hangle
  exact hangle.trans hN

/-- The terminal slide at the displayed cutoff, with no filter extraction. -/
theorem explicit_actual_word_terminal_gain_on_arc :
    ∀ m ≥ wordClassificationThreshold,
      ∀ (hm : 0 < m) (E : Finset ℕ) (hE : E.Nonempty)
        (ell R : ℕ) (s : SignPattern hm) (A gamma : ℝ),
    R < m →
    2 * Real.pi * (R - ell : ℕ) / (2 * m : ℝ) ≤ Real.pi / 12 →
    E ≠ natInterval ell (terminalRight E hE) →
    (∀ x ∈ E, ell ≤ x ∧ x ≤ R) →
    (∀ x, ell ≤ x → x ≤ R →
      (x ∈ E ↔ patternSign s (site hm x) = 1)) →
    0 ≤ A → 0 ≤ gamma →
    (∀ k, terminalLeft E hE ≤ k → k ≤ terminalRight E hE →
      gamma ≤ operator (2 * m)
          (vertex A s - patch hm A (gridSites hm E)) (site hm (k - 1)) -
        operator (2 * m) (vertex A s - patch hm A (gridSites hm E))
          (site hm k)) →
    ∃ left right : Fin m,
      left.val = terminalLeft E hE - 1 ∧
      right.val = terminalRight E hE ∧
      hamming s (flipTwo s left right) ≤ 2 ∧
      4 * A * gamma / (2 * m : ℝ) ≤
        normalizedBoxEnergy (operator (2 * m)) (vertex A (flipTwo s left right)) -
          normalizedBoxEnergy (operator (2 * m)) (vertex A s) := by
  intro m hmThreshold hm E hE ell R s A gamma hR hspan hnot hEarc hsign hA hgamma hstep
  have hsub : ∀ x ∈ E, ell ≤ x ∧ x ≤ R := hEarc
  have hleft_lt : ell < terminalLeft E hE :=
    terminal_component_of_not_initial_from E hE ell
      (fun x hx => (hsub x hx).1) hnot
  have hLmem := terminalLeft_mem E hE
  have hRmem := right_mem E hE
  have hleft_le_R : terminalLeft E hE ≤ R := (hsub _ hLmem).2
  have hright_le_R : terminalRight E hE ≤ R := (hsub _ hRmem).2
  have hpos : 0 < terminalLeft E hE := by omega
  have hFirst : ∀ x ∈ E, x < m := by
    intro x hx
    exact (hsub x hx).2.trans_lt hR
  have hnewsub : ∀ x ∈ translateTerminal E hE, ell ≤ x ∧ x ≤ R :=
    translate_subset_interval E hE hsub hleft_lt
  have hNewFirst : ∀ x ∈ translateTerminal E hE, x < m := by
    intro x hx
    exact (hnewsub x hx).2.trans_lt hR
  have hbound : ∀ x ∈ E, ∀ y ∈ E, Nat.dist x y ≤ R - ell := by
    intro x hx y hy
    have hx' := hsub x hx
    have hy' := hsub y hy
    by_cases hxy : x ≤ y
    · rw [Nat.dist_eq_sub_of_le hxy]
      omega
    · have hyx : y ≤ x := by omega
      rw [Nat.dist_eq_sub_of_le_right hyx]
      omega
  have hkernel := explicit_actual_grid_kernel_antitone m hmThreshold (R - ell) hspan
  have hleft_arc : ell ≤ terminalLeft E hE - 1 := by omega
  have hleft_not : terminalLeft E hE - 1 ∉ E :=
    before_left_not_mem E hE hpos
  have hleft_sign_site :
      patternSign s (site hm (terminalLeft E hE - 1)) = -1 := by
    have hiff := hsign (terminalLeft E hE - 1) hleft_arc
      (by omega : terminalLeft E hE - 1 ≤ R)
    have hne : patternSign s (site hm (terminalLeft E hE - 1)) ≠ 1 := by
      intro hs1
      exact hleft_not (hiff.mpr hs1)
    rcases patternSign_is_sign s (site hm (terminalLeft E hE - 1)) with hs1 | hs1
    · exact (hne hs1).elim
    · exact hs1
  have hright_sign_site :
      patternSign s (site hm (terminalRight E hE)) = 1 := by
    have hiff := hsign (terminalRight E hE) (hsub _ hRmem).1 hright_le_R
    exact hiff.mp hRmem
  have hsite_left :
      site hm (terminalLeft E hE - 1) =
        first ⟨terminalLeft E hE - 1, by
          have hx := hFirst _ hLmem
          omega⟩ := by
    apply Fin.ext
    rw [site_val hm]
    · rfl
    · have hx := hFirst _ hLmem
      omega
  have hsite_right :
      site hm (terminalRight E hE) =
        first ⟨terminalRight E hE, hFirst _ hRmem⟩ := by
    apply Fin.ext
    rw [site_val hm]
    · rfl
    · have hx := hFirst _ hRmem
      omega
  have hleft :
      patternSign s (first ⟨terminalLeft E hE - 1, by
        have hx := hFirst _ hLmem
        omega⟩) = -1 := by
    rw [← hsite_left]
    exact hleft_sign_site
  have hright :
      patternSign s (first ⟨terminalRight E hE, hFirst _ hRmem⟩) = 1 := by
    rw [← hsite_right]
    exact hright_sign_site
  have hg := actual_word_terminal_gain E hE hm hA hgamma hpos hFirst hNewFirst s
    hleft hright hstep hbound hkernel
  rcases hg with ⟨hgHam, hgGain⟩
  let left : Fin m := ⟨terminalLeft E hE - 1, by
    have hx := hFirst _ hLmem
    omega⟩
  let right : Fin m := ⟨terminalRight E hE, hFirst _ hRmem⟩
  refine ⟨left, right, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · simpa [left, right] using hgHam
  · simpa [left, right] using hgGain

/-- A bad terminal component improves the actual energy by `(16/25)/(2m)^2`. -/
theorem explicit_terminal_two_site_improvement :
    ∀ m ≥ wordClassificationThreshold, ∀ (hm : 0 < m) (E : Finset ℕ) (hE : E.Nonempty)
      (ell R : ℕ) (s : SignPattern hm),
      R < m → 2 * Real.pi * (R - ell : ℕ) / (2 * m : ℝ) ≤ Real.pi / 12 →
      E ≠ natInterval ell (terminalRight E hE) →
      (∀ x ∈ E, ell ≤ x ∧ x ≤ R) →
      (∀ x, ell ≤ x → x ≤ R → (x ∈ E ↔ patternSign s (site hm x) = 1)) →
      (∀ k, terminalLeft E hE ≤ k → k ≤ terminalRight E hE →
        Nonempty (BackgroundArcs hm
          (vertex (amplitude (2 * m)) s - patch hm (amplitude (2 * m)) (gridSites hm E))
          (k - 1))) →
      TwoSiteImprovement hm (16 / 25) s := by
  intro m hmThreshold hm E hE ell R s hR hspan hnot hEarc hsign harcs
  let A := amplitude (2 * m)
  let b := vertex A s - patch hm A (gridSites hm E)
  have hA : 1 ≤ A := amplitude_ge_one (by omega)
  have hbox : b ∈ Q hm := word_background_mem_Q hm s E (by
    intro x hx
    exact (hsign x (hEarc x hx).1 (hEarc x hx).2).mp hx)
  have hleft := terminal_component_of_not_initial_from E hE ell
    (fun x hx => (hEarc x hx).1) hnot
  have hstep : ∀ k, terminalLeft E hE ≤ k → k ≤ terminalRight E hE →
      (4 / 25 : ℝ) / (2 * m : ℕ) ≤ operator (2 * m) b (site hm (k - 1)) -
        operator (2 * m) b (site hm k) := by
    intro k hkL hkR
    obtain ⟨arcs⟩ := harcs k hkL hkR
    exact explicit_background_predecessor_drop m ((le_max_left _ _).trans hmThreshold)
      hm b hbox k (by omega) arcs
  obtain ⟨left, right, _, _, hh, hg⟩ :=
    explicit_actual_word_terminal_gain_on_arc m hmThreshold hm E hE ell R s A
      ((4 / 25 : ℝ) / (2 * m : ℕ)) hR hspan hnot hEarc hsign
      (by linarith) (by positivity) hstep
  let t := flipTwo s left right
  have hprice : (16 / 25 : ℝ) / (2 * m : ℕ) ^ 2 ≤
      4 * A * ((4 / 25 : ℝ) / (2 * m : ℕ)) / (2 * m : ℝ) := by
    have hn : (0 : ℝ) < (2 * m : ℕ) ^ 2 := by positivity
    calc
      _ ≤ 4 * A * (4 / 25 : ℝ) / (2 * m : ℕ) ^ 2 := by
        apply div_le_div_of_nonneg_right _ hn.le
        nlinarith [mul_le_mul_of_nonneg_right hA (by norm_num : (0 : ℝ) ≤ 4 / 25)]
      _ = _ := by push_cast; ring
  exact ⟨t, hh, hprice.trans hg⟩

/-- The localized first arc has its canonical transition or the explicit gain. -/
theorem explicit_first_arc_dichotomy :
    ∀ m ≥ wordClassificationThreshold, ∀ (hm : 0 < m) (s : SignPattern hm) (β : ℝ),
      0 ≤ β → β ≤ gridStep m → LocalizedSigns hm s β →
      (∃ cut ∈ Set.Icc (arcLeft m β 0) (arcRight m β 0),
        ∀ j ∈ Set.Icc (arcLeft m β 0) (arcRight m β 0 + 1),
          patternSign s (site hm j) = if j ≤ cut then 1 else -1) ∨
        TwoSiteImprovement hm (16 / 25) s := by
  intro m hmThreshold hm s β hβ0 hβhi hs
  have hstep := explicit_small_grid_step m hmThreshold
  obtain ⟨h01, h12, h11, h23, h22, hlast, hR⟩ :=
    standard_arc_order hm hβ0 hβhi hstep
  have hex := standard_exteriorSigns hm s hβ0 hstep hs
  let E := localizedPositiveSites hm s (arcLeft m β 0) (arcRight m β 0)
  have hsupport : ∀ x ∈ E, arcLeft m β 0 + 1 ≤ x ∧ x ≤ arcRight m β 0 := by
    intro x hx
    exact Finset.mem_Icc.mp (Finset.mem_filter.mp hx).1
  have hsign : ∀ j, arcLeft m β 0 + 1 ≤ j → j ≤ arcRight m β 0 →
      (j ∈ E ↔ patternSign s (site hm j) = 1) := by
    intro j hjL hjR
    simp only [E, localizedPositiveSites, Finset.mem_filter, Finset.mem_Icc]
    exact and_iff_right ⟨hjL, hjR⟩
  rcases localized_arc_dichotomy s h01.le hex.1
      (hex.2.1 _ (by omega) (by omega)) E hsupport hsign with hbad | hgood
  · right
    obtain ⟨hE, hnot⟩ := hbad
    have harcs : ∀ k, terminalLeft E hE ≤ k → k ≤ terminalRight E hE →
        Nonempty (BackgroundArcs hm
          (localizedBackground hm (amplitude (2 * m)) s
            (arcLeft m β 0) (arcRight m β 0)) (k - 1)) := by
      intro k hkL hkR
      have hk := hsupport k (terminal_interval E hE hkL hkR)
      exact standard_background_arcs hm s hβ0 hβhi hstep hs (by omega) (by omega)
    exact explicit_terminal_two_site_improvement m hmThreshold hm E hE
      (arcLeft m β 0 + 1) (arcRight m β 0) s hR
      (standard_arc_short_span hm hβ0 hβhi hstep) hnot hsupport hsign harcs
  · exact Or.inl hgood

/-- All three localized arcs have their canonical transitions, or there is the explicit gain. -/
theorem explicit_three_arc_dichotomy :
    ∀ m ≥ wordClassificationThreshold, ∀ (hm : 0 < m) (s : SignPattern hm) (β : ℝ),
      0 ≤ β → β ≤ gridStep m → LocalizedSigns hm s β →
        ThreeTransitions hm s β ∨ TwoSiteImprovement hm (16 / 25) s := by
  intro m hmThreshold hm s β hβ0 hβhi hs
  have hstep := explicit_small_grid_step m hmThreshold
  rcases explicit_first_arc_dichotomy m hmThreshold hm s β hβ0 hβhi hs with h0 | himp
  · obtain ⟨k₁, γ₁, hγ₁, he₁⟩ := phase_normalization_nonneg hm
      (show 0 ≤ β + Real.pi / 3 by positivity)
    have hs₁ := localizedSigns_rotate_direct (localizedSigns_negate_third hs) k₁ he₁
    rcases explicit_first_arc_dichotomy m hmThreshold hm
      (rotatePattern k₁ (globalNegate s)) γ₁ hγ₁.1 hγ₁.2.le hs₁ with h1 | himp
    · have hcuts₁ := arc_cuts_recenter hm hγ₁.1 hstep
        (i := 1) (α := β) (by simpa only [Nat.cast_one, one_mul] using he₁)
      have h1' := descending_of_rotate hm (globalNegate s) k₁ _ _ h1
      rw [hcuts₁.1, hcuts₁.2] at h1'
      have ha1 := ascending_of_negate hm s _ _ h1'
      obtain ⟨k₂, γ₂, hγ₂, he₂⟩ := phase_normalization_nonneg hm
        (show 0 ≤ β + 2 * Real.pi / 3 by positivity)
      have hs₂ := localizedSigns_rotate_direct (localizedSigns_two_thirds hs) k₂ he₂
      rcases explicit_first_arc_dichotomy m hmThreshold hm
        (rotatePattern k₂ s) γ₂ hγ₂.1 hγ₂.2.le hs₂ with h2 | himp
      · have hcuts₂ := arc_cuts_recenter hm hγ₂.1 hstep
          (i := 2) (α := β) (by norm_num only [Nat.cast_ofNat] at *; exact he₂)
        have h2' := descending_of_rotate hm s k₂ _ _ h2
        rw [hcuts₂.1, hcuts₂.2] at h2'
        exact Or.inl ⟨h0, ha1, h2'⟩
      · exact Or.inr (improvement_of_rotate k₂ himp)
    · exact Or.inr (improvement_of_negate (improvement_of_rotate k₁ himp))
  · exact Or.inr himp

/-- The standard three-block interval is already sufficient; no enlarged,
nonconstructively chosen interval is needed. -/
theorem explicit_three_block_two_site_improvement :
    ∀ m ≥ wordClassificationThreshold, ∀ (hm : 0 < m) (a b c : ℕ)
      (hp : 0 < a ∧ 0 < b ∧ 0 < c) (hs : a + b + c = m),
      angle m a ∈ Icc (Real.pi / 4) (5 * Real.pi / 12) →
      angle m b ∈ Icc (Real.pi / 4) (5 * Real.pi / 12) →
      angle m c ∈ Icc (Real.pi / 4) (5 * Real.pi / 12) →
      ¬ BalancedAt (m / 3) a b c →
      TwoSiteImprovement hm (16 / 25) (threeBlockPattern hm hp hs) := by
  intro m hmThreshold hm a b c hp hs ha hb hc hne
  have hmargin : ∀ r : ℤ, angle m r ∈ Icc (Real.pi / 4) (5 * Real.pi / 12) →
      (8 / 25 : ℝ) / (2 * m : ℕ) ^ 2 ≤ secondDifference (S (2 * m)) r := by
    intro r hr
    have hK := integer_kernel_margin (c := (1 : ℝ) / 50)
      (by positivity : (0 : ℝ) < Real.pi / 4)
      (fun q hlo hhi => by
        have hq := explicit_cross_negative_margin m
          ((le_max_left _ _).trans hmThreshold) q hlo hhi
        linarith) hr
    have hconv := strong_convexity_of_margin hm
      (by norm_num : (0 : ℝ) ≤ 1 / 50) hK
    norm_num at hconv ⊢
    exact hconv
  obtain ⟨a', b', c', hp', hs', hh, hg, _, _⟩ :=
    two_site_improvement_of_strong_convexity hm hp hs
      (by positivity : 0 ≤ (8 / 25 : ℝ) / (2 * m : ℕ) ^ 2)
      hmargin ha hb hc hne
  refine ⟨threeBlockPattern hm hp' hs', hh, ?_⟩
  change (16 / 25 : ℝ) / (2 * m : ℕ) ^ 2 ≤
    actualThreeBlockEnergy hm hp' hs' - actualThreeBlockEnergy hm hp hs
  have he : (16 / 25 : ℝ) / (2 * m : ℕ) ^ 2 =
      2 * ((8 / 25 : ℝ) / (2 * m : ℕ) ^ 2) := by ring
  rw [he]
  exact hg

/-- Pointwise finite classification once an explicit localization witness is supplied. -/
theorem explicit_classification_of_localization {m : ℕ}
    (hmThreshold : wordClassificationThreshold ≤ m) (hm : 0 < m)
    (s : SignPattern hm)
    (hloc : ∃ k : ℕ, ∃ β ∈ Ico 0 (gridStep m),
      LocalizedSigns hm (rotatePattern k s) β) :
    BalancedWord hm s ∨ TwoSiteImprovement hm (16 / 25) s := by
  obtain ⟨k, β, hβ, hsign⟩ := hloc
  rcases explicit_three_arc_dichotomy m hmThreshold hm (rotatePattern k s) β
      hβ.1 hβ.2.le hsign with himp | himp
  · obtain ⟨l, a, b, c, hp, hsum, heq, ha, hb, hc⟩ :=
      three_arcs_reconstruct hm (rotatePattern k s) hβ.1 hβ.2.le
        (explicit_small_grid_step m hmThreshold) hsign himp
    by_cases hB : BalancedAt (m / 3) a b c
    · exact Or.inl (balancedWord_of_rotate k ⟨l, a, b, c, hp, hsum, heq, hB⟩)
    · have hcan := explicit_three_block_two_site_improvement m hmThreshold hm
        a b c hp hsum ha hb hc hB
      rw [← heq] at hcan
      exact Or.inr (improvement_of_rotate k (improvement_of_rotate l
        (improvement_of_negate hcan)))
  · exact Or.inr (improvement_of_rotate k himp)

/-- The normalization step itself is finite and exact.  Thus an unwrapped
phase certificate can be fed directly into the pointwise classification. -/
theorem explicit_classification_of_raw_localization {m : ℕ}
    (hmThreshold : wordClassificationThreshold ≤ m) (hm : 0 < m)
    (s : SignPattern hm) {α : ℝ}
    (hα : α ∈ Icc (-(Real.pi / 3)) (Real.pi / 3))
    (hsign : LocalizedSigns hm s α) :
    BalancedWord hm s ∨ TwoSiteImprovement hm (16 / 25) s := by
  obtain ⟨k, β, hβ, heq⟩ := phase_normalization hm hα
  apply explicit_classification_of_localization hmThreshold hm s
  exact ⟨k, β, hβ, localizedSigns_rotate hsign k heq⟩

/-- Explicit pointwise endpoint corresponding to
`FiniteWordClassification.eventually_nonbalanced_improvement`. -/
theorem explicit_nonbalanced_improvement_of_localization {m : ℕ}
    (hmThreshold : wordClassificationThreshold ≤ m) (hm : 0 < m)
    (s : SignPattern hm)
    (hloc : ∃ k : ℕ, ∃ β ∈ Ico 0 (gridStep m),
      LocalizedSigns hm (rotatePattern k s) β)
    (hnot : ¬ BalancedWord hm s) :
    ∃ t : SignPattern hm, hamming s t ≤ 2 ∧
      (16 / 25 : ℝ) / (2 * m : ℕ) ^ 2 ≤
        normalizedBoxEnergy (operator (2 * m)) (vertex (amplitude (2 * m)) t) -
          normalizedBoxEnergy (operator (2 * m)) (vertex (amplitude (2 * m)) s) ∧
      0 ≤ deficit hm t ∧
      deficit hm t + (16 / 25 : ℝ) / (2 * m : ℕ) ^ 2 ≤ deficit hm s := by
  obtain ⟨t, hh, hg⟩ :=
    (explicit_classification_of_localization hmThreshold hm s hloc).resolve_left hnot
  have hupper := energy_le_B hm (vertex_mem_box (amplitude_pos (by omega)).le t)
  refine ⟨t, hh, hg, sub_nonneg.mpr hupper, ?_⟩
  dsimp only [deficit]
  linarith

/-- Unwrapped-phase form of the same explicit endpoint. -/
theorem explicit_nonbalanced_improvement_of_raw_localization {m : ℕ}
    (hmThreshold : wordClassificationThreshold ≤ m) (hm : 0 < m)
    (s : SignPattern hm) {α : ℝ}
    (hα : α ∈ Icc (-(Real.pi / 3)) (Real.pi / 3))
    (hsign : LocalizedSigns hm s α)
    (hnot : ¬ BalancedWord hm s) :
    ∃ t : SignPattern hm, hamming s t ≤ 2 ∧
      (16 / 25 : ℝ) / (2 * m : ℕ) ^ 2 ≤
        normalizedBoxEnergy (operator (2 * m)) (vertex (amplitude (2 * m)) t) -
          normalizedBoxEnergy (operator (2 * m)) (vertex (amplitude (2 * m)) s) ∧
      0 ≤ deficit hm t ∧
      deficit hm t + (16 / 25 : ℝ) / (2 * m : ℕ) ^ 2 ≤ deficit hm s := by
  obtain ⟨k, β, hβ, heq⟩ := phase_normalization hm hα
  apply explicit_nonbalanced_improvement_of_localization hmThreshold hm s
    ⟨k, β, hβ, localizedSigns_rotate hsign k heq⟩ hnot

end
end StructuralNote.ExplicitKernelBalanced
