import StructuralNote.SolTerminalScore
import StructuralNote.FiniteCompressionRanked
import StructuralNote.SolTerminalBoxMove

namespace StructuralNote.SolTerminalActualGain

open Finset
open scoped BigOperators
open StructuralNote.FiniteCompressionRanked
open StructuralNote.SolTerminalDistances StructuralNote.SolTerminalScore
open StructuralNote.SolTerminalComponent StructuralNote.SolTerminalTranslate
open StructuralNote.SolTerminalInteraction StructuralNote.SolTerminalBackground
open StructuralNote.FiniteCompressionEnergy
open StructuralNote.SolTerminalBoxMove StructuralNote.SolWordFlips StructuralNote.SolWordHamming
open Erdos1045.EventualExact FourierMultiplier FixedDualClassificationKernel
open Erdos1045.EventualExact.FiniteBox

/-- Actual finite-grid kernel specialization of the terminal score gain.  The
arc assumptions are explicit: all occurring distances lie in the interval on
which the genuine finite kernel is antitone, and the genuine background drops
by at least `gamma` per translated site. -/
theorem actual_terminal_score_gain (E : Finset ℕ) {m N L R : ℕ}
    {A gamma : ℝ} (hm : 0 < m) (hA : 0 ≤ A) (hL : 0 < L) (_hLR : L ≤ R)
    (b : Fin (2 * m) → ℝ)
    (hBg : gamma * (R - L + 1) ≤
      (∑ x ∈ E, b (site hm (slideAt L x))) - ∑ x ∈ E, b (site hm x))
    (hbound : ∀ x ∈ E, ∀ y ∈ E, Nat.dist x y ≤ N)
    (hkernel : AntitoneOn (gridKernel (2 * m)) (Set.Icc 0 N)) :
    (4 * A / (2 * m : ℝ)) * (gamma * (R - L + 1)) ≤
      compressionScore E (fun k => b (site hm k)) (gridKernel (2 * m))
          (4 * A / (2 * m : ℝ)) (16 * A^2 / (2 * m : ℝ)^2) L -
        ((4 * A / (2 * m : ℝ)) * ∑ x ∈ E, b (site hm x) +
          (16 * A^2 / (2 * m : ℝ)^2) *
            ∑ x ∈ E, ∑ y ∈ E, gridKernel (2 * m) (Nat.dist x y)) := by
  exact normalized_score_gain E hA (by positivity) hL hBg hbound hkernel

theorem actual_gain_at_least_one_site (E : Finset ℕ) {m N L R : ℕ}
    {A gamma : ℝ} (hm : 0 < m) (hA : 0 ≤ A) (hgamma : 0 ≤ gamma)
    (hL : 0 < L) (hLR : L ≤ R)
    (b : Fin (2 * m) → ℝ)
    (hBg : gamma * (R - L + 1) ≤
      (∑ x ∈ E, b (site hm (slideAt L x))) - ∑ x ∈ E, b (site hm x))
    (hbound : ∀ x ∈ E, ∀ y ∈ E, Nat.dist x y ≤ N)
    (hkernel : AntitoneOn (gridKernel (2 * m)) (Set.Icc 0 N)) :
    4 * A * gamma / (2 * m : ℝ) ≤
      compressionScore E (fun k => b (site hm k)) (gridKernel (2 * m))
          (4 * A / (2 * m : ℝ)) (16 * A^2 / (2 * m : ℝ)^2) L -
        ((4 * A / (2 * m : ℝ)) * ∑ x ∈ E, b (site hm x) +
          (16 * A^2 / (2 * m : ℝ)^2) *
            ∑ x ∈ E, ∑ y ∈ E, gridKernel (2 * m) (Nat.dist x y)) := by
  have hmain := actual_terminal_score_gain E hm hA hL hLR b hBg hbound hkernel
  have hc : 0 ≤ 4 * A / (2 * m : ℝ) := by positivity
  have hcount : (1 : ℝ) ≤ R - L + 1 := by
    have hLRr : (L : ℝ) ≤ R := by exact_mod_cast hLR
    linarith
  have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcount hgamma) hc
  have heq : 4 * A * gamma / (2 * m : ℝ) = (4 * A / (2 * m : ℝ)) * gamma := by ring
  rw [heq]
  simpa only [mul_one] using this.trans hmain

/-- With a local drop `c/n`, the gain has the advertised `4 A c/n²` scale. -/
theorem actual_gain_specialize {A c n gain : ℝ} (hn : 0 < n)
    (hgain : 4 * A * (c / n) / n ≤ gain) :
    4 * A * c / n^2 ≤ gain := by
  calc
    4 * A * c / n^2 = 4 * A * (c / n) / n := by field_simp
    _ ≤ gain := hgain

def gridSites {m : ℕ} (hm : 0 < m) (E : Finset ℕ) : Finset (Fin (2 * m)) :=
  E.image (site hm)

theorem sum_gridSites {m : ℕ} (hm : 0 < m) (E : Finset ℕ)
    (hbound : ∀ x ∈ E, x < 2 * m) (f : Fin (2 * m) → ℝ) :
    (∑ i ∈ gridSites hm E, f i) = ∑ x ∈ E, f (site hm x) := by
  apply sum_image
  intro x hx y hy hxy
  have h := congrArg Fin.val hxy
  simpa only [site_val hm (hbound x hx), site_val hm (hbound y hy)] using h

theorem grid_self_sum {m : ℕ} (hm : 0 < m) (E : Finset ℕ)
    (hbound : ∀ x ∈ E, x < 2 * m) :
    (∑ i ∈ gridSites hm E, ∑ j ∈ gridSites hm E,
      finiteKernel (2 * m) (gridAngle i - gridAngle j)) =
      ∑ x ∈ E, ∑ y ∈ E, gridKernel (2 * m) (Nat.dist x y) := by
  rw [sum_gridSites hm E hbound]
  simp_rw [sum_gridSites hm E hbound]
  apply sum_congr rfl
  intro x hx
  apply sum_congr rfl
  intro y hy
  rw [kernel_grid_distance, site_val hm (hbound x hx), site_val hm (hbound y hy)]

theorem actual_patch_expansion {m : ℕ} (hm : 0 < m) (A : ℝ)
    (E : Finset ℕ) (hbound : ∀ x ∈ E, x < 2 * m) (b : Fin (2 * m) → ℝ) :
    normalizedBoxEnergy (operator (2 * m)) (b + patch hm A (gridSites hm E)) =
      normalizedBoxEnergy (operator (2 * m)) b +
        (4 * A / (2 * m : ℝ)) * ∑ x ∈ E, operator (2 * m) b (site hm x) +
        (16 * A^2 / (2 * m : ℝ)^2) *
          ∑ x ∈ E, ∑ y ∈ E, gridKernel (2 * m) (Nat.dist x y) := by
  rw [energy_add_patch, sum_gridSites hm E hbound, grid_self_sum hm E hbound]

theorem patch_terminal_difference (E : Finset ℕ) (hE : E.Nonempty)
    {m : ℕ} (hm : 0 < m) (A : ℝ) (hpos : 0 < terminalLeft E hE)
    (hOld : ∀ x ∈ E, x < 2 * m)
    (hNew : ∀ x ∈ translateTerminal E hE, x < 2 * m) :
    patch hm A (gridSites hm (translateTerminal E hE)) - patch hm A (gridSites hm E) =
      patch hm A {site hm (terminalLeft E hE - 1)} -
        patch hm A {site hm (terminalRight E hE)} := by
  funext j
  simp only [Pi.sub_apply, patch, Finset.sum_apply]
  rw [sum_gridSites hm _ hNew, sum_gridSites hm E hOld]
  have hd := terminal_set_sum_difference
    (b := fun x => ((2 * A) • (point (site hm x) - point (halfTurn hm (site hm x)))) j)
    E hE hpos
  simpa using hd

theorem actual_normalized_energy_gain (E : Finset ℕ) (hE : E.Nonempty)
    {m N : ℕ} {A gamma : ℝ} (hm : 0 < m) (hA : 0 ≤ A) (hgamma : 0 ≤ gamma)
    (hpos : 0 < terminalLeft E hE)
    (hOld : ∀ x ∈ E, x < 2 * m)
    (hNew : ∀ x ∈ translateTerminal E hE, x < 2 * m)
    (b : Fin (2 * m) → ℝ)
    (hstep : ∀ k, terminalLeft E hE ≤ k → k ≤ terminalRight E hE →
      gamma ≤ operator (2 * m) b (site hm (k - 1)) - operator (2 * m) b (site hm k))
    (hbound : ∀ x ∈ E, ∀ y ∈ E, Nat.dist x y ≤ N)
    (hkernel : AntitoneOn (gridKernel (2 * m)) (Set.Icc 0 N)) :
    4 * A * gamma / (2 * m : ℝ) ≤
      normalizedBoxEnergy (operator (2 * m))
          (b + patch hm A (gridSites hm (translateTerminal E hE))) -
        normalizedBoxEnergy (operator (2 * m)) (b + patch hm A (gridSites hm E)) := by
  rw [actual_patch_expansion hm A _ hNew b, actual_patch_expansion hm A E hOld b]
  have hbg := terminal_set_background_gain
    (b := fun k => operator (2 * m) b (site hm k)) E hE hpos hstep
  have hint := translated_interaction_nondecreasing E hE hpos hbound hkernel
  have hcB : 0 ≤ 4 * A / (2 * m : ℝ) := by positivity
  have hcI : 0 ≤ 16 * A^2 / (2 * m : ℝ)^2 := by positivity
  have hcount : (1 : ℝ) ≤ terminalRight E hE - terminalLeft E hE + 1 := by
    have hLR := terminalLeft_le_right E hE
    have hLRr : (terminalLeft E hE : ℝ) ≤ terminalRight E hE := by exact_mod_cast hLR
    linarith
  have hgam : gamma ≤ gamma *
      (terminalRight E hE - terminalLeft E hE + 1) := by nlinarith
  have hbg1 := hgam.trans hbg
  have hbmul := mul_le_mul_of_nonneg_left hbg1 hcB
  have himul := mul_le_mul_of_nonneg_left hint hcI
  have heq : 4 * A * gamma / (2 * m : ℝ) = (4 * A / (2 * m : ℝ)) * gamma := by ring
  rw [heq]
  linarith

theorem actual_terminal_box_points_and_gain (E : Finset ℕ) (hE : E.Nonempty)
    {m N : ℕ} {A gamma : ℝ} (hm : 0 < m) (hA : 0 ≤ A) (hgamma : 0 ≤ gamma)
    (hpos : 0 < terminalLeft E hE)
    (hOld : ∀ x ∈ E, x < 2 * m)
    (hNew : ∀ x ∈ translateTerminal E hE, x < 2 * m)
    (b : Fin (2 * m) → ℝ) (hb : b ∈ FiniteBox.box hm A)
    (hbOld : ∀ i ∈ gridSites hm E, b i = -A)
    (hbNew : ∀ i ∈ gridSites hm (translateTerminal E hE), b i = -A)
    (hstep : ∀ k, terminalLeft E hE ≤ k → k ≤ terminalRight E hE →
      gamma ≤ operator (2 * m) b (site hm (k - 1)) - operator (2 * m) b (site hm k))
    (hbound : ∀ x ∈ E, ∀ y ∈ E, Nat.dist x y ≤ N)
    (hkernel : AntitoneOn (gridKernel (2 * m)) (Set.Icc 0 N)) :
    b + patch hm A (gridSites hm E) ∈ FiniteBox.box hm A ∧
      b + patch hm A (gridSites hm (translateTerminal E hE)) ∈ FiniteBox.box hm A ∧
      4 * A * gamma / (2 * m : ℝ) ≤
        normalizedBoxEnergy (operator (2 * m))
            (b + patch hm A (gridSites hm (translateTerminal E hE))) -
          normalizedBoxEnergy (operator (2 * m)) (b + patch hm A (gridSites hm E)) := by
  exact ⟨add_patch_mem_box hm A _ b hb hbOld,
    add_patch_mem_box hm A _ b hb hbNew,
    actual_normalized_energy_gain E hE hm hA hgamma hpos hOld hNew b hstep hbound hkernel⟩

theorem actual_gain_gamma_eq_c_div_n (E : Finset ℕ) (hE : E.Nonempty)
    {m N : ℕ} {A c : ℝ} (hm : 0 < m) (hA : 0 ≤ A) (hc : 0 ≤ c)
    (hpos : 0 < terminalLeft E hE)
    (hOld : ∀ x ∈ E, x < 2 * m)
    (hNew : ∀ x ∈ translateTerminal E hE, x < 2 * m)
    (b : Fin (2 * m) → ℝ)
    (hstep : ∀ k, terminalLeft E hE ≤ k → k ≤ terminalRight E hE →
      c / (2 * m : ℝ) ≤
        operator (2 * m) b (site hm (k - 1)) - operator (2 * m) b (site hm k))
    (hbound : ∀ x ∈ E, ∀ y ∈ E, Nat.dist x y ≤ N)
    (hkernel : AntitoneOn (gridKernel (2 * m)) (Set.Icc 0 N)) :
    4 * A * c / (2 * m : ℝ)^2 ≤
      normalizedBoxEnergy (operator (2 * m))
          (b + patch hm A (gridSites hm (translateTerminal E hE))) -
        normalizedBoxEnergy (operator (2 * m)) (b + patch hm A (gridSites hm E)) := by
  have hg := actual_normalized_energy_gain E hE hm hA (div_nonneg hc (by positivity))
    hpos hOld hNew b hstep hbound hkernel
  have heq : 4 * A * c / (2 * m : ℝ)^2 =
      4 * A * (c / (2 * m : ℝ)) / (2 * m : ℝ) := by field_simp
  rw [heq]
  exact hg

theorem actual_word_terminal_gain (E : Finset ℕ) (hE : E.Nonempty)
    {m N : ℕ} {A gamma : ℝ} (hm : 0 < m) (hA : 0 ≤ A) (hgamma : 0 ≤ gamma)
    (hpos : 0 < terminalLeft E hE)
    (hFirst : ∀ x ∈ E, x < m)
    (hNewFirst : ∀ x ∈ translateTerminal E hE, x < m)
    (s : FiniteBox.SignPattern hm)
    (hleft : patternSign s (first ⟨terminalLeft E hE - 1,
      by have := hFirst _ (terminalLeft_mem E hE); omega⟩) = -1)
    (hright : patternSign s (first ⟨terminalRight E hE,
      hFirst _ (right_mem E hE)⟩) = 1)
    (hstep : ∀ k, terminalLeft E hE ≤ k → k ≤ terminalRight E hE →
      gamma ≤ operator (2 * m)
          (vertex A s - patch hm A (gridSites hm E)) (site hm (k - 1)) -
        operator (2 * m) (vertex A s - patch hm A (gridSites hm E)) (site hm k))
    (hbound : ∀ x ∈ E, ∀ y ∈ E, Nat.dist x y ≤ N)
    (hkernel : AntitoneOn (gridKernel (2 * m)) (Set.Icc 0 N)) :
    hamming s (flipTwo s
        ⟨terminalLeft E hE - 1, by have := hFirst _ (terminalLeft_mem E hE); omega⟩
        ⟨terminalRight E hE, hFirst _ (right_mem E hE)⟩) ≤ 2 ∧
      4 * A * gamma / (2 * m : ℝ) ≤
        normalizedBoxEnergy (operator (2 * m))
            (vertex A (flipTwo s
              ⟨terminalLeft E hE - 1, by have := hFirst _ (terminalLeft_mem E hE); omega⟩
              ⟨terminalRight E hE, hFirst _ (right_mem E hE)⟩)) -
          normalizedBoxEnergy (operator (2 * m)) (vertex A s) := by
  let left : Fin m := ⟨terminalLeft E hE - 1,
    by have := hFirst _ (terminalLeft_mem E hE); omega⟩
  let right : Fin m := ⟨terminalRight E hE, hFirst _ (right_mem E hE)⟩
  have hne : left ≠ right := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [left, right] at hv
    have hLR := terminalLeft_le_right E hE
    omega
  have hsLeft : site hm (terminalLeft E hE - 1) = first left := by
    apply Fin.ext
    rw [site_val hm]
    · rfl
    · have := hFirst _ (terminalLeft_mem E hE)
      omega
  have hsRight : site hm (terminalRight E hE) = first right := by
    apply Fin.ext
    rw [site_val hm]
    · rfl
    · have := hFirst _ (right_mem E hE)
      omega
  have hOld2 : ∀ x ∈ E, x < 2 * m := by intro x hx; have := hFirst x hx; omega
  have hNew2 : ∀ x ∈ translateTerminal E hE, x < 2 * m := by
    intro x hx; have := hNewFirst x hx; omega
  let base := vertex A s - patch hm A (gridSites hm E)
  have hg := actual_normalized_energy_gain E hE hm hA hgamma hpos hOld2 hNew2
    base (by simpa [base] using hstep) hbound hkernel
  have hd := patch_terminal_difference E hE hm A hpos hOld2 hNew2
  have hp : patch hm A (gridSites hm (translateTerminal E hE)) =
      patch hm A (gridSites hm E) +
        (patch hm A {first left} - patch hm A {first right}) := by
    rw [← hsLeft, ← hsRight]
    funext j
    have hj := congrFun hd j
    simp only [Pi.sub_apply, Pi.add_apply] at hj ⊢
    linarith
  have hold : base + patch hm A (gridSites hm E) = vertex A s := by
    dsimp [base]
    abel
  have hnew : base + patch hm A (gridSites hm (translateTerminal E hE)) =
      vertex A (flipTwo s left right) := by
    rw [hp]
    dsimp [base]
    rw [vertex_flipTwo_eq_endpoint_patches A s left right hne]
    · abel
    · simpa [left] using hleft
    · simpa [right] using hright
  constructor
  · exact hamming_flipTwo_le_two s left right
  · rw [hold, hnew] at hg
    simpa [left, right] using hg

theorem actual_word_gain_c_div_n {m : ℕ} {hm : 0 < m} {A c : ℝ}
    (s t : FiniteBox.SignPattern hm)
    (h : hamming s t ≤ 2 ∧
      4 * A * (c / (2 * m : ℝ)) / (2 * m : ℝ) ≤
        normalizedBoxEnergy (operator (2 * m)) (vertex A t) -
          normalizedBoxEnergy (operator (2 * m)) (vertex A s)) :
    hamming s t ≤ 2 ∧
      4 * A * c / (2 * m : ℝ)^2 ≤
        normalizedBoxEnergy (operator (2 * m)) (vertex A t) -
          normalizedBoxEnergy (operator (2 * m)) (vertex A s) := by
  refine ⟨h.1, ?_⟩
  have heq : 4 * A * c / (2 * m : ℝ)^2 =
      4 * A * (c / (2 * m : ℝ)) / (2 * m : ℝ) := by field_simp
  rw [heq]
  exact h.2

end StructuralNote.SolTerminalActualGain
