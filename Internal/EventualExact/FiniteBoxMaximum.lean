import EventualExact.FiniteMultiplier
import Mathlib.Data.Finset.Max

/-!
# An attained finite antiperiodic box maximum

The maximum is defined over a finite set of actual sign vectors. A single
gradient rounding step dominates every point of the box, so this finite maximum
is also the maximum over the whole real box. No existence premise is used.
-/

noncomputable section

open scoped BigOperators

namespace Erdos1045.EventualExact.FiniteBox

open FourierMultiplier

def Antiperiodic {m : ℕ} (hm : 0 < m) (q : Fin (2 * m) → ℝ) : Prop :=
  ∀ j, q (halfTurn hm j) = -q j

def box {m : ℕ} (hm : 0 < m) (A : ℝ) : Set (Fin (2 * m) → ℝ) :=
  {q | Antiperiodic hm q ∧ ∀ j, |q j| ≤ A}

def boolSign (b : Bool) : ℝ := if b then 1 else -1

theorem boolSign_is_sign (b : Bool) : boolSign b = 1 ∨ boolSign b = -1 := by
  cases b <;> simp [boolSign]

theorem boolSign_decide {x : ℝ} (h : x = 1 ∨ x = -1) :
    boolSign (decide (x = 1)) = x := by
  classical
  rcases h with rfl | rfl <;> norm_num [boolSign]

theorem halfTurn_lt_iff {m : ℕ} (hm : 0 < m) (j : Fin (2 * m)) :
    (halfTurn hm j).val < m ↔ ¬j.val < m := by
  have hj := j.isLt
  change (j.val + m) % (2 * m) < m ↔ ¬j.val < m
  by_cases h : j.val < m
  · rw [Nat.mod_eq_of_lt (by omega : j.val + m < 2 * m)]
    omega
  · rw [show j.val + m = (j.val - m) + 2 * m by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega : j.val - m < 2 * m)]
    omega

/-- Boolean sign columns satisfying the exact half-turn relation. -/
def SignPattern {m : ℕ} (hm : 0 < m) :=
  {s : Fin (2 * m) → Bool // Antiperiodic hm (fun j => boolSign (s j))}

instance {m : ℕ} (hm : 0 < m) : Fintype (SignPattern hm) := by
  classical
  unfold SignPattern
  infer_instance

def seedPattern {m : ℕ} (hm : 0 < m) : SignPattern hm :=
  ⟨fun j => decide (j.val < m), by
    intro j
    simp only [boolSign, decide_eq_true_eq, halfTurn_lt_iff]
    split <;> simp_all⟩

instance {m : ℕ} (hm : 0 < m) : Nonempty (SignPattern hm) := ⟨seedPattern hm⟩

def patternSign {m : ℕ} {hm : 0 < m} (s : SignPattern hm) (j : Fin (2 * m)) : ℝ :=
  boolSign (s.val j)

theorem patternSign_is_sign {m : ℕ} {hm : 0 < m} (s : SignPattern hm) :
    IsSignVector (patternSign s) := fun j => boolSign_is_sign (s.val j)

theorem patternSign_antiperiodic {m : ℕ} {hm : 0 < m} (s : SignPattern hm) :
    Antiperiodic hm (patternSign s) := s.property

def encodeSign {m : ℕ} {hm : 0 < m} (s : Fin (2 * m) → ℝ)
    (hs : IsSignVector s) (ha : Antiperiodic hm s) : SignPattern hm :=
  ⟨fun j => decide (s j = 1), by
    intro j
    dsimp only
    rw [boolSign_decide (hs _), boolSign_decide (hs _), ha j]⟩

theorem patternSign_encodeSign {m : ℕ} {hm : 0 < m} (s : Fin (2 * m) → ℝ)
    (hs : IsSignVector s) (ha : Antiperiodic hm s) :
    patternSign (encodeSign s hs ha) = s := by
  funext j
  exact boolSign_decide (hs j)

def vertex {m : ℕ} {hm : 0 < m} (A : ℝ) (s : SignPattern hm) :
    Fin (2 * m) → ℝ := boxVertex A (patternSign s)

theorem vertex_abs {m : ℕ} {hm : 0 < m} {A : ℝ} (hA : 0 ≤ A)
    (s : SignPattern hm) (j : Fin (2 * m)) : |vertex A s j| = A := by
  rcases patternSign_is_sign s j with h | h <;>
    simp [vertex, boxVertex, h, abs_of_nonneg hA]

theorem vertex_mem_box {m : ℕ} {hm : 0 < m} {A : ℝ} (hA : 0 ≤ A)
    (s : SignPattern hm) : vertex A s ∈ box hm A := by
  constructor
  · intro j
    change A * patternSign s (halfTurn hm j) = -(A * patternSign s j)
    rw [patternSign_antiperiodic s j, mul_neg]
  · intro j
    rcases patternSign_is_sign s j with h | h <;>
      simp [vertex, boxVertex, h, abs_of_nonneg hA]

/-- A generic positive quadratic form increases under gradient sign rounding. -/
theorem rounded_energy_ge {ι : Type*} [Fintype ι]
    {T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
    (hTs : FiniteSelfAdjoint T) (hTp : FinitePositiveSemidefinite T)
    {A : ℝ} {f s : ι → ℝ} (hs : IsSignVector s) (hf : ∀ i, |f i| ≤ A) :
    normalizedBoxEnergy T f ≤ normalizedBoxEnergy T (roundedBoxVertex A s (T f)) := by
  have hp : 0 ≤ finitePairing (roundedBoxVertex A s (T f) - f) (T f) := by
    apply Finset.sum_nonneg
    intro i _
    have hi : f i * T f i ≤ A * |T f i| := by
      calc
        _ ≤ |f i * T f i| := le_abs_self _
        _ = |f i| * |T f i| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_right (hf i) (abs_nonneg _)
    have hr := roundedSign_mul (x := T f i) (hs i)
    change 0 ≤ (A * roundedSign (s i) (T f i) - f i) * T f i
    nlinarith [congrArg (fun x : ℝ => A * x) hr]
  have he := boxEnergy_sub hTs f (roundedBoxVertex A s (T f))
  have hpos := boxEnergy_nonneg hTp (roundedBoxVertex A s (T f) - f)
  unfold normalizedBoxEnergy
  exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)

/-- Every point of the real box is dominated by an actual antiperiodic vertex. -/
theorem exists_dominating_vertex {m : ℕ} (hm : 0 < m) {A : ℝ}
    (f : Fin (2 * m) → ℝ) (hf : ∀ j, |f j| ≤ A) :
    ∃ s : SignPattern hm,
      normalizedBoxEnergy (operator (2 * m)) f ≤
        normalizedBoxEnergy (operator (2 * m)) (vertex A s) := by
  let s₀ := patternSign (seedPattern hm)
  let g := operator (2 * m) f
  let s := fun j => roundedSign (s₀ j) (g j)
  have hs : IsSignVector s := fun j => roundedSign_is_sign (patternSign_is_sign _ j)
  have ha : Antiperiodic hm s := by
    intro j
    dsimp [s, g]
    rw [show s₀ (halfTurn hm j) = -s₀ j from patternSign_antiperiodic _ j,
      operator_antiperiodic hm, roundedSign_neg]
  refine ⟨encodeSign s hs ha, ?_⟩
  have he : vertex A (encodeSign s hs ha) = roundedBoxVertex A s₀ g := by
    unfold vertex
    rw [patternSign_encodeSign]
    rfl
  rw [he]
  exact rounded_energy_ge (selfAdjoint _) (positiveSemidefinite _)
    (patternSign_is_sign _) hf

def maximum {m : ℕ} (hm : 0 < m) (A : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun s : SignPattern hm => normalizedBoxEnergy (operator (2 * m)) (vertex A s))

theorem vertex_energy_le_maximum {m : ℕ} {hm : 0 < m} (A : ℝ) (s : SignPattern hm) :
    normalizedBoxEnergy (operator (2 * m)) (vertex A s) ≤ maximum hm A :=
  Finset.le_sup' (fun s : SignPattern hm =>
    normalizedBoxEnergy (operator (2 * m)) (vertex A s)) (Finset.mem_univ s)

theorem energy_le_maximum {m : ℕ} (hm : 0 < m) {A : ℝ}
    (f : Fin (2 * m) → ℝ) (hf : ∀ j, |f j| ≤ A) :
    normalizedBoxEnergy (operator (2 * m)) f ≤ maximum hm A := by
  obtain ⟨s, hs⟩ := exists_dominating_vertex hm f hf
  exact hs.trans (vertex_energy_le_maximum A s)

theorem exists_vertex_maximizer {m : ℕ} (hm : 0 < m) (A : ℝ) :
    ∃ s : SignPattern hm,
      normalizedBoxEnergy (operator (2 * m)) (vertex A s) = maximum hm A := by
  obtain ⟨s, _, hs⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun s : SignPattern hm => normalizedBoxEnergy (operator (2 * m)) (vertex A s))
  exact ⟨s, hs.symm⟩

theorem exists_box_maximizer {m : ℕ} (hm : 0 < m) {A : ℝ} (hA : 0 ≤ A) :
    ∃ f ∈ box hm A, normalizedBoxEnergy (operator (2 * m)) f = maximum hm A ∧
      ∀ g ∈ box hm A, normalizedBoxEnergy (operator (2 * m)) g ≤
        normalizedBoxEnergy (operator (2 * m)) f := by
  obtain ⟨s, hs⟩ := exists_vertex_maximizer hm A
  refine ⟨vertex A s, vertex_mem_box hA s, hs, ?_⟩
  intro g hg
  rw [hs]
  exact energy_le_maximum hm g hg.2

theorem maximum_nonneg {m : ℕ} (hm : 0 < m) (A : ℝ) : 0 ≤ maximum hm A := by
  have h := vertex_energy_le_maximum A (seedPattern hm)
  have hp : 0 ≤ normalizedBoxEnergy (operator (2 * m)) (vertex A (seedPattern hm)) :=
    div_nonneg (boxEnergy_nonneg (positiveSemidefinite _) _) (Nat.cast_nonneg _)
  exact hp.trans h

/-- Every maximizing sign vertex agrees with the sign of its potential. -/
theorem maximizer_sign_alignment {m : ℕ} (hm : 0 < m) {A : ℝ} (hA : 0 < A)
    (s : SignPattern hm)
    (hs : normalizedBoxEnergy (operator (2 * m)) (vertex A s) = maximum hm A)
    (j : Fin (2 * m)) :
    patternSign s j * operator (2 * m) (vertex A s) j =
      |operator (2 * m) (vertex A s) j| := by
  let : NeZero (2 * m) := ⟨by omega⟩
  have hB := energy_le_maximum hm
    (roundedBoxVertex A (patternSign s) (operator (2 * m) (vertex A s)))
    (roundedBoxVertex_mem_box hA.le (patternSign_is_sign s) _)
  have hb := normalized_badSignMass_le_defect (selfAdjoint (2 * m))
    (positiveSemidefinite (2 * m)) hA (patternSign_is_sign s) hB
  change badSignMass (patternSign s) (operator (2 * m) (vertex A s)) /
    Fintype.card (Fin (2 * m)) ≤ (maximum hm A -
      normalizedBoxEnergy (operator (2 * m)) (vertex A s)) / (2 * A) at hb
  rw [hs, sub_self, zero_div] at hb
  have hmpos : (0 : ℝ) < Fintype.card (Fin (2 * m)) := by
    simp only [Fintype.card_fin]
    positivity
  have hz : badSignMass (patternSign s) (operator (2 * m) (vertex A s)) = 0 :=
    le_antisymm (by simpa only [zero_mul] using (div_le_iff₀ hmpos).mp hb)
      (badSignMass_nonneg _ _)
  have hj := Finset.single_le_sum
    (fun i (_ : i ∈ Finset.univ) => badSignWeight_nonneg
      (patternSign s i) (operator (2 * m) (vertex A s) i)) (Finset.mem_univ j)
  change badSignWeight (patternSign s j) (operator (2 * m) (vertex A s) j) ≤
    badSignMass (patternSign s) (operator (2 * m) (vertex A s)) at hj
  rw [hz] at hj
  have he := sign_abs_gap (x := operator (2 * m) (vertex A s) j)
    (patternSign_is_sign s j)
  have hzero := le_antisymm hj (badSignWeight_nonneg _ _)
  rw [hzero] at he
  linarith

/-- The amplitude in manuscript (4.3). -/
def amplitude (n : ℕ) : ℝ := n * Real.tan (Real.pi / (2 * n))

theorem amplitude_pos {n : ℕ} (hn : 2 ≤ n) : 0 < amplitude n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0 : ℝ) < n := by linarith
  apply mul_pos hnp
  apply Real.tan_pos_of_pos_of_lt_pi_div_two
  · positivity
  · apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * n)).2
    nlinarith [Real.pi_pos]

def Q {m : ℕ} (hm : 0 < m) : Set (Fin (2 * m) → ℝ) := box hm (amplitude (2 * m))

def B {m : ℕ} (hm : 0 < m) : ℝ := maximum hm (amplitude (2 * m))

theorem energy_le_B {m : ℕ} (hm : 0 < m) {f : Fin (2 * m) → ℝ}
    (hf : f ∈ Q hm) : normalizedBoxEnergy (operator (2 * m)) f ≤ B hm :=
  energy_le_maximum hm f hf.2

theorem B_attained {m : ℕ} (hm : 0 < m) :
    ∃ f ∈ Q hm, normalizedBoxEnergy (operator (2 * m)) f = B hm ∧
      ∀ g ∈ Q hm, normalizedBoxEnergy (operator (2 * m)) g ≤
        normalizedBoxEnergy (operator (2 * m)) f :=
  exists_box_maximizer hm (amplitude_pos (by omega)).le

theorem B_nonneg {m : ℕ} (hm : 0 < m) : 0 ≤ B hm := maximum_nonneg hm _

theorem B_attained_at_vertex {m : ℕ} (hm : 0 < m) :
    ∃ s : SignPattern hm,
      normalizedBoxEnergy (operator (2 * m)) (vertex (amplitude (2 * m)) s) = B hm ∧
      (∀ j, |vertex (amplitude (2 * m)) s j| = amplitude (2 * m)) ∧
      ∀ j, patternSign s j * operator (2 * m) (vertex (amplitude (2 * m)) s) j =
        |operator (2 * m) (vertex (amplitude (2 * m)) s) j| := by
  obtain ⟨s, hs⟩ := exists_vertex_maximizer hm (amplitude (2 * m))
  refine ⟨s, hs, vertex_abs (amplitude_pos (by omega)).le s, ?_⟩
  exact maximizer_sign_alignment hm (amplitude_pos (by omega)) s hs

/-- Manuscript Lemma 7.1 for the actual finite operator and the constructed Bn. -/
theorem rounding_defect {m : ℕ} (hm : 0 < m) (s : SignPattern hm) :
    let A := amplitude (2 * m)
    let f := vertex A s
    let g := operator (2 * m) f
    badSignMass (patternSign s) g / (2 * m : ℕ) ≤
      (B hm - normalizedBoxEnergy (operator (2 * m)) f) / (2 * A) ∧
    (∑ j, (patternSign s j * g j - |g j|) ^ 2) / (2 * m : ℕ) ≤
      (2 * ‖g‖ / A) * (B hm - normalizedBoxEnergy (operator (2 * m)) f) := by
  let : NeZero (2 * m) := ⟨by omega⟩
  simpa only [vertex, B, Fintype.card_fin] using
    normalized_box_rounding_defect (selfAdjoint (2 * m))
      (positiveSemidefinite (2 * m)) (amplitude_pos (by omega))
      (patternSign_is_sign s) (fun f hf => energy_le_maximum hm f hf)

end Erdos1045.EventualExact.FiniteBox
