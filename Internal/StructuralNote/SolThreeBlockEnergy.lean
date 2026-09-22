import StructuralNote.SolThreeBlockTransfer
import StructuralNote.SolIntegratedKernel
import EventualExact.FiniteFourierLift
import EventualExact.SchurLift

namespace StructuralNote.SolThreeBlockEnergy

open Complex Erdos1045.EventualExact
open FourierMultiplier FiniteBox FiniteFourierLift
open StructuralNote.SolThreeBlockWord StructuralNote.SolIntegratedKernel
open StructuralNote.SolThreeBlockTransfer StructuralNote.SolWordHamming
open StructuralNote.DiscreteConvexBalance StructuralNote.FixedDualClassificationKernel
open scoped BigOperators ComplexConjugate
noncomputable section

def actualThreeBlockEnergy {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m) : ℝ :=
  normalizedBoxEnergy (operator (2 * m))
    (threeBlockVertex hm hpos hsum (amplitude (2 * m)))

def rawComplex {m : ℕ} (r₁ r₂ : ℕ) : Fin (2 * m) → ℂ :=
  fun j => threeBlockRaw (m := m) r₁ r₂ j

theorem rawDifference_firstJump {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m) :
    difference (by omega : 0 < 2 * m) (rawComplex (m := m) r₁ r₂)
      ⟨r₁ - 1, by omega⟩ = -2 := by
  rcases hpos with ⟨h₁, h₂, h₃⟩
  have e₂ : r₁ % m = r₁ := Nat.mod_eq_of_lt (by omega)
  have e₃ : (r₁ - 1) % m = r₁ - 1 := Nat.mod_eq_of_lt (by omega)
  have hp : r₁ - 1 + 1 = r₁ := by omega
  simp only [difference, successor, rawComplex, threeBlockRaw, halfValue]
  simp only [hp, Nat.mod_eq_of_lt (by omega : r₁ < 2 * m), e₂, e₃]
  repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
  norm_num

theorem rawDifference_secondJump {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m) :
    difference (by omega : 0 < 2 * m) (rawComplex (m := m) r₁ r₂)
      ⟨r₁ + r₂ - 1, by omega⟩ = 2 := by
  rcases hpos with ⟨h₁, h₂, h₃⟩
  have hp : r₁ + r₂ - 1 + 1 = r₁ + r₂ := by omega
  have e₁ : (r₁ + r₂) % (2 * m) = r₁ + r₂ := Nat.mod_eq_of_lt (by omega)
  have e₂ : (r₁ + r₂) % m = r₁ + r₂ := Nat.mod_eq_of_lt (by omega)
  have e₃ : (r₁ + r₂ - 1) % m = r₁ + r₂ - 1 := Nat.mod_eq_of_lt (by omega)
  simp only [difference, successor, rawComplex, threeBlockRaw, halfValue]
  simp only [hp, e₁, e₂, e₃]
  repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
  norm_num

theorem rawDifference_halfBoundary {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m) :
    difference (by omega : 0 < 2 * m) (rawComplex (m := m) r₁ r₂)
      ⟨m - 1, by omega⟩ = -2 := by
  rcases hpos with ⟨h₁, h₂, h₃⟩
  have hp : m - 1 + 1 = m := by omega
  have e₁ : m % (2 * m) = m := Nat.mod_eq_of_lt (by omega)
  have e₂ : (m - 1) % m = m - 1 := Nat.mod_eq_of_lt (by omega)
  simp only [difference, successor, rawComplex, threeBlockRaw, halfValue]
  simp only [hp, e₁, Nat.mod_self, e₂]
  repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
  norm_num

theorem rawDifference_halfTurn {m r₁ r₂ : ℕ} (hm : 0 < m) (j : Fin (2 * m)) :
    difference (by omega : 0 < 2 * m) (rawComplex (m := m) r₁ r₂) (halfTurn hm j) =
      -difference (by omega : 0 < 2 * m) (rawComplex (m := m) r₁ r₂) j := by
  unfold difference rawComplex
  rw [← Erdos1045.EventualExact.SchurLift.halfTurn_successor hm]
  rw [threeBlockRaw_antiperiodic hm, threeBlockRaw_antiperiodic hm]
  push_cast
  ring

theorem rawDifference_eq_zero_firstHalf {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m)
    (j : Fin (2 * m)) (hj : j.val < m)
    (h₁ : j.val ≠ r₁ - 1) (h₂ : j.val ≠ r₁ + r₂ - 1)
    (h₃ : j.val ≠ m - 1) :
    difference (by omega : 0 < 2 * m) (rawComplex (m := m) r₁ r₂) j = 0 := by
  rcases hpos with ⟨hp₁, hp₂, hp₃⟩
  have hj1m : j.val + 1 < m := by omega
  have hj12m : j.val + 1 < 2 * m := by omega
  have e₁ : (j.val + 1) % (2 * m) = j.val + 1 := Nat.mod_eq_of_lt hj12m
  have e₂ : (j.val + 1) % m = j.val + 1 := Nat.mod_eq_of_lt hj1m
  have e₃ : j.val % m = j.val := Nat.mod_eq_of_lt hj
  have hc : (j.val + 1 < r₁ ∨ r₁ + r₂ ≤ j.val + 1) ↔
      (j.val < r₁ ∨ r₁ + r₂ ≤ j.val) := by omega
  simp only [difference, successor, rawComplex, threeBlockRaw, halfValue]
  simp only [e₁, e₂, e₃, if_pos hj, if_pos hj1m]
  simp [hc]

theorem rawDifference_eq_zero_off_jumps {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m)
    (j : Fin (2 * m))
    (hoff : j ≠ ⟨r₁ - 1, by omega⟩ ∧ j ≠ ⟨r₁ + r₂ - 1, by omega⟩ ∧
      j ≠ ⟨m - 1, by omega⟩ ∧
      j ≠ halfTurn hm ⟨r₁ - 1, by omega⟩ ∧
      j ≠ halfTurn hm ⟨r₁ + r₂ - 1, by omega⟩ ∧
      j ≠ halfTurn hm ⟨m - 1, by omega⟩) :
    difference (by omega : 0 < 2 * m) (rawComplex (m := m) r₁ r₂) j = 0 := by
  by_cases hj : j.val < m
  · apply rawDifference_eq_zero_firstHalf hm hpos hsum j hj
    · intro e; exact hoff.1 (Fin.ext e)
    · intro e; exact hoff.2.1 (Fin.ext e)
    · intro e; exact hoff.2.2.1 (Fin.ext e)
  · let k := halfTurn hm j
    have hk : k.val < m := (halfTurn_lt_iff hm j).2 hj
    have hk1 : k.val ≠ r₁ - 1 := by
      intro e
      have he : k = ⟨r₁ - 1, by omega⟩ := Fin.ext e
      apply hoff.2.2.2.1
      rw [← he]
      exact (Erdos1045.EventualExact.SchurLift.halfTurn_involutive hm j).symm
    have hk2 : k.val ≠ r₁ + r₂ - 1 := by
      intro e
      have he : k = ⟨r₁ + r₂ - 1, by omega⟩ := Fin.ext e
      apply hoff.2.2.2.2.1
      rw [← he]
      exact (Erdos1045.EventualExact.SchurLift.halfTurn_involutive hm j).symm
    have hk3 : k.val ≠ m - 1 := by
      intro e
      have he : k = ⟨m - 1, by omega⟩ := Fin.ext e
      apply hoff.2.2.2.2.2
      rw [← he]
      exact (Erdos1045.EventualExact.SchurLift.halfTurn_involutive hm j).symm
    have hz := rawDifference_eq_zero_firstHalf hm hpos hsum k hk hk1 hk2 hk3
    have ha := rawDifference_halfTurn (m := m) (r₁ := r₁) (r₂ := r₂) hm k
    rw [Erdos1045.EventualExact.SchurLift.halfTurn_involutive hm j, hz, neg_zero] at ha
    exact ha

def jumpSupport {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (_hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (_hsum : r₁ + r₂ + r₃ = m) :
    Finset (Fin (2 * m)) :=
  {⟨r₁ - 1, by omega⟩, ⟨r₁ + r₂ - 1, by omega⟩, ⟨m - 1, by omega⟩,
    halfTurn hm ⟨r₁ - 1, by omega⟩, halfTurn hm ⟨r₁ + r₂ - 1, by omega⟩,
    halfTurn hm ⟨m - 1, by omega⟩}

/-- The cyclic finite-difference DFT is supported on the six genuine jumps. -/
theorem coefficient_rawDifference_eq_jump_sum {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m)
    (p : Fin (2 * m)) :
    coefficient (difference (by omega : 0 < 2 * m) (rawComplex (m := m) r₁ r₂)) p =
      (∑ j ∈ jumpSupport hm hpos hsum,
        difference (by omega : 0 < 2 * m) (rawComplex (m := m) r₁ r₂) j *
          conj (character (2 * m) p j)) / (2 * m : ℕ) := by
  unfold coefficient
  congr 1
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  have hoff : j ≠ ⟨r₁ - 1, by omega⟩ ∧ j ≠ ⟨r₁ + r₂ - 1, by omega⟩ ∧
      j ≠ ⟨m - 1, by omega⟩ ∧
      j ≠ halfTurn hm ⟨r₁ - 1, by omega⟩ ∧
      j ≠ halfTurn hm ⟨r₁ + r₂ - 1, by omega⟩ ∧
      j ≠ halfTurn hm ⟨m - 1, by omega⟩ := by
    simpa [jumpSupport] using hj
  rw [rawDifference_eq_zero_off_jumps hm hpos hsum j hoff, zero_mul]

theorem halfTurn_first_value {m : ℕ} (hm : 0 < m) (j : Fin (2 * m))
    (hj : j.val < m) : halfTurn hm j = ⟨j.val + m, by omega⟩ := by
  apply Fin.ext
  simp [halfTurn, Nat.mod_eq_of_lt (by omega : j.val + m < 2 * m)]

theorem coefficient_rawDifference_active {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m)
    (p : Fin (2 * m)) (hp : SchurWeights.Active (2 * m) p) :
    coefficient (difference (by omega : 0 < 2 * m) (rawComplex (m := m) r₁ r₂)) p =
      4 * (-conj (character (2 * m) p (r₁ - 1)) +
        conj (character (2 * m) p (r₁ + r₂ - 1)) -
        conj (character (2 * m) p (m - 1))) / (2 * m : ℕ) := by
  rw [coefficient_rawDifference_eq_jump_sum hm hpos hsum p]
  rcases hpos with ⟨h₁, h₂, h₃⟩
  let a : Fin (2 * m) := ⟨r₁ - 1, by omega⟩
  let b : Fin (2 * m) := ⟨r₁ + r₂ - 1, by omega⟩
  let c : Fin (2 * m) := ⟨m - 1, by omega⟩
  let d : Fin (2 * m) := ⟨r₁ - 1 + m, by omega⟩
  let e : Fin (2 * m) := ⟨r₁ + r₂ - 1 + m, by omega⟩
  let f : Fin (2 * m) := ⟨m - 1 + m, by omega⟩
  have hne (x y : Fin (2 * m)) (hxy : x.val < y.val) : x ≠ y := by
    intro h
    have := congrArg Fin.val h
    omega
  have hab : a ≠ b := hne a b (by dsimp [a, b]; omega)
  have hac : a ≠ c := hne a c (by dsimp [a, c]; omega)
  have had : a ≠ d := hne a d (by dsimp [a, d]; omega)
  have hae : a ≠ e := hne a e (by dsimp [a, e]; omega)
  have haf : a ≠ f := hne a f (by dsimp [a, f]; omega)
  have hbc : b ≠ c := hne b c (by dsimp [b, c]; omega)
  have hbd : b ≠ d := hne b d (by dsimp [b, d]; omega)
  have hbe : b ≠ e := hne b e (by dsimp [b, e]; omega)
  have hbf : b ≠ f := hne b f (by dsimp [b, f]; omega)
  have hcd : c ≠ d := hne c d (by dsimp [c, d]; omega)
  have hce : c ≠ e := hne c e (by dsimp [c, e]; omega)
  have hcf : c ≠ f := hne c f (by dsimp [c, f]; omega)
  have hde : d ≠ e := hne d e (by dsimp [d, e]; omega)
  have hdf : d ≠ f := hne d f (by dsimp [d, f]; omega)
  have hef : e ≠ f := hne e f (by dsimp [e, f]; omega)
  have had' : halfTurn hm a = d := halfTurn_first_value hm a (by dsimp [a]; omega)
  have hbe' : halfTurn hm b = e := halfTurn_first_value hm b (by dsimp [b]; omega)
  have hcf' : halfTurn hm c = f := halfTurn_first_value hm c (by dsimp [c]; omega)
  have hsupport : jumpSupport hm ⟨h₁, h₂, h₃⟩ hsum = {a, b, c, d, e, f} := by
    change {a, b, c, halfTurn hm a, halfTurn hm b, halfTurn hm c} = _
    rw [had', hbe', hcf']
  rw [hsupport]
  have haN : a ∉ ({b, c, d, e, f} : Finset (Fin (2 * m))) := by simp [hab, hac, had, hae, haf]
  have hbN : b ∉ ({c, d, e, f} : Finset (Fin (2 * m))) := by simp [hbc, hbd, hbe, hbf]
  have hcN : c ∉ ({d, e, f} : Finset (Fin (2 * m))) := by simp [hcd, hce, hcf]
  have hdN : d ∉ ({e, f} : Finset (Fin (2 * m))) := by simp [hde, hdf]
  have heN : e ∉ ({f} : Finset (Fin (2 * m))) := by simp [hef]
  rw [Finset.sum_insert haN, Finset.sum_insert hbN, Finset.sum_insert hcN,
    Finset.sum_insert hdN, Finset.sum_insert heN, Finset.sum_singleton]
  have hda := rawDifference_firstJump hm ⟨h₁, h₂, h₃⟩ hsum
  have hdb := rawDifference_secondJump hm ⟨h₁, h₂, h₃⟩ hsum
  have hdc := rawDifference_halfBoundary hm ⟨h₁, h₂, h₃⟩ hsum
  have hdad := rawDifference_halfTurn (m := m) (r₁ := r₁) (r₂ := r₂) hm a
  have hdbe := rawDifference_halfTurn (m := m) (r₁ := r₁) (r₂ := r₂) hm b
  have hdcf := rawDifference_halfTurn (m := m) (r₁ := r₁) (r₂ := r₂) hm c
  have hcad := character_halfTurn (p := p.val) hm hp.1 a
  have hcbe := character_halfTurn (p := p.val) hm hp.1 b
  have hccf := character_halfTurn (p := p.val) hm hp.1 c
  change difference (by omega : 0 < 2 * m) (rawComplex (m := m) r₁ r₂) a = -2 at hda
  change difference (by omega : 0 < 2 * m) (rawComplex (m := m) r₁ r₂) b = 2 at hdb
  change difference (by omega : 0 < 2 * m) (rawComplex (m := m) r₁ r₂) c = -2 at hdc
  rw [← had', ← hbe', ← hcf']
  rw [hda, hdb, hdc, hdad, hdbe, hdcf, hda, hdb, hdc, hcad, hcbe, hccf]
  dsimp [a, b, c]
  push_cast
  simp only [map_neg]
  ring

/-- Division by the cyclic difference symbol, specialized to real Fourier
coefficients.  This is the active-frequency bridge used in the three-jump calculation. -/
theorem realCoefficient_eq_difference_div {n : ℕ} (hn : 0 < n)
    (f : Fin n → ℝ) (p : Fin n) (hp : p.val ≠ 0) :
    realCoefficient f p =
      coefficient (difference hn (fun j => (f j : ℂ))) p / differenceSymbol n p := by
  have hd := coefficient_difference hn (fun j => (f j : ℂ)) p
  rw [hd]
  exact (eq_div_iff (differenceSymbol_ne_zero hn p hp)).2 rfl

theorem threeBlockCoefficient_eq_difference_div {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m)
    (p : Fin (2 * m)) (hp : p.val ≠ 0) :
    realCoefficient (threeBlockVertex hm hpos hsum (amplitude (2 * m))) p =
      coefficient (difference (by omega : 0 < 2 * m)
        (fun j => (threeBlockVertex hm hpos hsum (amplitude (2 * m)) j : ℂ))) p /
          differenceSymbol (2 * m) p :=
  realCoefficient_eq_difference_div (by omega) _ p hp

/-- The elementary three-phase norm expansion.  Later the three phases are the
three genuine jump locations `0,r₁,r₁+r₂`. -/
theorem normSq_three_phases (x y z : ℂ) (hx : normSq x = 1)
    (hy : normSq y = 1) (hz : normSq z = 1) :
    normSq (x - y + z) = 3 - 2 * (x * conj y).re + 2 * (x * conj z).re -
      2 * (y * conj z).re := by
  rw [normSq_add, normSq_sub, hx, hy, hz]
  rw [sub_mul]
  change 1 + 1 - 2 * (x * conj y).re + 1 +
      2 * ((x * conj z).re - (y * conj z).re) = _
  ring

theorem coefficient_vertexDifference_active {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m)
    (p : Fin (2 * m)) (_hp : SchurWeights.Active (2 * m) p) :
    coefficient (difference (by omega : 0 < 2 * m)
        (fun j => (threeBlockVertex hm hpos hsum (amplitude (2 * m)) j : ℂ))) p =
      (amplitude (2 * m) : ℂ) *
        coefficient (difference (by omega : 0 < 2 * m)
          (rawComplex (m := m) r₁ r₂)) p := by
  have hv (j : Fin (2 * m)) :
      (threeBlockVertex hm hpos hsum (amplitude (2 * m)) j : ℂ) =
        (amplitude (2 * m) : ℂ) * rawComplex (m := m) r₁ r₂ j := by
    simp [threeBlockVertex, vertex, boxVertex, rawComplex]
  unfold coefficient difference
  simp_rw [hv]
  simp_rw [← mul_sub, mul_assoc]
  rw [← Finset.mul_sum]
  push_cast
  ring

theorem active_three_phase_norm {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m)
    (p : Fin (2 * m)) (hp : SchurWeights.Active (2 * m) p) :
    normSq (-conj (character (2 * m) p (r₁ - 1)) +
        conj (character (2 * m) p (r₁ + r₂ - 1)) -
        conj (character (2 * m) p (m - 1))) =
      3 - 2 * Real.cos (2 * Real.pi * (p : ℕ) * (r₁ : ℝ) / (2 * m)) -
        2 * Real.cos (2 * Real.pi * (p : ℕ) * (r₂ : ℝ) / (2 * m)) -
        2 * Real.cos (2 * Real.pi * (p : ℕ) * (r₃ : ℝ) / (2 * m)) := by
  rcases hpos with ⟨h₁, h₂, h₃⟩
  let a : Fin (2 * m) := ⟨r₁ - 1, by omega⟩
  let b : Fin (2 * m) := ⟨r₁ + r₂ - 1, by omega⟩
  let c : Fin (2 * m) := ⟨m - 1, by omega⟩
  have hn (j : Fin (2 * m)) : normSq (conj (character (2 * m) p j)) = 1 := by
    rw [normSq_conj, SolIntegratedKernel.character_normSq]
  have hexpand := normSq_three_phases (conj (character (2 * m) p a))
    (conj (character (2 * m) p b)) (conj (character (2 * m) p c)) (hn a) (hn b) (hn c)
  have hneg : -conj (character (2 * m) p (r₁ - 1)) +
        conj (character (2 * m) p (r₁ + r₂ - 1)) -
        conj (character (2 * m) p (m - 1)) =
      -(conj (character (2 * m) p (r₁ - 1)) -
        conj (character (2 * m) p (r₁ + r₂ - 1)) +
        conj (character (2 * m) p (m - 1))) := by ring
  rw [hneg]
  rw [normSq_neg]
  change normSq (conj (character (2 * m) p a) - conj (character (2 * m) p b) +
      conj (character (2 * m) p c)) = _
  rw [hexpand]
  have hstar (x : ℂ) : (starRingEnd ℂ) ((starRingEnd ℂ) x) = x := star_star x
  simp_rw [hstar]
  change 3 - 2 * (conj (character (2 * m) p a) * character (2 * m) p b).re +
      2 * (conj (character (2 * m) p a) * character (2 * m) p c).re -
      2 * (conj (character (2 * m) p b) * character (2 * m) p c).re = _
  have hre (x y : Fin (2 * m)) :
      (conj (character (2 * m) p x) * character (2 * m) p y).re =
        Real.cos (2 * Real.pi * (p : ℕ) * ((y : ℝ) - (x : ℝ)) / (2 * m)) := by
    rw [mul_comm]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      SolIntegratedKernel.character_mul_conj_re p y x
  rw [hre a b, hre a c, hre b c]
  dsimp [a, b, c]
  have habN : (r₁ + r₂ - 1 : ℕ) - (r₁ - 1) = r₂ := by omega
  have hab : ((r₁ + r₂ - 1 : ℕ) : ℝ) - (r₁ - 1 : ℕ) = r₂ := by
    rw [← Nat.cast_sub (by omega : r₁ - 1 ≤ r₁ + r₂ - 1), habN]
  have hbcN : (m - 1 : ℕ) - (r₁ + r₂ - 1) = r₃ := by omega
  have hbc : ((m - 1 : ℕ) : ℝ) - (r₁ + r₂ - 1 : ℕ) = r₃ := by
    rw [← Nat.cast_sub (by omega : r₁ + r₂ - 1 ≤ m - 1), hbcN]
  rw [hab, hbc]
  obtain ⟨k, hk⟩ := hp.1
  have hcaN : (m - 1 : ℕ) - (r₁ - 1) = m - r₁ := by omega
  have hca : ((m - 1 : ℕ) : ℝ) - (r₁ - 1 : ℕ) = (m : ℝ) - r₁ := by
    rw [← Nat.cast_sub (by omega : r₁ - 1 ≤ m - 1), hcaN,
      Nat.cast_sub (by omega : r₁ ≤ m)]
  rw [hca]
  have hang : 2 * Real.pi * (p : ℕ) * ((m : ℝ) - r₁) / (2 * m) =
      Real.pi * (2 * k + 1) - 2 * Real.pi * (p : ℕ) * (r₁ : ℝ) / (2 * m) := by
    rw [hk]
    push_cast
    field_simp
  rw [hang]
  have hperiod : Real.pi * (2 * (k : ℝ) + 1) -
        2 * Real.pi * (p : ℕ) * (r₁ : ℝ) / (2 * m) =
      (Real.pi - 2 * Real.pi * (p : ℕ) * (r₁ : ℝ) / (2 * m)) +
        k * (2 * Real.pi) := by ring
  rw [hperiod, Real.cos_add_nat_mul_two_pi, Real.cos_sub]
  simp
  ring

theorem active_threeBlockCoefficient_normSq {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m)
    (p : Fin (2 * m)) (hp : SchurWeights.Active (2 * m) p) :
    normSq (realCoefficient (threeBlockVertex hm hpos hsum (amplitude (2 * m))) p) =
      (2 * amplitude (2 * m) / (2 * m)) ^ 2 *
        (3 - 2 * Real.cos (2 * Real.pi * (p : ℕ) * (r₁ : ℝ) / (2 * m)) -
          2 * Real.cos (2 * Real.pi * (p : ℕ) * (r₂ : ℝ) / (2 * m)) -
          2 * Real.cos (2 * Real.pi * (p : ℕ) * (r₃ : ℝ) / (2 * m))) /
        Real.sin (Real.pi * (p : ℕ) / (2 * m)) ^ 2 := by
  have hp0 : (p : ℕ) ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by omega : 0 < 3) hp.2.1)
  rw [threeBlockCoefficient_eq_difference_div hm hpos hsum p hp0,
    coefficient_vertexDifference_active hm hpos hsum p hp,
    coefficient_rawDifference_active hm hpos hsum p hp]
  rw [normSq_div, normSq_mul, normSq_div, normSq_mul, normSq_ofReal,
    active_three_phase_norm hm hpos hsum p hp,
    SolIntegratedKernel.differenceSymbol_normSq (by omega) p]
  norm_num [Complex.normSq_apply]
  have hn : ((2 * m : ℕ) : ℝ) ≠ 0 := by positivity
  have hs := SolIntegratedKernel.active_sine_ne_zero hp
  field_simp
  ring

/-- The exact spectral energy of the actual finite-box three-block vertex. -/
theorem actualThreeBlockEnergy_eq {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m) :
    actualThreeBlockEnergy hm hpos hsum =
      3 * S (2 * m) 0 - 2 * S (2 * m) r₁ - 2 * S (2 * m) r₂ -
        2 * S (2 * m) r₃ := by
  classical
  rw [actualThreeBlockEnergy, spectral_energy (by omega)]
  let s := Finset.univ.filter fun p : Fin (2 * m) => SchurWeights.Active (2 * m) p
  have hfilter : (∑ p : Fin (2 * m), SchurWeights.weight (2 * m) p *
        normSq (realCoefficient
          (threeBlockVertex hm hpos hsum (amplitude (2 * m))) p)) =
      ∑ p ∈ s, SchurWeights.weight (2 * m) p *
        normSq (realCoefficient
          (threeBlockVertex hm hpos hsum (amplitude (2 * m))) p) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p _ hp
    have hna : ¬ SchurWeights.Active (2 * m) p := by simpa [s] using hp
    simp [SchurWeights.weight_eq_zero hna]
  rw [hfilter]
  rw [show (∑ p ∈ s, SchurWeights.weight (2 * m) p *
        normSq (realCoefficient
          (threeBlockVertex hm hpos hsum (amplitude (2 * m))) p)) =
      ∑ p ∈ s, SchurWeights.weight (2 * m) p *
        ((2 * amplitude (2 * m) / (2 * m)) ^ 2 *
          (3 - 2 * Real.cos (2 * Real.pi * (p : ℕ) * (r₁ : ℝ) / (2 * m)) -
            2 * Real.cos (2 * Real.pi * (p : ℕ) * (r₂ : ℝ) / (2 * m)) -
            2 * Real.cos (2 * Real.pi * (p : ℕ) * (r₃ : ℝ) / (2 * m))) /
          Real.sin (Real.pi * (p : ℕ) / (2 * m)) ^ 2) by
      apply Finset.sum_congr rfl
      intro p hp
      rw [active_threeBlockCoefficient_normSq hm hpos hsum p
        (Finset.mem_filter.mp hp).2]]
  let t (r : ℤ) (p : Fin (2 * m)) :=
    SchurWeights.weight (2 * m) p * (2 * amplitude (2 * m) / (2 * m)) ^ 2 *
      Real.cos (2 * Real.pi * (p : ℕ) * (r : ℝ) / (2 * m)) /
        Real.sin (Real.pi * (p : ℕ) / (2 * m)) ^ 2
  have hterm (p : Fin (2 * m)) (hp : p ∈ s) :
      SchurWeights.weight (2 * m) p *
          ((2 * amplitude (2 * m) / (2 * m)) ^ 2 *
            (3 - 2 * Real.cos (2 * Real.pi * (p : ℕ) * (r₁ : ℝ) / (2 * m)) -
              2 * Real.cos (2 * Real.pi * (p : ℕ) * (r₂ : ℝ) / (2 * m)) -
              2 * Real.cos (2 * Real.pi * (p : ℕ) * (r₃ : ℝ) / (2 * m))) /
            Real.sin (Real.pi * (p : ℕ) / (2 * m)) ^ 2) =
        3 * t 0 p - 2 * t r₁ p - 2 * t r₂ p - 2 * t r₃ p := by
    have hsine := SolIntegratedKernel.active_sine_ne_zero (Finset.mem_filter.mp hp).2
    simp [t]
    field_simp
  rw [show (∑ p ∈ s, SchurWeights.weight (2 * m) p *
        ((2 * amplitude (2 * m) / (2 * m)) ^ 2 *
          (3 - 2 * Real.cos (2 * Real.pi * (p : ℕ) * (r₁ : ℝ) / (2 * m)) -
            2 * Real.cos (2 * Real.pi * (p : ℕ) * (r₂ : ℝ) / (2 * m)) -
            2 * Real.cos (2 * Real.pi * (p : ℕ) * (r₃ : ℝ) / (2 * m))) /
          Real.sin (Real.pi * (p : ℕ) / (2 * m)) ^ 2)) =
      ∑ p ∈ s, (3 * t 0 p - 2 * t r₁ p - 2 * t r₂ p - 2 * t r₃ p) by
        exact Finset.sum_congr rfl hterm]
  simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  change (1 / 2 : ℝ) * (3 * (∑ p ∈ s, t 0 p) - 2 * (∑ p ∈ s, t r₁ p) -
      2 * (∑ p ∈ s, t r₂ p) - 2 * (∑ p ∈ s, t r₃ p)) = _
  have hS (r : ℤ) : S (2 * m) r = (1 / 2) * ∑ p ∈ s, t r p := by
    simp only [S, s, t, Nat.cast_mul, Nat.cast_ofNat]
  rw [hS, hS, hS, hS]
  ring

/-- A negative kernel margin makes an unbalanced three-block word admit an
actual two-site balancing improvement. -/
theorem exists_two_site_balancing_improvement
    {m r₁ r₂ r₃ : ℕ} (hm : 0 < m)
    (hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃) (hsum : r₁ + r₂ + r₃ = m)
    (hgap : r₂ + 2 ≤ r₁ ∨ r₁ + 2 ≤ r₂ ∨ r₃ + 2 ≤ r₂ ∨
      r₂ + 2 ≤ r₃ ∨ r₃ + 2 ≤ r₁ ∨ r₁ + 2 ≤ r₃)
    {l u : ℤ} {delta : ℝ} (hdelta : 0 ≤ delta)
    (hI₁ : (r₁ : ℤ) ∈ Set.Icc l u) (hI₂ : (r₂ : ℤ) ∈ Set.Icc l u)
    (hI₃ : (r₃ : ℤ) ∈ Set.Icc l u)
    (hmargin : ∀ x, l < x → x < u →
      finiteKernel (2 * m) (2 * Real.pi * (x : ℝ) / (2 * m)) ≤ -delta) :
    ∃ s₁ s₂ s₃ : ℕ,
      ∃ (hspos : 0 < s₁ ∧ 0 < s₂ ∧ 0 < s₃) (hssum : s₁ + s₂ + s₃ = m),
      hamming (threeBlockPattern hm hpos hsum)
        (threeBlockPattern hm hspos hssum) ≤ 2 ∧
      32 * amplitude (2 * m) ^ 2 / (2 * m : ℝ) ^ 2 * delta ≤
        actualThreeBlockEnergy hm hspos hssum -
          actualThreeBlockEnergy hm hpos hsum := by
  let kappa : ℝ := 16 * amplitude (2 * m) ^ 2 / (2 * m : ℝ) ^ 2 * delta
  have hkappa : 0 ≤ kappa := by positivity
  have hconv : ∀ x, l < x → x < u → kappa ≤ secondDifference (S (2 * m)) x := by
    intro x hl hu
    rw [SolIntegratedKernel.secondDifference_S]
    have hK := hmargin x hl hu
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hK ⊢
    have hc : 0 ≤ 16 * amplitude (2 * m) ^ 2 / (2 * m : ℝ) ^ 2 := by positivity
    have hmultiply := mul_le_mul_of_nonneg_left hK hc
    calc
      kappa = (16 * amplitude (2 * m) ^ 2 / (2 * m : ℝ) ^ 2) * delta := rfl
      _ ≤ -(16 * amplitude (2 * m) ^ 2 / (2 * m : ℝ) ^ 2) *
          finiteKernel (2 * m) (2 * Real.pi * (x : ℝ) / (2 * m)) := by linarith
      _ = -16 * amplitude (2 * m) ^ 2 / (2 * m : ℝ) ^ 2 *
          finiteKernel (2 * m) (2 * Real.pi * (x : ℝ) / (2 * m)) := by ring
  rcases exists_balancing_transfer_with_value_gain hm hpos hsum hgap
      (C := 3 * S (2 * m) 0) (g := S (2 * m)) (κ := kappa)
      hkappa hconv hI₁ hI₂ hI₃ with
    ⟨s₁, s₂, s₃, hspos, hssum, hham, hgain⟩
  refine ⟨s₁, s₂, s₃, hspos, hssum, hham, ?_⟩
  rw [actualThreeBlockEnergy_eq hm (r₁ := s₁) (r₂ := s₂) (r₃ := s₃)
      hspos hssum,
    actualThreeBlockEnergy_eq hm hpos hsum]
  change 2 * kappa ≤ _ at hgain
  dsimp [threeBlockValue] at hgain
  dsimp [kappa] at hgain ⊢
  convert hgain using 1 <;> ring


end
end StructuralNote.SolThreeBlockEnergy
