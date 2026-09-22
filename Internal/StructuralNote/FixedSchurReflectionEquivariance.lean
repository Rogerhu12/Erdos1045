import StructuralNote.FixedSchurCyclicEquivariance

/-! Exact reflection equivariance for the actual fixed-Schur coordinates.

Vertex fields use the index `-j`, while oriented edge fields use `-j-1`.
Keeping these two permutations separate records the orientation reversal which
changes the sign of the normal coordinate but not the tangent coordinate.
-/

namespace StructuralNote.FixedSchurReflectionEquivariance

open scoped BigOperators Topology

open Complex Filter
open Erdos1045 Erdos1045.EventualExact
open FourierMultiplier FiniteFourierLift FiniteBox SchurLift SchurSpectrum
open StructuralNote.CommonFiberGeometry
open StructuralNote.CommonDomainClosure
open StructuralNote.CommonTangentialParameters
open StructuralNote.EdgeCoordinates
open StructuralNote.FixedSchurData
open StructuralNote.FixedSchurLinear
open StructuralNote.FixedSchurDomainSmallness
open StructuralNote.FixedSchurEquations
open StructuralNote.FixedSchurChart
open StructuralNote.SignPatternSymmetry
open StructuralNote.SignedPressureRemainder
open StructuralNote.FixedSchurCyclicEquivariance

noncomputable section

local notation "conj" => (starRingEnd ℂ)

theorem conj_div (a b : ℂ) : conj (a / b) = conj a / conj b := by
  exact map_div₀ (starRingEnd ℂ) a b

theorem conj_neg (a : ℂ) : conj (-a) = -conj a := by
  exact (starRingEnd ℂ).map_neg a

def vertexReflection (n : ℕ) : Equiv.Perm (Fin n) := Equiv.neg (Fin n)

def edgeReflection (n : ℕ) : Equiv.Perm (Fin n) :=
  (finRotate n).trans (Equiv.neg (Fin n))

def reflectReal {n : ℕ} (f : Fin n → ℝ) : Fin n → ℝ :=
  fun j => -f (vertexReflection n j)

def reflectCenter {n : ℕ} (C : Fin n → ℂ) : Fin n → ℂ :=
  fun j => conj (C (vertexReflection n j))

def reflectNormal {n : ℕ} (q : Fin n → ℝ) : Fin n → ℝ :=
  fun j => -q (edgeReflection n j)

def reflectTangent {n : ℕ} (p : Fin n → ℝ) : Fin n → ℝ :=
  fun j => p (edgeReflection n j)

@[simp] theorem vertexReflection_apply {n : ℕ} (j : Fin n) :
    vertexReflection n j = -j := rfl

@[simp] theorem edgeReflection_apply {n : ℕ} (j : Fin n) :
    edgeReflection n j = -(finRotate n j) := rfl

theorem successor_edgeReflection {n : ℕ} (hn : 2 ≤ n) (j : Fin n) :
    successor (by omega) (edgeReflection n j) = vertexReflection n j := by
  rw [← finRotate_eq_successor hn]
  let : NeZero n := ⟨by omega⟩
  simp only [edgeReflection_apply, vertexReflection_apply, finRotate_apply]
  abel

theorem edgeReflection_involutive {n : ℕ} (hn : 2 ≤ n) :
    Function.Involutive (edgeReflection n) := by
  intro j
  let : NeZero n := ⟨by omega⟩
  simp only [edgeReflection_apply, finRotate_apply]
  abel

theorem vertexReflection_successor {n : ℕ} (hn : 2 ≤ n) (j : Fin n) :
    vertexReflection n (successor (by omega) j) = edgeReflection n j := by
  rw [← finRotate_eq_successor hn]
  rfl

def middle {m : ℕ} (hm : 0 < m) : Fin (2 * m) := ⟨m, by omega⟩

theorem halfTurn_eq_add {m : ℕ} (hm : 0 < m) (j : Fin (2 * m)) :
    halfTurn hm j = j + middle hm := by
  apply Fin.ext
  rfl

theorem halfTurn_middle_neg {m : ℕ} (hm : 0 < m) :
    -(middle hm) = middle hm := by
  let : NeZero (2 * m) := ⟨by omega⟩
  have hne : middle hm ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [middle, Fin.val_zero] at hv
    omega
  apply Fin.ext
  rw [Fin.val_neg, if_neg hne]
  simp only [middle]
  omega

theorem halfTurnCommuting_edgeReflection {m : ℕ} (hm : 0 < m) :
    halfTurnCommuting hm (edgeReflection (2 * m)) := by
  intro j
  let : NeZero (2 * m) := ⟨by omega⟩
  rw [halfTurn_eq_add, halfTurn_eq_add]
  simp only [edgeReflection_apply, finRotate_apply, neg_add_rev,
    halfTurn_middle_neg hm]
  abel

def reflectPattern {m : ℕ} {hm : 0 < m} (s : SignPattern hm) : SignPattern hm :=
  globalNegate (reindex (edgeReflection (2 * m))
    (halfTurnCommuting_edgeReflection hm) s)

@[simp] theorem patternSign_reflectPattern {m : ℕ} {hm : 0 < m}
    (s : SignPattern hm) (j : Fin (2 * m)) :
    patternSign (reflectPattern s) j = -patternSign s (edgeReflection (2 * m) j) := by
  simp only [reflectPattern, patternSign_globalNegate, patternSign_reindex]

theorem character_vertexReflection {n : ℕ} (hn : 2 ≤ n) (j : Fin n) :
    character n 1 (vertexReflection n j) = conj (character n 1 j) := by
  let : NeZero n := ⟨by omega⟩
  simpa only [vertexReflection_apply, character, Nat.mul_one, Nat.one_mul] using
    character_neg j 1

theorem root_eq_phase_sq (n : ℕ) :
    LocalPhase.regularRoot n = LocalPhase.phase n 1 ^ 2 := by
  unfold LocalPhase.regularRoot LocalPhase.phase
  rw [pow_two, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phase_mul_conj_root (n : ℕ) :
    LocalPhase.phase n 1 * conj (LocalPhase.regularRoot n) =
      conj (LocalPhase.phase n 1) := by
  rw [root_eq_phase_sq, map_pow, pow_two]
  have hu := phase_mul_conj n 1
  calc
    LocalPhase.phase n 1 *
        (conj (LocalPhase.phase n 1) * conj (LocalPhase.phase n 1)) =
      (LocalPhase.phase n 1 * conj (LocalPhase.phase n 1)) *
        conj (LocalPhase.phase n 1) := by ring
    _ = _ := by rw [hu, one_mul]

theorem frame_edgeReflection {n : ℕ} (hn : 2 ≤ n) (j : Fin n) :
    frame n (edgeReflection n j) = conj (frame n j) := by
  have hc := character_vertexReflection hn (finRotate n j)
  have hr := character_successor (show 0 < n by omega)
    (⟨1, by omega⟩ : Fin n) j
  have hr' : character n 1 (finRotate n j) =
      character n 1 j * LocalPhase.regularRoot n := by
    rw [finRotate_eq_successor hn]
    simpa only [Fin.val_one, pow_one] using hr
  have hc' : character n 1 ((-(finRotate n j) : Fin n) : ℕ) =
      conj (character n 1 (finRotate n j)) := by
    simpa only [vertexReflection_apply] using hc
  simp only [edgeReflection_apply, frame]
  rw [hc', hr']
  simp only [map_mul]
  calc
    LocalPhase.phase n 1 *
        (conj (character n 1 j) * conj (LocalPhase.regularRoot n)) =
      (LocalPhase.phase n 1 * conj (LocalPhase.regularRoot n)) *
        conj (character n 1 j) := by ring
    _ = _ := by rw [phase_mul_conj_root]

theorem diameterVector_reflect {n : ℕ} (hn : 2 ≤ n) (θ : Fin n → ℝ) :
    diameterVector (reflectReal θ) = reflectCenter (diameterVector θ) := by
  funext j
  simp only [diameterVector, reflectReal, reflectCenter,
    character_vertexReflection hn, map_mul, conj_conj]
  unfold LensClosure.unit
  rw [← exp_conj]
  congr 1
  apply Complex.ext <;> simp

theorem difference_reflectCenter {n : ℕ} (hn : 2 ≤ n) (C : Fin n → ℂ) :
    difference (by omega) (reflectCenter C) =
      fun j => -conj (difference (by omega) C (edgeReflection n j)) := by
  funext j
  simp only [difference, reflectCenter]
  rw [vertexReflection_successor hn, successor_edgeReflection hn]
  simp only [map_sub]
  ring

theorem reference_difference_edgeReflection {n : ℕ} (hn : 2 ≤ n)
    (j : Fin n) :
    difference (by omega) (fun j => character n 1 j) (edgeReflection n j) =
      -conj (difference (by omega) (fun j => character n 1 j) j) := by
  rw [reference_difference, reference_difference, frame_edgeReflection hn]
  simp only [map_mul, Complex.conj_ofReal, conj_I]
  ring

theorem edgeRatio_reflectCenter {n : ℕ} (hn : 2 ≤ n) (C : Fin n → ℂ) :
    edgeRatio (by omega) (reflectCenter C) =
      fun j => conj (edgeRatio (by omega) C (edgeReflection n j)) := by
  funext j
  rw [edgeRatio_eq_difference, difference_reflectCenter hn,
    edgeRatio_eq_difference, reference_difference_edgeReflection hn]
  rw [conj_div, conj_neg, conj_conj]
  ring

theorem normal_reflectCenter {n : ℕ} (hn : 2 ≤ n) (C : Fin n → ℂ) :
    normal (by omega) (reflectCenter C) = reflectNormal (normal (by omega) C) := by
  funext j
  simp only [normal, reflectNormal, edgeRatio_reflectCenter hn, Complex.conj_im]
  ring

theorem tangent_reflectCenter {n : ℕ} (hn : 2 ≤ n) (C : Fin n → ℂ) :
    tangent (by omega) (reflectCenter C) = reflectTangent (tangent (by omega) C) := by
  funext j
  simp only [tangent, reflectTangent, edgeRatio_reflectCenter hn, Complex.conj_re]

theorem sum_reflectCenter {n : ℕ} (C : Fin n → ℂ) :
    (∑ j, reflectCenter C j) = conj (∑ j, C j) := by
  simp only [reflectCenter, ← map_sum]
  exact congrArg conj (Equiv.sum_comp (vertexReflection n) C)

theorem firstCoefficient_reflectNormal {n : ℕ} (hn : 2 ≤ n)
    (q : Fin n → ℝ) :
    firstCoefficient (reflectNormal q) = -conj (firstCoefficient q) := by
  have hterm (j : Fin n) :
      ((reflectNormal q j : ℝ) : ℂ) * conj (frame n j) =
        -conj (((q (edgeReflection n j) : ℝ) : ℂ) *
          conj (frame n (edgeReflection n j))) := by
    simp only [reflectNormal, frame_edgeReflection hn, map_mul,
      Complex.conj_ofReal, Complex.ofReal_neg, conj_conj]
    ring
  unfold firstCoefficient
  simp_rw [hterm]
  rw [Finset.sum_neg_distrib, ← map_sum,
    Equiv.sum_comp (edgeReflection n)
      (fun j => ((q j : ℝ) : ℂ) * conj (frame n j))]
  rw [conj_div]
  have hnconj : conj (n : ℂ) = (n : ℂ) := map_natCast (starRingEnd ℂ) n
  rw [hnconj]
  ring

theorem J_reflectNormal {n : ℕ} (hn : 2 ≤ n) (q : Fin n → ℝ) :
    J (reflectNormal q) = reflectTangent (J q) := by
  funext j
  simp only [J, reflectTangent, firstCoefficient_reflectNormal hn,
    frame_edgeReflection hn]
  have he : -conj (firstCoefficient q) * frame n j =
      -conj (firstCoefficient q * conj (frame n j)) := by
    simp only [map_mul, conj_conj]
    ring
  rw [he, Complex.neg_im, Complex.conj_im]
  ring

theorem increment_eq_edgeIncrement {n : ℕ} (q : Fin n → ℝ) :
    increment q = edgeIncrement q (J q) := by
  funext j
  simp only [increment, edgeIncrement, J]
  push_cast
  ring

theorem edgeIncrement_reflect {n : ℕ} (hn : 2 ≤ n)
    (q p : Fin n → ℝ) :
    edgeIncrement (reflectNormal q) (reflectTangent p) =
      fun j => -conj (edgeIncrement q p (edgeReflection n j)) := by
  funext j
  simp only [edgeIncrement, reflectNormal, reflectTangent,
    frame_edgeReflection hn, map_mul, Complex.conj_ofReal, Complex.ofReal_neg,
    map_add, conj_I, conj_conj, neg_mul]
  push_cast
  ring

theorem increment_reflectNormal {n : ℕ} (hn : 2 ≤ n) (q : Fin n → ℝ) :
    increment (reflectNormal q) =
      fun j => -conj (increment q (edgeReflection n j)) := by
  rw [increment_eq_edgeIncrement, J_reflectNormal hn,
    edgeIncrement_reflect hn, ← increment_eq_edgeIncrement]

theorem canonicalLift_reflectNormal {n : ℕ} (hn : 3 ≤ n) (q : Fin n → ℝ) :
    reflectCenter (canonicalLift q) = canonicalLift (reflectNormal q) := by
  apply canonicalLift_unique hn (reflectNormal q)
  · rw [sum_reflectCenter, canonicalLift_mean_zero (show 0 < n by omega)]
    simp
  · rw [difference_reflectCenter (show 2 ≤ n by omega),
      canonicalLift_difference hn,
      increment_reflectNormal (show 2 ≤ n by omega)]

theorem projection_reflectCenter {m : ℕ} (hm : 2 ≤ m)
    (C : Fin (2 * m) → ℂ) :
    projection hm (reflectCenter C) = reflectCenter (projection hm C) := by
  have hc := normal_reflectCenter (show 2 ≤ 2 * m by omega) C
  rw [normal_eq_constraint hm, normal_eq_constraint hm] at hc
  unfold projection
  rw [hc, ← canonicalLift_reflectNormal (show 3 ≤ 2 * m by omega)]
  funext j
  simp only [reflectCenter, Pi.sub_apply, map_sub]

theorem center_reflect {m : ℕ} (hm : 2 ≤ m)
    (q : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) :
    reflectCenter (FixedSchurLinear.center q v) =
      FixedSchurLinear.center (reflectNormal q) (reflectCenter v) := by
  unfold FixedSchurLinear.center
  rw [← canonicalLift_reflectNormal (show 3 ≤ 2 * m by omega)]
  funext j
  simp only [reflectCenter, Pi.add_apply, map_add]

theorem chordField_reflect {n : ℕ} (hn : 2 ≤ n) (θ : Fin n → ℝ) :
    chordField (by omega) (reflectReal θ) =
      fun j => conj (chordField (by omega) θ (edgeReflection n j)) := by
  funext j
  have hd := congrFun (diameterVector_reflect hn θ) j
  have hds := congrFun (diameterVector_reflect hn θ)
    (successor (by omega) j)
  simp only [chordField]
  rw [hd, hds]
  simp only [reflectCenter]
  rw [vertexReflection_successor hn,
    successor_edgeReflection hn, frame_edgeReflection hn]
  simp only [map_mul, map_add, conj_conj]
  ring

theorem X_reflect {n : ℕ} (hn : 2 ≤ n) (θ : Fin n → ℝ) :
    X (by omega) (reflectReal θ) =
      fun j => X (by omega) θ (edgeReflection n j) := by
  funext j
  simp only [X]
  rw [chordField_reflect hn, Complex.conj_re]

theorem Y_reflect {n : ℕ} (hn : 2 ≤ n) (θ : Fin n → ℝ) :
    Y (by omega) (reflectReal θ) =
      fun j => -Y (by omega) θ (edgeReflection n j) := by
  funext j
  simp only [Y]
  rw [chordField_reflect hn, Complex.conj_im]

theorem rootValue_reflect (σ ε X Y p : ℝ) :
    FixedSchurScalarRoot.rootValue (-σ) ε X (-Y) p =
      -FixedSchurScalarRoot.rootValue σ ε X Y p := by
  unfold FixedSchurScalarRoot.rootValue
  rw [show (-Y + -σ * ε * p) ^ 2 = (Y + σ * ε * p) ^ 2 by ring]
  ring

theorem equationMap_reflect {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (σ q : Fin (2 * m) → ℝ) :
    equationMap hm (reflectReal θ) (reflectCenter v)
        (reflectNormal σ) (reflectNormal q) =
      reflectNormal (equationMap hm θ v σ q) := by
  funext j
  simp only [equationMap, FixedSchurContraction.crossingMap, reflectNormal,
    X_reflect (show 2 ≤ 2 * m by omega),
    Y_reflect (show 2 ≤ 2 * m by omega),
    tangent_reflectCenter (show 2 ≤ 2 * m by omega),
    J_reflectNormal (show 2 ≤ 2 * m by omega)]
  exact rootValue_reflect _ _ _ _ _

theorem halfTurnCommuting_vertexReflection {m : ℕ} (hm : 0 < m) :
    halfTurnCommuting hm (vertexReflection (2 * m)) := by
  let : NeZero (2 * m) := ⟨by omega⟩
  intro j
  rw [halfTurn_eq_add, halfTurn_eq_add]
  change -(j + middle hm) = -j + middle hm
  calc
    _ = -(middle hm) + -j := neg_add_rev _ _
    _ = _ := by rw [halfTurn_middle_neg]; abel

theorem halfPeriodic_reflectCenter {m : ℕ} (hm : 0 < m)
    (C : Fin (2 * m) → ℂ) (hC : HalfPeriodic hm C) :
    HalfPeriodic hm (reflectCenter C) := by
  intro j
  simp only [reflectCenter]
  rw [halfTurnCommuting_vertexReflection hm, hC]

theorem halfPeriodic_reflectReal {m : ℕ} (hm : 0 < m)
    (q : Fin (2 * m) → ℝ) (hq : HalfPeriodic hm (fun j => (q j : ℂ))) :
    HalfPeriodic hm (fun j => ((reflectReal q j : ℝ) : ℂ)) := by
  intro j
  simp only [reflectReal, Complex.ofReal_neg]
  rw [halfTurnCommuting_vertexReflection hm]
  exact congrArg (fun z : ℂ => -z) (hq (vertexReflection (2 * m) j))

theorem root_vertexReflection {n : ℕ} (hn : 2 ≤ n) (j : Fin n) :
    SignedPressureAngular.root n (vertexReflection n j) =
      conj (SignedPressureAngular.root n j) := by
  simpa only [SignedPressureAngular.root, character, Nat.mul_one] using
    character_vertexReflection hn j

theorem root_chord_vertexReflection {n : ℕ} (hn : 2 ≤ n) (i j : Fin n) :
    Complex.normSq (SignedPressureAngular.root n (vertexReflection n i) -
        SignedPressureAngular.root n (vertexReflection n j)) =
      Complex.normSq (SignedPressureAngular.root n i -
        SignedPressureAngular.root n j) := by
  rw [root_vertexReflection hn, root_vertexReflection hn, ← map_sub,
    Complex.normSq_conj]

theorem pairEnergy_vertexReindex {n : ℕ} (hn : 2 ≤ n) (C : Fin n → ℂ) :
    pairEnergy (by omega) (fun j => C (vertexReflection n j)) =
      pairEnergy (by omega) C :=
  SignedPressureAngular.pairEnergy_perm (by omega) (vertexReflection n)
    (root_chord_vertexReflection hn) C

theorem pairEnergy_reflectCenter {n : ℕ} (hn : 2 ≤ n) (C : Fin n → ℂ) :
    pairEnergy (by omega) (reflectCenter C) = pairEnergy (by omega) C := by
  rw [AngularObjectiveCurvature.pairEnergy_eq_chord_sum,
    AngularObjectiveCurvature.pairEnergy_eq_chord_sum]
  simp only [reflectCenter, ← map_sub, Complex.normSq_conj]
  simpa only [AngularObjectiveCurvature.pairEnergy_eq_chord_sum] using
    pairEnergy_vertexReindex hn C

theorem pairEnergy_reflectReal {n : ℕ} (hn : 2 ≤ n) (q : Fin n → ℝ) :
    pairEnergy (by omega) (fun j => ((reflectReal q j : ℝ) : ℂ)) =
      pairEnergy (by omega) (fun j => (q j : ℂ)) := by
  calc
    pairEnergy (by omega) (fun j => ((reflectReal q j : ℝ) : ℂ)) =
        pairEnergy (by omega) (fun j => (q (vertexReflection n j) : ℂ)) := by
      rw [AngularObjectiveCurvature.pairEnergy_eq_chord_sum,
        AngularObjectiveCurvature.pairEnergy_eq_chord_sum]
      apply congrArg (fun x : ℝ => x / 2)
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [show ((reflectReal q i : ℝ) : ℂ) - (reflectReal q j : ℂ) =
          -((q (vertexReflection n i) : ℂ) -
            (q (vertexReflection n j) : ℂ)) by
        simp only [reflectReal, Complex.ofReal_neg]
        ring,
        Complex.normSq_neg]
    _ = pairEnergy (by omega) (fun j => (q j : ℂ)) :=
      pairEnergy_vertexReindex hn (fun j => (q j : ℂ))

theorem parameterSpace_reflectCenter {m : ℕ} (hm : 2 ≤ m)
    (v : Fin (2 * m) → ℂ) (hv : ParameterSpace (by omega) v) :
    ParameterSpace (by omega) (reflectCenter v) := by
  refine ⟨halfPeriodic_reflectCenter (by omega) v hv.1, ?_, ?_⟩
  · rw [sum_reflectCenter, hv.2.1]
    simp
  · have hc := normal_reflectCenter (show 2 ≤ 2 * m by omega) v
    rw [normal_eq_constraint hm, normal_eq_constraint hm, hv.2.2] at hc
    have hz : reflectNormal (0 : Fin (2 * m) → ℝ) = 0 := by
      funext j
      simp only [reflectNormal, Pi.zero_apply, neg_zero]
    rw [hz] at hc
    exact hc

theorem inDomain_reflect {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (hdom : InDomain (by omega) θ v) :
    InDomain (by omega) (reflectReal θ) (reflectCenter v) := by
  refine ⟨halfPeriodic_reflectReal (by omega) θ hdom.1, ?_,
    parameterSpace_reflectCenter hm v hdom.2.2.1, ?_⟩
  · change (∑ j, ((-θ (vertexReflection (2 * m) j) : ℝ) : ℂ)) = 0
    simp only [Complex.ofReal_neg, Finset.sum_neg_distrib]
    rw [Equiv.sum_comp (vertexReflection (2 * m)) (fun j => (θ j : ℂ)),
      hdom.2.1, neg_zero]
  · rw [pairEnergy_reflectReal (show 2 ≤ 2 * m by omega),
      pairEnergy_reflectCenter (show 2 ≤ 2 * m by omega)]
    exact hdom.2.2.2

theorem selectedWord_reflect {m : ℕ} {hm : 0 < m} (s : SignPattern hm) :
    patternSign (reflectPattern s) = reflectNormal (patternSign s) := by
  funext j
  exact patternSign_reflectPattern s j

theorem baseWord_reflect {n : ℕ} (σ : Fin n → ℝ) :
    baseWord (reflectNormal σ) = reflectNormal (baseWord σ) := by
  funext j
  simp only [baseWord, reflectNormal]
  ring

theorem norm_reflectNormal {n : ℕ} (hn : 2 ≤ n) (q : Fin n → ℝ) :
    ‖reflectNormal q‖ = ‖q‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg q)).2
    intro j
    have h := norm_le_pi_norm q (edgeReflection n j)
    simpa only [reflectNormal, Real.norm_eq_abs, abs_neg] using h
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (reflectNormal q))).2
    intro j
    have h := norm_le_pi_norm (reflectNormal q) (edgeReflection n j)
    rw [reflectNormal, edgeReflection_involutive hn j,
      Real.norm_eq_abs, abs_neg] at h
    exact h

theorem norm_reflectNormal_sub {n : ℕ} (hn : 2 ≤ n)
    (q r : Fin n → ℝ) :
    ‖reflectNormal q - reflectNormal r‖ = ‖q - r‖ := by
  rw [show reflectNormal q - reflectNormal r = reflectNormal (q - r) by
    funext j
    simp only [reflectNormal, Pi.sub_apply]
    ring,
    norm_reflectNormal hn]

theorem eventual_coordinate_reflect : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v →
      coordinate (by omega) (reflectPattern s) (reflectReal θ) (reflectCenter v) =
        reflectNormal (coordinate (by omega) s θ v) := by
  filter_upwards [eventual_coordinate_spec, eventual_coordinate_unique]
    with m hspec huniq
  intro hm s θ v hdom
  have hs := hspec (by omega) s θ v hdom
  symm
  apply huniq (by omega) (reflectPattern s) (reflectReal θ) (reflectCenter v)
    (inDomain_reflect hm θ v hdom) (reflectNormal (coordinate (by omega) s θ v))
  · rw [selectedWord_reflect, baseWord_reflect,
      norm_reflectNormal_sub (show 2 ≤ 2 * m by omega)]
    exact hs.1
  · rw [selectedWord_reflect, equationMap_reflect, hs.2]

theorem eventual_chosenCenter_reflect : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v →
      FixedSchurLinear.center
          (coordinate (by omega) (reflectPattern s) (reflectReal θ)
            (reflectCenter v))
          (reflectCenter v) =
        reflectCenter (FixedSchurLinear.center
          (coordinate (by omega) s θ v) v) := by
  filter_upwards [eventual_coordinate_reflect] with m heq
  intro hm s θ v hdom
  rw [heq hm s θ v hdom, ← center_reflect hm]

theorem eventual_configuration_reflect : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v →
      FixedSchurChart.configuration (by omega) (reflectPattern s)
          (reflectReal θ) (reflectCenter v) =
        reflectCenter (FixedSchurChart.configuration (by omega) s θ v) := by
  filter_upwards [eventual_coordinate_reflect] with m heq
  intro hm s θ v hdom
  funext j
  unfold FixedSchurChart.configuration FixedSchurEdgeGeometry.vertex
  rw [heq hm s θ v hdom]
  have hd := congrFun
    (diameterVector_reflect (show 2 ≤ 2 * m by omega) θ) j
  have hc := congrFun (center_reflect hm (coordinate (by omega) s θ v) v) j
  rw [hd, ← hc]
  simp only [reflectCenter, map_add]

theorem eventual_chosen_normal_reflect : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v →
      normal (by omega)
          (FixedSchurLinear.center
            (coordinate (by omega) (reflectPattern s) (reflectReal θ)
              (reflectCenter v))
            (reflectCenter v)) =
        reflectNormal (normal (by omega)
          (FixedSchurLinear.center (coordinate (by omega) s θ v) v)) := by
  filter_upwards [eventual_chosenCenter_reflect] with m heq
  intro hm s θ v hdom
  rw [heq hm s θ v hdom,
    normal_reflectCenter (show 2 ≤ 2 * m by omega)]

theorem eventual_chosen_tangent_reflect : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v →
      tangent (by omega)
          (FixedSchurLinear.center
            (coordinate (by omega) (reflectPattern s) (reflectReal θ)
              (reflectCenter v))
            (reflectCenter v)) =
        reflectTangent (tangent (by omega)
          (FixedSchurLinear.center (coordinate (by omega) s θ v) v)) := by
  filter_upwards [eventual_chosenCenter_reflect] with m heq
  intro hm s θ v hdom
  rw [heq hm s θ v hdom,
    tangent_reflectCenter (show 2 ≤ 2 * m by omega)]

end
end StructuralNote.FixedSchurReflectionEquivariance
