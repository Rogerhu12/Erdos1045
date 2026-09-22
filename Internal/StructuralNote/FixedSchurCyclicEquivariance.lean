import StructuralNote.FixedSchurChart
import StructuralNote.SignPatternSymmetry
import StructuralNote.SignedPressureAngular

/-! Exact equivariance of the fixed-Schur coordinates under cyclic relabeling.

The center action includes the compensating rotation by the inverse `k`-th
root of unity.  All statements are exact finite identities; the only eventual
statement is the one which invokes existence and uniqueness of the chosen
nonlinear coordinate.
-/

namespace StructuralNote.FixedSchurCyclicEquivariance

open scoped BigOperators Topology

open Complex Filter
open Erdos1045 Erdos1045.EventualExact
open Erdos1045.EventualExact.FourierMultiplier
open Erdos1045.EventualExact.FiniteFourierLift
open Erdos1045.EventualExact.FiniteBox
open Erdos1045.EventualExact.SchurLift
open Erdos1045.EventualExact.SchurSpectrum
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
open StructuralNote.SignedPressureAngular
open StructuralNote.SignedPressureRemainder
open Erdos1045.EventualExact.AngularObjectiveCurvature

noncomputable section

local notation "conj" => (starRingEnd ℂ)

def cyclicIndex (n k : ℕ) : Equiv.Perm (Fin n) := (finRotate n) ^ k

def cyclicReal {n : ℕ} (k : ℕ) (f : Fin n → ℝ) : Fin n → ℝ :=
  fun j => f (cyclicIndex n k j)

def cyclicCenter {n : ℕ} (k : ℕ) (C : Fin n → ℂ) : Fin n → ℂ :=
  fun j => conj (LocalPhase.regularRoot n ^ k) * C (cyclicIndex n k j)

@[simp] theorem cyclicIndex_zero (n : ℕ) : cyclicIndex n 0 = 1 := by
  simp [cyclicIndex]

theorem finRotate_successor {n : ℕ} (hn : 2 ≤ n) (j : Fin n) :
    finRotate n (successor (by omega) j) = successor (by omega) (finRotate n j) := by
  rw [← finRotate_eq_successor hn, ← finRotate_eq_successor hn]

theorem cyclicIndex_successor {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (j : Fin n) :
    cyclicIndex n k (successor (by omega) j) =
      successor (by omega) (cyclicIndex n k j) := by
  induction k generalizing j with
  | zero => simp [cyclicIndex]
  | succ k ih =>
      rw [cyclicIndex, pow_succ]
      change ((finRotate n) ^ k) (finRotate n (successor (by omega) j)) = _
      rw [finRotate_successor hn, show ((finRotate n) ^ k)
        (successor (by omega) (finRotate n j)) =
          cyclicIndex n k (successor (by omega) (finRotate n j)) by rfl,
        ih]
      rfl

theorem frame_finRotate {n : ℕ} (hn : 2 ≤ n) (j : Fin n) :
    frame n (finRotate n j) = frame n j * LocalPhase.regularRoot n := by
  rw [finRotate_eq_successor hn]
  have hc := character_successor (show 0 < n by omega) (⟨1, by omega⟩ : Fin n) j
  have hc' : character n 1 (successor (by omega) j) =
      character n 1 j * LocalPhase.regularRoot n := by
    simpa only [Fin.val_one, pow_one] using hc
  unfold frame
  rw [hc']
  ring

theorem frame_cyclicIndex {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (j : Fin n) :
    frame n (cyclicIndex n k j) =
      frame n j * LocalPhase.regularRoot n ^ k := by
  induction k generalizing j with
  | zero => simp [cyclicIndex]
  | succ k ih =>
      rw [cyclicIndex, pow_succ]
      change frame n (((finRotate n) ^ k) (finRotate n j)) = _
      rw [show ((finRotate n) ^ k) (finRotate n j) =
          cyclicIndex n k (finRotate n j) by rfl,
        ih (finRotate n j), frame_finRotate hn]
      rw [pow_succ]
      ring

theorem root_pow_mul_conj (n k : ℕ) :
    LocalPhase.regularRoot n ^ k * conj (LocalPhase.regularRoot n ^ k) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow,
    ClosedFourier.root_norm]
  norm_num

theorem conj_root_pow_mul (n k : ℕ) :
    conj (LocalPhase.regularRoot n ^ k) * LocalPhase.regularRoot n ^ k = 1 := by
  rw [mul_comm, root_pow_mul_conj]

theorem cyclicReal_comp {n : ℕ} (k l : ℕ) (f : Fin n → ℝ) :
    cyclicReal l (cyclicReal k f) = cyclicReal (k + l) f := by
  funext j
  simp only [cyclicReal, cyclicIndex, pow_add, Equiv.Perm.mul_apply]

theorem cyclicCenter_comp {n : ℕ} (k l : ℕ) (C : Fin n → ℂ) :
    cyclicCenter l (cyclicCenter k C) = cyclicCenter (k + l) C := by
  funext j
  simp only [cyclicCenter, cyclicIndex, pow_add, Equiv.Perm.mul_apply, map_mul]
  ring

theorem sum_cyclicReal {n : ℕ} (k : ℕ) (f : Fin n → ℝ) :
    (∑ j, cyclicReal k f j) = ∑ j, f j := by
  exact Equiv.sum_comp (cyclicIndex n k) f

theorem sum_cyclicCenter {n : ℕ} (k : ℕ) (C : Fin n → ℂ) :
    (∑ j, cyclicCenter k C j) =
      conj (LocalPhase.regularRoot n ^ k) * ∑ j, C j := by
  simp only [cyclicCenter, ← Finset.mul_sum]
  rw [Equiv.sum_comp (cyclicIndex n k) C]

theorem difference_cyclicCenter {n : ℕ} (hn : 2 ≤ n) (k : ℕ)
    (C : Fin n → ℂ) :
    difference (by omega) (cyclicCenter k C) =
      fun j => conj (LocalPhase.regularRoot n ^ k) *
        difference (by omega) C (cyclicIndex n k j) := by
  funext j
  simp only [difference, cyclicCenter]
  rw [cyclicIndex_successor hn]
  ring

theorem constraint_cyclicCenter {n : ℕ} (hn : 2 ≤ n) (k : ℕ)
    (C : Fin n → ℂ) :
    constraint (by omega) (cyclicCenter k C) = cyclicReal k (constraint (by omega) C) := by
  funext j
  simp only [constraint, cyclicReal]
  rw [difference_cyclicCenter hn, frame_cyclicIndex hn]
  simp only [map_mul]
  ring

theorem edgeRatio_cyclicCenter {n : ℕ} (hn : 2 ≤ n) (k : ℕ)
    (C : Fin n → ℂ) :
    edgeRatio (by omega) (cyclicCenter k C) =
      fun j => edgeRatio (by omega) C (cyclicIndex n k j) := by
  funext j
  rw [edgeRatio_eq_difference, difference_cyclicCenter hn,
    edgeRatio_eq_difference, reference_difference, reference_difference,
    frame_cyclicIndex hn]
  have hz : LocalPhase.regularRoot n ^ k ≠ 0 :=
    pow_ne_zero _ (Complex.exp_ne_zero _)
  have ha : ((2 * Real.sin (Real.pi / n) : ℝ) : ℂ) * I * frame n j ≠ 0 := by
    simpa only [reference_difference] using reference_difference_ne_zero hn j
  simp only
  rw [show ((2 * Real.sin (Real.pi / n) : ℝ) : ℂ) * I *
      (frame n j * LocalPhase.regularRoot n ^ k) =
      (((2 * Real.sin (Real.pi / n) : ℝ) : ℂ) * I * frame n j) *
        LocalPhase.regularRoot n ^ k by ring]
  apply (div_eq_div_iff ha (mul_ne_zero ha hz)).2
  rw [show (conj (LocalPhase.regularRoot n ^ k) *
          difference (by omega) C (cyclicIndex n k j)) *
        ((((2 * Real.sin (Real.pi / n) : ℝ) : ℂ) * I * frame n j) *
          LocalPhase.regularRoot n ^ k) =
      (conj (LocalPhase.regularRoot n ^ k) * LocalPhase.regularRoot n ^ k) *
        (difference (by omega) C (cyclicIndex n k j) *
          (((2 * Real.sin (Real.pi / n) : ℝ) : ℂ) * I * frame n j)) by ring,
    conj_root_pow_mul, one_mul]

theorem normal_cyclicCenter {n : ℕ} (hn : 2 ≤ n) (k : ℕ)
    (C : Fin n → ℂ) :
    normal (by omega) (cyclicCenter k C) = cyclicReal k (normal (by omega) C) := by
  funext j
  simp only [normal, cyclicReal, edgeRatio_cyclicCenter hn]

theorem tangent_cyclicCenter {n : ℕ} (hn : 2 ≤ n) (k : ℕ)
    (C : Fin n → ℂ) :
    tangent (by omega) (cyclicCenter k C) = cyclicReal k (tangent (by omega) C) := by
  funext j
  simp only [tangent, cyclicReal, edgeRatio_cyclicCenter hn]

theorem firstCoefficient_cyclicReal {n : ℕ} (hn : 2 ≤ n) (k : ℕ)
    (q : Fin n → ℝ) :
    firstCoefficient (cyclicReal k q) =
      LocalPhase.regularRoot n ^ k * firstCoefficient q := by
  have hterm (j : Fin n) :
      ((cyclicReal k q j : ℝ) : ℂ) * conj (frame n j) =
        LocalPhase.regularRoot n ^ k *
          (((q (cyclicIndex n k j) : ℝ) : ℂ) *
            conj (frame n (cyclicIndex n k j))) := by
    simp only [cyclicReal, frame_cyclicIndex hn, map_mul]
    rw [show LocalPhase.regularRoot n ^ k *
          ((q (cyclicIndex n k j) : ℂ) *
            (conj (frame n j) * conj (LocalPhase.regularRoot n ^ k))) =
        (LocalPhase.regularRoot n ^ k *
          conj (LocalPhase.regularRoot n ^ k)) *
            ((q (cyclicIndex n k j) : ℂ) * conj (frame n j)) by ring,
      root_pow_mul_conj, one_mul]
  unfold firstCoefficient
  simp_rw [hterm]
  rw [← Finset.mul_sum,
    Equiv.sum_comp (cyclicIndex n k)
      (fun j => ((q j : ℝ) : ℂ) * conj (frame n j))]
  ring

theorem J_cyclicReal {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (q : Fin n → ℝ) :
    J (cyclicReal k q) = cyclicReal k (J q) := by
  funext j
  simp only [J, cyclicReal, firstCoefficient_cyclicReal hn,
    frame_cyclicIndex hn]
  congr 1
  ring

theorem increment_cyclicReal {n : ℕ} (hn : 2 ≤ n) (k : ℕ)
    (q : Fin n → ℝ) :
    increment (cyclicReal k q) =
      fun j => conj (LocalPhase.regularRoot n ^ k) *
        increment q (cyclicIndex n k j) := by
  funext j
  simp only [increment, cyclicReal, firstCoefficient_cyclicReal hn,
    frame_cyclicIndex hn]
  rw [show LocalPhase.regularRoot n ^ k * firstCoefficient q * frame n j =
      firstCoefficient q * (frame n j * LocalPhase.regularRoot n ^ k) by ring]
  have hfac : conj (LocalPhase.regularRoot n ^ k) *
      (frame n j * LocalPhase.regularRoot n ^ k) = frame n j := by
    rw [show conj (LocalPhase.regularRoot n ^ k) *
        (frame n j * LocalPhase.regularRoot n ^ k) =
      (conj (LocalPhase.regularRoot n ^ k) *
        LocalPhase.regularRoot n ^ k) * frame n j by ring,
      conj_root_pow_mul, one_mul]
  generalize (2 * Real.sin (Real.pi / n) / n : ℝ) *
      (q (cyclicIndex n k j) : ℂ) +
    I * (4 * Real.sin (Real.pi / n) / n : ℝ) *
      (((firstCoefficient q * (frame n j *
        LocalPhase.regularRoot n ^ k)).im : ℝ) : ℂ) = w
  change frame n j * w = conj (LocalPhase.regularRoot n ^ k) *
    ((frame n j * LocalPhase.regularRoot n ^ k) * w)
  calc
    _ = (conj (LocalPhase.regularRoot n ^ k) *
        (frame n j * LocalPhase.regularRoot n ^ k)) * w := by rw [hfac]
    _ = _ := by ring

theorem canonicalLift_cyclicReal {n : ℕ} (hn : 3 ≤ n) (k : ℕ)
    (q : Fin n → ℝ) :
    cyclicCenter k (canonicalLift q) = canonicalLift (cyclicReal k q) := by
  apply canonicalLift_unique hn (cyclicReal k q)
  · rw [sum_cyclicCenter, canonicalLift_mean_zero (show 0 < n by omega), mul_zero]
  · rw [difference_cyclicCenter (show 2 ≤ n by omega),
      canonicalLift_difference hn, increment_cyclicReal (show 2 ≤ n by omega)]

theorem projection_cyclicCenter {m : ℕ} (hm : 2 ≤ m) (k : ℕ)
    (C : Fin (2 * m) → ℂ) :
    projection hm (cyclicCenter k C) = cyclicCenter k (projection hm C) := by
  unfold projection
  rw [constraint_cyclicCenter (show 2 ≤ 2 * m by omega),
    ← canonicalLift_cyclicReal (show 3 ≤ 2 * m by omega)]
  funext j
  simp only [cyclicCenter, Pi.sub_apply]
  ring

theorem center_cyclic {m : ℕ} (hm : 2 ≤ m) (k : ℕ)
    (q : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) :
    cyclicCenter k (FixedSchurLinear.center q v) =
      FixedSchurLinear.center (cyclicReal k q) (cyclicCenter k v) := by
  unfold FixedSchurLinear.center
  rw [← canonicalLift_cyclicReal (show 3 ≤ 2 * m by omega)]
  funext j
  simp only [cyclicCenter, Pi.add_apply]
  ring

theorem character_cyclicIndex {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (j : Fin n) :
    character n 1 (cyclicIndex n k j) =
      character n 1 j * LocalPhase.regularRoot n ^ k := by
  have h := frame_cyclicIndex hn k j
  unfold frame at h
  rw [show LocalPhase.phase n 1 * character n 1 j *
      LocalPhase.regularRoot n ^ k =
      LocalPhase.phase n 1 *
        (character n 1 j * LocalPhase.regularRoot n ^ k) by ring] at h
  exact mul_left_cancel₀ (show LocalPhase.phase n 1 ≠ 0 from Complex.exp_ne_zero _) h

theorem diameterVector_cyclic {n : ℕ} (hn : 2 ≤ n) (k : ℕ)
    (θ : Fin n → ℝ) :
    diameterVector (cyclicReal k θ) = cyclicCenter k (diameterVector θ) := by
  funext j
  simp only [diameterVector, cyclicReal, cyclicCenter,
    character_cyclicIndex hn]
  rw [show conj (LocalPhase.regularRoot n ^ k) *
        (character n 1 j * LocalPhase.regularRoot n ^ k *
          LensClosure.unit (θ (cyclicIndex n k j))) =
      (conj (LocalPhase.regularRoot n ^ k) *
        LocalPhase.regularRoot n ^ k) *
          (character n 1 j * LensClosure.unit (θ (cyclicIndex n k j))) by ring,
    conj_root_pow_mul, one_mul]

theorem chordField_cyclic {n : ℕ} (hn : 2 ≤ n) (k : ℕ)
    (θ : Fin n → ℝ) :
    chordField (by omega) (cyclicReal k θ) =
      fun j => chordField (by omega) θ (cyclicIndex n k j) := by
  funext j
  have hd := congrFun (diameterVector_cyclic hn k θ) j
  have hds := congrFun (diameterVector_cyclic hn k θ)
    (successor (by omega) j)
  simp only [chordField]
  rw [hd, hds]
  simp only [cyclicCenter]
  rw [cyclicIndex_successor hn, frame_cyclicIndex hn]
  simp only [map_mul]
  ring

theorem X_cyclic {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (θ : Fin n → ℝ) :
    X (by omega) (cyclicReal k θ) = cyclicReal k (X (by omega) θ) := by
  funext j
  simp only [X, cyclicReal]
  rw [chordField_cyclic hn]

theorem Y_cyclic {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (θ : Fin n → ℝ) :
    Y (by omega) (cyclicReal k θ) = cyclicReal k (Y (by omega) θ) := by
  funext j
  simp only [Y, cyclicReal]
  rw [chordField_cyclic hn]

theorem equationMap_cyclic {m : ℕ} (hm : 0 < m) (k : ℕ)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (σ q : Fin (2 * m) → ℝ) :
    equationMap hm (cyclicReal k θ) (cyclicCenter k v)
        (cyclicReal k σ) (cyclicReal k q) =
      cyclicReal k (equationMap hm θ v σ q) := by
  funext j
  simp only [equationMap, FixedSchurContraction.crossingMap, cyclicReal,
    X_cyclic (show 2 ≤ 2 * m by omega),
    Y_cyclic (show 2 ≤ 2 * m by omega),
    tangent_cyclicCenter (show 2 ≤ 2 * m by omega),
    J_cyclicReal (show 2 ≤ 2 * m by omega)]

theorem baseWord_cyclic {n : ℕ} (k : ℕ) (σ : Fin n → ℝ) :
    baseWord (cyclicReal k σ) = cyclicReal k (baseWord σ) := by
  rfl

theorem norm_cyclicReal {n : ℕ} (k : ℕ) (q : Fin n → ℝ) :
    ‖cyclicReal k q‖ = ‖q‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg q)).2
    intro j
    simpa only [cyclicReal] using norm_le_pi_norm q (cyclicIndex n k j)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (cyclicReal k q))).2
    intro j
    have h := norm_le_pi_norm (cyclicReal k q) ((cyclicIndex n k).symm j)
    simpa only [cyclicReal, Equiv.apply_symm_apply] using h

theorem norm_cyclicReal_sub {n : ℕ} (k : ℕ) (q r : Fin n → ℝ) :
    ‖cyclicReal k q - cyclicReal k r‖ = ‖q - r‖ := by
  rw [show cyclicReal k q - cyclicReal k r = cyclicReal k (q - r) by
    funext j
    rfl, norm_cyclicReal]

theorem root_cyclicIndex {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (j : Fin n) :
    SignedPressureAngular.root n (cyclicIndex n k j) =
      SignedPressureAngular.root n j * LocalPhase.regularRoot n ^ k := by
  simpa only [SignedPressureAngular.root, character, Nat.mul_one] using
    character_cyclicIndex hn k j

theorem root_chord_cyclicIndex {n : ℕ} (hn : 2 ≤ n) (k : ℕ)
    (i j : Fin n) :
    Complex.normSq (SignedPressureAngular.root n (cyclicIndex n k i) -
        SignedPressureAngular.root n (cyclicIndex n k j)) =
      Complex.normSq (SignedPressureAngular.root n i -
        SignedPressureAngular.root n j) := by
  rw [root_cyclicIndex hn, root_cyclicIndex hn, ← sub_mul,
    Complex.normSq_mul]
  have hu : Complex.normSq (LocalPhase.regularRoot n ^ k) = 1 := by
    rw [Complex.normSq_eq_norm_sq, norm_pow, ClosedFourier.root_norm]
    norm_num
  rw [hu, mul_one]

theorem pairEnergy_cyclicReindex {n : ℕ} (hn : 2 ≤ n) (k : ℕ)
    (C : Fin n → ℂ) :
    pairEnergy (by omega) (fun j => C (cyclicIndex n k j)) =
      pairEnergy (by omega) C :=
  pairEnergy_perm (by omega) (cyclicIndex n k)
    (root_chord_cyclicIndex hn k) C

theorem pairEnergy_cyclicCenter {n : ℕ} (hn : 2 ≤ n) (k : ℕ)
    (C : Fin n → ℂ) :
    pairEnergy (by omega) (cyclicCenter k C) = pairEnergy (by omega) C := by
  calc
    pairEnergy (by omega) (cyclicCenter k C) =
        pairEnergy (by omega) (fun j => C (cyclicIndex n k j)) := by
      have hu : Complex.normSq (conj (LocalPhase.regularRoot n ^ k)) = 1 := by
        rw [Complex.normSq_conj, Complex.normSq_eq_norm_sq, norm_pow,
          ClosedFourier.root_norm]
        norm_num
      rw [pairEnergy_eq_chord_sum, pairEnergy_eq_chord_sum]
      simp only [cyclicCenter, ← mul_sub, Complex.normSq_mul, hu, one_mul]
    _ = pairEnergy (by omega) C := pairEnergy_cyclicReindex hn k C

theorem pairEnergy_cyclicReal {n : ℕ} (hn : 2 ≤ n) (k : ℕ)
    (q : Fin n → ℝ) :
    pairEnergy (by omega) (fun j => ((cyclicReal k q j : ℝ) : ℂ)) =
      pairEnergy (by omega) (fun j => (q j : ℂ)) := by
  simpa only [cyclicReal] using pairEnergy_cyclicReindex hn k
    (fun j => (q j : ℂ))

theorem halfPeriodic_cyclicCenter {m : ℕ} (hm : 0 < m) (k : ℕ)
    (C : Fin (2 * m) → ℂ) (hC : HalfPeriodic hm C) :
    HalfPeriodic hm (cyclicCenter k C) := by
  intro j
  simp only [cyclicCenter]
  change conj (LocalPhase.regularRoot (2 * m) ^ k) *
      C (((finRotate (2 * m)) ^ k) (halfTurn hm j)) = _
  rw [halfTurnCommuting_finRotate_pow hm k, hC]
  rfl

theorem halfPeriodic_cyclicReal {m : ℕ} (hm : 0 < m) (k : ℕ)
    (q : Fin (2 * m) → ℝ) (hq : HalfPeriodic hm (fun j => (q j : ℂ))) :
    HalfPeriodic hm (fun j => ((cyclicReal k q j : ℝ) : ℂ)) := by
  intro j
  simp only [cyclicReal]
  change ((q (((finRotate (2 * m)) ^ k) (halfTurn hm j)) : ℝ) : ℂ) = _
  rw [halfTurnCommuting_finRotate_pow hm k]
  simpa only [cyclicIndex] using hq (((finRotate (2 * m)) ^ k) j)

theorem parameterSpace_cyclicCenter {m : ℕ} (hm : 0 < m) (k : ℕ)
    (v : Fin (2 * m) → ℂ) (hv : ParameterSpace hm v) :
    ParameterSpace hm (cyclicCenter k v) := by
  refine ⟨halfPeriodic_cyclicCenter hm k v hv.1, ?_, ?_⟩
  · rw [sum_cyclicCenter, hv.2.1, mul_zero]
  · rw [constraint_cyclicCenter (show 2 ≤ 2 * m by omega), hv.2.2]
    rfl

theorem inDomain_cyclic {m : ℕ} (hm : 0 < m) (k : ℕ)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (hdom : InDomain hm θ v) :
    InDomain hm (cyclicReal k θ) (cyclicCenter k v) := by
  refine ⟨halfPeriodic_cyclicReal hm k θ hdom.1, ?_,
    parameterSpace_cyclicCenter hm k v hdom.2.2.1, ?_⟩
  · change (∑ j, (θ (cyclicIndex (2 * m) k j) : ℂ)) = 0
    rw [Equiv.sum_comp (cyclicIndex (2 * m) k) (fun j => (θ j : ℂ))]
    exact hdom.2.1
  · rw [pairEnergy_cyclicReal (show 2 ≤ 2 * m by omega),
      pairEnergy_cyclicCenter (show 2 ≤ 2 * m by omega)]
    exact hdom.2.2.2

theorem selectedWord_cyclic {m : ℕ} {hm : 0 < m} (k : ℕ)
    (s : SignPattern hm) :
    patternSign (rotatePattern k s) = cyclicReal k (patternSign s) := by
  funext j
  exact patternSign_rotatePattern k s j

theorem eventual_coordinate_cyclic : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (k : ℕ) (s : SignPattern hm)
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain hm θ v →
      coordinate hm (rotatePattern k s) (cyclicReal k θ) (cyclicCenter k v) =
        cyclicReal k (coordinate hm s θ v) := by
  filter_upwards [eventual_coordinate_spec, eventual_coordinate_unique]
    with m hspec huniq
  intro hm k s θ v hdom
  have hs := hspec hm s θ v hdom
  symm
  apply huniq hm (rotatePattern k s) (cyclicReal k θ) (cyclicCenter k v)
    (inDomain_cyclic hm k θ v hdom) (cyclicReal k (coordinate hm s θ v))
  · rw [selectedWord_cyclic, baseWord_cyclic, norm_cyclicReal_sub]
    exact hs.1
  · rw [selectedWord_cyclic, equationMap_cyclic, hs.2]

theorem eventual_chosenCenter_cyclic : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (k : ℕ) (s : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v →
      FixedSchurLinear.center
          (coordinate (by omega) (rotatePattern k s) (cyclicReal k θ)
            (cyclicCenter k v))
          (cyclicCenter k v) =
        cyclicCenter k (FixedSchurLinear.center
          (coordinate (by omega) s θ v) v) := by
  filter_upwards [eventual_coordinate_cyclic] with m heq
  intro hm k s θ v hdom
  rw [heq (by omega) k s θ v hdom, ← center_cyclic hm]

theorem eventual_configuration_cyclic : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (k : ℕ) (s : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v →
      FixedSchurChart.configuration (by omega) (rotatePattern k s) (cyclicReal k θ)
          (cyclicCenter k v) =
        cyclicCenter k (FixedSchurChart.configuration (by omega) s θ v) := by
  filter_upwards [eventual_coordinate_cyclic] with m heq
  intro hm k s θ v hdom
  funext j
  unfold FixedSchurChart.configuration FixedSchurEdgeGeometry.vertex
  rw [heq (by omega) k s θ v hdom]
  have hd := congrFun
    (diameterVector_cyclic (show 2 ≤ 2 * m by omega) k θ) j
  have hc := congrFun (center_cyclic hm k (coordinate (by omega) s θ v) v) j
  rw [hd, ← hc]
  simp only [cyclicCenter]
  ring

theorem eventual_chosen_normal_cyclic : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (k : ℕ) (s : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v →
      normal (by omega)
          (FixedSchurLinear.center
            (coordinate (by omega) (rotatePattern k s) (cyclicReal k θ)
              (cyclicCenter k v))
            (cyclicCenter k v)) =
        cyclicReal k (normal (by omega)
          (FixedSchurLinear.center (coordinate (by omega) s θ v) v)) := by
  filter_upwards [eventual_chosenCenter_cyclic] with m heq
  intro hm k s θ v hdom
  rw [heq hm k s θ v hdom, normal_cyclicCenter (show 2 ≤ 2 * m by omega)]

theorem eventual_chosen_tangent_cyclic : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (k : ℕ) (s : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v →
      tangent (by omega)
          (FixedSchurLinear.center
            (coordinate (by omega) (rotatePattern k s) (cyclicReal k θ)
              (cyclicCenter k v))
            (cyclicCenter k v)) =
        cyclicReal k (tangent (by omega)
          (FixedSchurLinear.center (coordinate (by omega) s θ v) v)) := by
  filter_upwards [eventual_chosenCenter_cyclic] with m heq
  intro hm k s θ v hdom
  rw [heq hm k s θ v hdom, tangent_cyclicCenter (show 2 ≤ 2 * m by omega)]

end
end StructuralNote.FixedSchurCyclicEquivariance
