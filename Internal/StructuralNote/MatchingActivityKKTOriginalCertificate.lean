import StructuralNote.MatchingActivityKKTRigidTransport
import StructuralNote.MatchingActivityNonlocal
import StructuralNote.MatchingActivityActiveEdgeCover

/-! The final KKT certificate on the original vertex labeling.  This file only
packages already established activity, rigidity, and multiplier facts; it does
not repeat the stress argument. -/

namespace StructuralNote.MatchingActivityKKTOriginalCertificate

open Erdos1045 Erdos1045.Configuration Erdos1045.EventualExact Complex
open CommonLocalization CommonClosureEnergy CommonTangentialParameters CommonFiberGeometry
open FiniteFourierLift FourierMultiplier SchurSpectrum
open NormalizedPolarRepresentation ActualCrossingGeometry PolarCenterEnergy
open StrongPointwiseCoordinates MatchingActivityRadialActual
open MatchingActivityRadialClosure MatchingActivityRadialIntegration
open MatchingActivityNonlocalPairs
open MatchingActivityActualChart MatchingActivityActualChartSelection MatchingActivityActualChartEntry
open MatchingActivityActiveConstraintDifferentials
open MatchingActivityActiveGradientIndependence
open MatchingActivityActualActiveGradientIndependence
open MatchingActivityActiveEdgeCover MatchingActivityNonlocal
open MatchingActivityKKTAnalytic MatchingActivityKKTActual
open MatchingActivityKKTRigidTransport
open MatchingActivityCrossingExclusivity MatchingActivityRadialGeometry
open FixedSchurEdgeGeometry FixedSchurOffsetGeometry FixedSchurChartGeometry
open FixedSchurSimpleGraph
open scoped BigOperators Topology

noncomputable section

/-- Full row rank of the active squared-distance differentials after the
physical relabeling back to the original configuration. -/
def RelabeledConstraintDifferentialsIndependent {m : ℕ} (hm : 0 < m)
    (s : Fin m → ℝ) (π : Equiv.Perm (Fin (2 * m)))
    (z : Points (2 * m)) : Prop :=
  ∀ cM cX : Fin m → ℝ,
    (∀ U : Points (2 * m),
      (∑ i, cM i * edgeDifferential z U
        (π (matchingFirst i)) (π (matchingSecond hm i))) +
      ∑ i, cX i * edgeDifferential z U
        (π (selectedFirst hm s i)) (π (selectedSecond hm s i)) = 0) →
    cM = 0 ∧ cX = 0

/-- Push a normalized ambient velocity to the original labeling. -/
def pushforwardVelocity {n : ℕ} (b : ℂ) (π : Equiv.Perm (Fin n))
    (V : Points n) : Points n :=
  fun k => b * V (π.symm k)

@[simp] theorem pullback_pushforward {n : ℕ} (b : ℂ)
    (π : Equiv.Perm (Fin n)) (V : Points n) (hb : ‖b‖ = 1) :
    pullbackVelocity b π (pushforwardVelocity b π V) = V := by
  funext j
  simp only [pullbackVelocity, pushforwardVelocity, Equiv.symm_apply_apply]
  rw [← mul_assoc, mul_comm (starRingEnd ℂ b) b,
    mul_conj_eq_one_of_norm_eq_one hb, one_mul]

/-- Ambient LICQ is invariant under the genuine unit rigid relabeling. -/
theorem relabeled_independent_of_rigid {m : ℕ} (hm : 0 < m)
    (s : Fin m → ℝ) {x z : Points (2 * m)}
    (π : Equiv.Perm (Fin (2 * m))) (a b : ℂ) (hb : ‖b‖ = 1)
    (hrep : ∀ j, z (π j) = a + b * x j)
    (hind : ActiveConstraintDifferentialsIndependent hm s x) :
    RelabeledConstraintDifferentialsIndependent hm s π z := by
  intro cM cX hrel
  apply hind cM cX
  intro V
  let U := pushforwardVelocity b π V
  have hU := hrel U
  have hpull : pullbackVelocity b π U = V :=
    pullback_pushforward b π V hb
  simpa only [← edgeDifferential_rigid_relabel π a b hb hrep U,
    hpull] using hU

/-- LICQ makes the multiplier certificate unique on the original labeling. -/
theorem relabeled_multipliers_unique {m : ℕ} (hm : 0 < m)
    (s : Fin m → ℝ) (π : Equiv.Perm (Fin (2 * m)))
    (z : Points (2 * m))
    (hind : RelabeledConstraintDifferentialsIndependent hm s π z)
    (K L : RelabeledMultipliers hm s π z) : K = L := by
  have hrel (U : Points (2 * m)) :
      (∑ i, (K.matching i - L.matching i) * edgeDifferential z U
        (π (matchingFirst i)) (π (matchingSecond hm i))) +
      ∑ i, (K.crossing i - L.crossing i) * edgeDifferential z U
        (π (selectedFirst hm s i)) (π (selectedSecond hm s i)) = 0 := by
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    linarith [K.stationarity U, L.stationarity U]
  obtain ⟨hM, hX⟩ := hind (K.matching - L.matching) (K.crossing - L.crossing) (by
    intro U
    simpa only [Pi.sub_apply] using hrel U)
  cases K with
  | mk KM KX KS =>
      cases L with
      | mk LM LX LS =>
          simp only at hM hX ⊢
          have hMeq : KM = LM := sub_eq_zero.mp hM
          have hXeq : KX = LX := sub_eq_zero.mp hX
          subst LM
          subst LX
          rfl

/-- The literal two crossing-multiplier arrays used in the manuscript. -/
def plusMultiplier {m : ℕ} (s : Fin m → ℝ) (lam : Fin m → ℝ) (i : Fin m) : ℝ :=
  if s i = 1 then lam i else 0

def minusMultiplier {m : ℕ} (s : Fin m → ℝ) (lam : Fin m → ℝ) (i : Fin m) : ℝ :=
  if s i = -1 then lam i else 0

theorem branch_multipliers_of_sign {m : ℕ} {s lam : Fin m → ℝ}
    (hs : ∀ i, s i = 1 ∨ s i = -1) (hlam : ∀ i, 0 < lam i) (i : Fin m) :
    0 ≤ plusMultiplier s lam i ∧ 0 ≤ minusMultiplier s lam i ∧
    plusMultiplier s lam i * minusMultiplier s lam i = 0 ∧
    plusMultiplier s lam i + minusMultiplier s lam i = lam i ∧
    (s i = 1 → 0 < plusMultiplier s lam i ∧ minusMultiplier s lam i = 0) ∧
    (s i = -1 → plusMultiplier s lam i = 0 ∧ 0 < minusMultiplier s lam i) := by
  rcases hs i with hi | hi
  · norm_num [plusMultiplier, minusMultiplier, hi, (hlam i).le, hlam i]
  · norm_num [plusMultiplier, minusMultiplier, hi, (hlam i).le, hlam i]

/-- Rewrite the selected-crossing KKT identity as the manuscript's two
crossing branches, with the inactive coefficient definitionally zero. -/
theorem relabeled_branch_stationarity {m : ℕ} (hm : 0 < m)
    (s : Fin m → ℝ) (π : Equiv.Perm (Fin (2 * m))) (z : Points (2 * m))
    (L : RelabeledMultipliers hm s π z)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (U : Points (2 * m)) :
    fderiv ℝ logDiscriminant z U =
      (∑ i, L.matching i * edgeDifferential z U
        (π (matchingFirst i)) (π (matchingSecond hm i))) +
      ((∑ i, plusMultiplier s L.crossing i * edgeDifferential z U
        (π (successor (by omega) (halfIndex i)))
        (π (halfTurn hm (halfIndex i)))) +
      ∑ i, minusMultiplier s L.crossing i * edgeDifferential z U
        (π (halfIndex i))
        (π (halfTurn hm (successor (by omega) (halfIndex i))))) := by
  rw [L.stationarity]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases hs i with hi | hi
  · norm_num [plusMultiplier, minusMultiplier, selectedFirst, selectedSecond, hi]
  · norm_num [plusMultiplier, minusMultiplier, selectedFirst, selectedSecond, hi]

/-- The physical `+` crossing vector is literally the corresponding edge of
the saturated normalized configuration. -/
theorem normalized_plus_crossing {m : ℕ} (hm : 2 ≤ m)
    (β : ℂ) (u : ℕ → ℂ) (hu : Function.Periodic u (2 * m))
    (hsat : ∀ i : Fin m, modelRadii m β u i = 1) (i : Fin m) :
    normalizedPoint m β u (successor (by omega) (halfIndex i)) -
        normalizedPoint m β u (halfTurn (by omega) (halfIndex i)) =
      plusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
        (actualCenter m β u) i := by
  have hcfg := normalizedPoint_meanGauge_eq_vertex (show 0 < m by omega) β u hu hsat
  have hθ : HalfPeriodic (by omega) (fun j => (normalizedAngle m u j : ℂ)) := by
    intro j
    exact congrArg Complex.ofReal (normalizedAngle_halfPeriodic (by omega) u hu j)
  have hC : HalfPeriodic (by omega) (centerZero (actualCenter m β u)) :=
    centerZero_halfPeriodic (by omega) _
      (actualCenter_halfPeriodic (by omega) β u hu)
  have hedge := crossingVector_eq_vertex_sub_plus hm (normalizedAngle m u)
    (centerZero (actualCenter m β u)) (fun _ => (1 : ℝ)) hθ hC (halfIndex i) rfl
  have hsum := weighted_diameter_sum (show 0 < m by omega)
    (normalizedAngle m u) (modelRadii m β u) i
  rw [radiusFull_halfIndex, radiusFull_next, hsat i,
    hsat (nextIndex (by omega) i)] at hsum
  simp only [Complex.ofReal_one, one_mul] at hsum
  have hd : centerZero (actualCenter m β u) (successor (by omega) (halfIndex i)) -
      centerZero (actualCenter m β u) (halfIndex i) =
      difference (by omega) (actualCenter m β u) (halfIndex i) := by
    simp only [centerZero, difference]
    ring
  have hv (j : Fin (2 * m)) := congrFun hcfg j
  rw [show normalizedPoint m β u (successor (by omega) (halfIndex i)) -
      normalizedPoint m β u (halfTurn (by omega) (halfIndex i)) =
      vertex (normalizedAngle m u) (centerZero (actualCenter m β u))
          (successor (by omega) (halfIndex i)) -
        vertex (normalizedAngle m u) (centerZero (actualCenter m β u))
          (halfTurn (by omega) (halfIndex i)) by
        rw [← hv (successor (by omega) (halfIndex i)),
          ← hv (halfTurn (by omega) (halfIndex i))]
        ring]
  rw [← hedge]
  unfold crossingVector plusCrossingVector
  rw [hd, hsum]
  norm_num

/-- The physical `-` crossing vector is the other adjacent edge. -/
theorem normalized_minus_crossing {m : ℕ} (hm : 2 ≤ m)
    (β : ℂ) (u : ℕ → ℂ) (hu : Function.Periodic u (2 * m))
    (hsat : ∀ i : Fin m, modelRadii m β u i = 1) (i : Fin m) :
    normalizedPoint m β u (halfIndex i) -
        normalizedPoint m β u (halfTurn (by omega) (successor (by omega) (halfIndex i))) =
      minusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
        (actualCenter m β u) i := by
  have hcfg := normalizedPoint_meanGauge_eq_vertex (show 0 < m by omega) β u hu hsat
  have hθ : HalfPeriodic (by omega) (fun j => (normalizedAngle m u j : ℂ)) := by
    intro j
    exact congrArg Complex.ofReal (normalizedAngle_halfPeriodic (by omega) u hu j)
  have hC : HalfPeriodic (by omega) (centerZero (actualCenter m β u)) :=
    centerZero_halfPeriodic (by omega) _
      (actualCenter_halfPeriodic (by omega) β u hu)
  have hedge := crossingVector_eq_vertex_sub_minus hm (normalizedAngle m u)
    (centerZero (actualCenter m β u)) (fun _ => (-1 : ℝ)) hθ hC (halfIndex i) rfl
  have hsum := weighted_diameter_sum (show 0 < m by omega)
    (normalizedAngle m u) (modelRadii m β u) i
  rw [radiusFull_halfIndex, radiusFull_next, hsat i,
    hsat (nextIndex (by omega) i)] at hsum
  simp only [Complex.ofReal_one, one_mul] at hsum
  have hd : centerZero (actualCenter m β u) (successor (by omega) (halfIndex i)) -
      centerZero (actualCenter m β u) (halfIndex i) =
      difference (by omega) (actualCenter m β u) (halfIndex i) := by
    simp only [centerZero, difference]
    ring
  have hv (j : Fin (2 * m)) := congrFun hcfg j
  rw [show normalizedPoint m β u (halfIndex i) -
      normalizedPoint m β u (halfTurn (by omega) (successor (by omega) (halfIndex i))) =
      vertex (normalizedAngle m u) (centerZero (actualCenter m β u)) (halfIndex i) -
        vertex (normalizedAngle m u) (centerZero (actualCenter m β u))
          (halfTurn (by omega) (successor (by omega) (halfIndex i))) by
        rw [← hv (halfIndex i),
          ← hv (halfTurn (by omega) (successor (by omega) (halfIndex i)))]
        ring]
  rw [← hedge]
  unfold crossingVector minusCrossingVector
  simp only [Complex.ofReal_neg, Complex.ofReal_one]
  rw [hd, hsum]
  ring

theorem normalized_matching_active {m : ℕ} (hm : 2 ≤ m)
    (β : ℂ) (u : ℕ → ℂ) (hu : Function.Periodic u (2 * m))
    (hsat : ∀ i : Fin m, modelRadii m β u i = 1) (i : Fin m) :
    ‖normalizedPoint m β u (matchingFirst i) -
      normalizedPoint m β u (matchingSecond (by omega) i)‖ = 2 := by
  have hcfg := normalizedPoint_meanGauge_eq_vertex (show 0 < m by omega) β u hu hsat
  have hθ : HalfPeriodic (by omega) (fun j => (normalizedAngle m u j : ℂ)) := by
    intro j
    exact congrArg Complex.ofReal (normalizedAngle_halfPeriodic (by omega) u hu j)
  have hC : HalfPeriodic (by omega) (centerZero (actualCenter m β u)) :=
    centerZero_halfPeriodic (by omega) _
      (actualCenter_halfPeriodic (by omega) β u hu)
  have hv (j : Fin (2 * m)) := congrFun hcfg j
  rw [show normalizedPoint m β u (matchingFirst i) -
      normalizedPoint m β u (matchingSecond (by omega) i) =
      vertex (normalizedAngle m u) (centerZero (actualCenter m β u)) (matchingFirst i) -
        vertex (normalizedAngle m u) (centerZero (actualCenter m β u))
          (matchingSecond (by omega) i) by
        rw [← hv (matchingFirst i), ← hv (matchingSecond (by omega) i)]
        ring]
  unfold matchingFirst matchingSecond vertex
  rw [diameterVector_halfTurn (by omega) (normalizedAngle m u) hθ,
    hC (halfIndex i)]
  rw [show diameterVector (normalizedAngle m u) (halfIndex i) +
      centerZero (actualCenter m β u) (halfIndex i) -
      (-diameterVector (normalizedAngle m u) (halfIndex i) +
        centerZero (actualCenter m β u) (halfIndex i)) =
      2 * diameterVector (normalizedAngle m u) (halfIndex i) by ring,
    norm_mul, diameterVector_norm]
  norm_num

theorem normalized_selected_active {m : ℕ} (hm : 2 ≤ m)
    (β : ℂ) (u : ℕ → ℂ) (hu : Function.Periodic u (2 * m))
    (hsat : ∀ i : Fin m, modelRadii m β u i = 1)
    (hactive : ∀ i : Fin m,
      (‖plusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ = 2 ∧
        ‖minusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ < 2) ∨
      (‖plusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ < 2 ∧
        ‖minusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ = 2)) (i : Fin m) :
    ‖normalizedPoint m β u
        (selectedFirst (by omega)
          (fun j => activeHalfSign (by omega) (normalizedAngle m u)
            (modelRadii m β u) (actualCenter m β u) j) i) -
      normalizedPoint m β u
        (selectedSecond (by omega)
          (fun j => activeHalfSign (by omega) (normalizedAngle m u)
            (modelRadii m β u) (actualCenter m β u) j) i)‖ = 2 := by
  rcases hactive i with hp | hn
  · have hs : activeHalfSign (by omega) (normalizedAngle m u) (modelRadii m β u)
        (actualCenter m β u) i = 1 := by
      unfold activeHalfSign
      rw [if_pos hp.1]
    simp only [selectedFirst, selectedSecond, hs, if_pos]
    rw [normalized_plus_crossing hm β u hu hsat i]
    exact hp.1
  · have hs : activeHalfSign (by omega) (normalizedAngle m u) (modelRadii m β u)
        (actualCenter m β u) i = -1 := by
      unfold activeHalfSign
      rw [if_neg (ne_of_lt hn.1)]
    simp only [selectedFirst, selectedSecond, hs,
      if_neg (by norm_num : (-1 : ℝ) ≠ 1)]
    rw [normalized_minus_crossing hm β u hu hsat i]
    exact hn.2

/-- If the forward `(m+1)` crossing is active, the physical word has the
required negative sign at its initial vertex. -/
theorem activeRaw_neg_of_forward_crossing {m : ℕ} (hm : 2 ≤ m)
    (β : ℂ) (u : ℕ → ℂ) (hu : Function.Periodic u (2 * m))
    (hsat : ∀ i : Fin m, modelRadii m β u i = 1)
    (hactive : ∀ i : Fin m,
      (‖plusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ = 2 ∧
        ‖minusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ < 2) ∨
      (‖plusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ < 2 ∧
        ‖minusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ = 2))
    {p q : Fin (2 * m)} (hpq : p = cyclicAdvance q (m + 1))
    (hd : ‖normalizedPoint m β u p - normalizedPoint m β u q‖ = 2) :
    activeRaw (by omega) (normalizedAngle m u) (modelRadii m β u)
      (actualCenter m β u) q = -1 := by
  obtain ⟨i, hq | hq⟩ := half_decomposition_active (show 0 < m by omega) q
  · have hp : p = halfTurn (by omega) (successor (by omega) (halfIndex i)) := by
      rw [hpq, hq]
      exact advance_next (show 0 < m by omega) (halfIndex i)
    have hminus : ‖minusCrossingVector (by omega) (normalizedAngle m u)
        (modelRadii m β u) (actualCenter m β u) i‖ = 2 := by
      rw [← normalized_minus_crossing hm β u hu hsat i]
      rw [hp, hq] at hd
      rwa [norm_sub_rev] at hd
    have hsign : activeHalfSign (by omega) (normalizedAngle m u) (modelRadii m β u)
        (actualCenter m β u) i = -1 := by
      unfold activeHalfSign
      rcases hactive i with ha | ha
      · exfalso
        linarith [ha.2, hminus]
      · rw [if_neg (ne_of_lt ha.1)]
    rw [hq]
    change activeRaw (by omega) (normalizedAngle m u) (modelRadii m β u)
      (actualCenter m β u) (halfIndex i) = -1
    rw [activeRaw_halfIndex]
    exact hsign
  · have hp : p = successor (by omega) (halfIndex i) := by
      rw [hpq, hq]
      exact advance_halfTurn_next hm i
    have hplus : ‖plusCrossingVector (by omega) (normalizedAngle m u)
        (modelRadii m β u) (actualCenter m β u) i‖ = 2 := by
      rw [← normalized_plus_crossing hm β u hu hsat i]
      rwa [hp, hq] at hd
    have hsign : activeHalfSign (by omega) (normalizedAngle m u) (modelRadii m β u)
        (actualCenter m β u) i = 1 := by
      unfold activeHalfSign
      rw [if_pos hplus]
    have hanti := activeRaw_antiperiodic (show 0 < m by omega) (normalizedAngle m u)
      (modelRadii m β u) (actualCenter m β u) (halfIndex i)
    rw [hq]
    change activeRaw (by omega) (normalizedAngle m u) (modelRadii m β u)
      (actualCenter m β u) (halfTurn (by omega) (halfIndex i)) = -1
    rw [hanti, activeRaw_halfIndex, hsign]

/-- On the very same physical relabeling used by the KKT multipliers, the
diameter graph is the word selected by the physical crossing activity. -/
theorem model_actual_word_graph {m : ℕ} (hm : 0 < m)
    {z : Points (2 * m)} {π : Equiv.Perm (Fin (2 * m))} {α β : ℂ}
    {u : ℕ → ℂ} {η : ℝ}
    (hmodel : NormalizedRelativeEdgeModel z π α β u η)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (ctx : ActualKKTConditions hm β u) (p q : Fin (2 * m)) :
    ‖z (π p) - z (π q)‖ = 2 ↔
      WordEdge (activeRaw hm (normalizedAngle m u) (modelRadii m β u)
        (actualCenter m β u)) p q := by
  let σ := activeRaw hm (normalizedAngle m u) (modelRadii m β u)
    (actualCenter m β u)
  let s : Fin m → ℝ := fun i => activeHalfSign hm (normalizedAngle m u)
    (modelRadii m β u) (actualCenter m β u) i
  have hanti : FiniteBox.Antiperiodic hm σ :=
    activeRaw_antiperiodic hm (normalizedAngle m u) (modelRadii m β u)
      (actualCenter m β u)
  have hs (i : Fin m) : s i = σ (halfIndex i) := by
    simp only [s, σ, activeRaw_halfIndex]
  have hm2 : 2 ≤ m := by
    have := ctx.large
    omega
  constructor
  · intro hd
    have hdn : ‖normalizedPoint m β u p - normalizedPoint m β u q‖ = 2 := by
      rw [← model_normalized_distance hmodel]
      exact hd
    let r := cyclicForwardDistance q p
    have hrlt : r < 2 * m := by
      dsimp only [r, cyclicForwardDistance]
      exact Nat.mod_lt _ (by omega)
    have hpq : cyclicAdvance q r = p :=
      CommonFiberNonlocalFeasibility.cyclicAdvance_forwardDistance q p
    have hspecial : r = m - 1 ∨ r = m ∨ r = m + 1 := by
      by_contra hn
      push Not at hn
      have hlt := model_nonlocal_offset_strict ctx.large hrlt
        ⟨hn.1, hn.2.1, hn.2.2⟩ hmodel hz.1 ctx.bounds ctx.budget
          ctx.smallB ctx.smallC ctx.smallR ctx.smallb q
      rw [hpq] at hlt
      linarith
    rw [wordEdge_generated hm2]
    rcases hspecial with hr | hr | hr
    · right
      right
      have hpq' : p = cyclicAdvance q (m - 1) := by simpa only [hr] using hpq.symm
      have hqp : q = cyclicAdvance p (m + 1) := by
        calc
          q = cyclicAdvance (cyclicAdvance q (m - 1)) (m + 1) :=
            (advance_reverse q (by omega)).symm
          _ = cyclicAdvance p (m + 1) := by rw [hpq']
      refine ⟨hqp, ?_⟩
      exact activeRaw_neg_of_forward_crossing hm2 β u
        hmodel.periodic ctx.saturated hctxActive hqp (by rwa [norm_sub_rev])
    · left
      have hpq' : cyclicAdvance q m = p := by simpa only [hr] using hpq
      simpa only [halfTurn, cyclicAdvance] using hpq'.symm
    · right
      left
      have hpq' : p = cyclicAdvance q (m + 1) := by simpa only [hr] using hpq.symm
      refine ⟨hpq', ?_⟩
      exact activeRaw_neg_of_forward_crossing hm2 β u
        hmodel.periodic ctx.saturated hctxActive hpq' hdn
  · intro hedge
    have hcov := wordEdge_covered hm2 σ hanti s hs hedge
    have hnorm : ‖normalizedPoint m β u p - normalizedPoint m β u q‖ = 2 := by
      rcases hcov with ⟨i, h | h⟩ | ⟨i, h | h⟩
      · rw [h.1, h.2]
        exact normalized_matching_active hm2 β u
          hmodel.periodic ctx.saturated i
      · rw [h.1, h.2, norm_sub_rev]
        exact normalized_matching_active hm2 β u
          hmodel.periodic ctx.saturated i
      · rw [h.1, h.2]
        exact normalized_selected_active hm2 β u hmodel.periodic
          ctx.saturated hctxActive i
      · rw [h.1, h.2, norm_sub_rev]
        exact normalized_selected_active hm2 β u hmodel.periodic
          ctx.saturated hctxActive i
    rw [model_normalized_distance hmodel]
    exact hnorm
  where
    hctxActive := ctx.active

theorem model_actual_active_edges_exact {m : ℕ} (hm : 0 < m)
    {z : Points (2 * m)} {π : Equiv.Perm (Fin (2 * m))} {α β : ℂ}
    {u : ℕ → ℂ} {η : ℝ}
    (hmodel : NormalizedRelativeEdgeModel z π α β u η)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (ctx : ActualKKTConditions hm β u) (p q : Fin (2 * m)) :
    ‖z (π p) - z (π q)‖ = 2 ↔
      CoveredByActiveEdges hm
        (fun i => activeHalfSign hm (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i) p q := by
  let σ := activeRaw hm (normalizedAngle m u) (modelRadii m β u)
    (actualCenter m β u)
  let s : Fin m → ℝ := fun i => activeHalfSign hm (normalizedAngle m u)
    (modelRadii m β u) (actualCenter m β u) i
  have hanti : FiniteBox.Antiperiodic hm σ :=
    activeRaw_antiperiodic hm (normalizedAngle m u) (modelRadii m β u)
      (actualCenter m β u)
  have hs (i : Fin m) : s i = σ (halfIndex i) := by
    simp only [s, σ, activeRaw_halfIndex]
  have hm2 : 2 ≤ m := by have := ctx.large; omega
  constructor
  · intro hd
    exact wordEdge_covered hm2 σ hanti s hs
      ((model_actual_word_graph hm hmodel hz ctx p q).1 hd)
  · intro hcov
    have hnorm : ‖normalizedPoint m β u p - normalizedPoint m β u q‖ = 2 := by
      rcases hcov with ⟨i, h | h⟩ | ⟨i, h | h⟩
      · rw [h.1, h.2]
        exact normalized_matching_active hm2 β u hmodel.periodic ctx.saturated i
      · rw [h.1, h.2, norm_sub_rev]
        exact normalized_matching_active hm2 β u hmodel.periodic ctx.saturated i
      · rw [h.1, h.2]
        exact normalized_selected_active hm2 β u hmodel.periodic ctx.saturated ctx.active i
      · rw [h.1, h.2, norm_sub_rev]
        exact normalized_selected_active hm2 β u hmodel.periodic ctx.saturated ctx.active i
    rw [model_normalized_distance hmodel]
    exact hnorm

theorem model_relabeled_independent {m : ℕ} (hm : 0 < m)
    {z : Points (2 * m)} {π : Equiv.Perm (Fin (2 * m))} {α β : ℂ}
    {u : ℕ → ℂ} {η : ℝ}
    (hmodel : NormalizedRelativeEdgeModel z π α β u η)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (ctx : ActualKKTConditions hm β u) :
    RelabeledConstraintDifferentialsIndependent hm
      (fun i => activeHalfSign hm (normalizedAngle m u) (modelRadii m β u)
        (actualCenter m β u) i) π z := by
  have hind := model_activeConstraintDifferentialsIndependent ctx.large hmodel hz.1
    ctx.bounds ctx.budget ctx.smallB ctx.smallC ctx.smallR ctx.saturated ctx.active
  obtain ⟨A, R, hR, hrep⟩ := model_directRigid_normalizedPoint hmodel
  exact relabeled_independent_of_rigid hm _ π A R hR hrep hind

/-- A complete original-label KKT certificate, retaining the exact physical
model and the normalized multiplier to which positivity applies. -/
structure OriginalCertificate {m : ℕ} (z : Points (2 * m)) (hm : 0 < m)
    (π : Equiv.Perm (Fin (2 * m))) (α β : ℂ) (u : ℕ → ℂ) (η : ℝ) : Type where
  model : NormalizedRelativeEdgeModel z π α β u η
  conditions : ActualKKTConditions hm β u
  normalized : ActualMultipliers hm β u
  original : RelabeledMultipliers hm
    (fun i => activeHalfSign hm (normalizedAngle m u) (modelRadii m β u)
      (actualCenter m β u) i) π z
  matching_eq : original.matching = normalized.matching
  crossing_eq : original.crossing = normalized.crossing
  active_edges : ∀ p q, ‖z (π p) - z (π q)‖ = 2 ↔
    CoveredByActiveEdges hm
      (fun i => activeHalfSign hm (normalizedAngle m u) (modelRadii m β u)
        (actualCenter m β u) i) p q
  licq : RelabeledConstraintDifferentialsIndependent hm
    (fun i => activeHalfSign hm (normalizedAngle m u) (modelRadii m β u)
      (actualCenter m β u) i) π z
  unique : ∀ L : RelabeledMultipliers hm
    (fun i => activeHalfSign hm (normalizedAngle m u) (modelRadii m β u)
      (actualCenter m β u) i) π z, L = original

theorem eventual_actual_maximizer_original_certificate :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z : Points (2 * m),
      ExtremalNormalization.DiameterExtremal z →
      ∃ (hm : 0 < m) (π : Equiv.Perm (Fin (2 * m))) (α β : ℂ)
        (u : ℕ → ℂ) (η : ℝ), Nonempty (OriginalCertificate z hm π α β u η) := by
  obtain ⟨m₀, hcert⟩ := eventual_actual_maximizer_relabeled_multipliers
  refine ⟨m₀, ?_⟩
  intro m hm z hz
  obtain ⟨hmp, π, α, β, u, η, K, L, hmodel, ctx, _, hmatching, hcrossing⟩ :=
    hcert m hm z hz
  have hactive := model_actual_active_edges_exact hmp hmodel hz ctx
  have hind := model_relabeled_independent hmp hmodel hz ctx
  have hunique (L' : RelabeledMultipliers hmp
      (fun i => activeHalfSign hmp (normalizedAngle m u) (modelRadii m β u)
        (actualCenter m β u) i) π z) : L' = L :=
    relabeled_multipliers_unique hmp _ π z hind L' L
  exact ⟨hmp, π, α, β, u, η,
    ⟨⟨hmodel, ctx, K, L, hmatching, hcrossing, hactive, hind, hunique⟩⟩⟩

end
end StructuralNote.MatchingActivityKKTOriginalCertificate
