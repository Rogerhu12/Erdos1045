import StructuralNote.MatchingActivityActiveEdgeCover
import StructuralNote.MatchingActivityActiveGradientIndependence
import Mathlib.Analysis.Calculus.LagrangeMultipliers
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Equality-multiplier existence for a diameter extremal whose complete
active graph is the selected word graph.  The inequality signs of the
multipliers are handled by genuine one-sided feasible paths later. -/

namespace StructuralNote.MatchingActivityKKTAnalytic

open Erdos1045 Erdos1045.EventualExact Configuration Filter Set
open FixedSchurChartGeometry FixedSchurSimpleGraph
open FiniteFourierLift FiniteBox
open MatchingActivityActiveConstraintDifferentials
open MatchingActivityActiveGradientIndependence MatchingActivityActiveEdgeCover
open scoped BigOperators Topology ContDiff

noncomputable section

def activeConstraint {m : ℕ} (hm : 0 < m) (s : Fin m → ℝ)
    (k : Sum (Fin m) (Fin m)) (x : Points (2 * m)) : ℝ :=
  match k with
  | .inl i => matchingConstraint hm x i
  | .inr i => selectedConstraint hm s x i

def activeLevelSet {m : ℕ} (hm : 0 < m) (s : Fin m → ℝ)
    (x : Points (2 * m)) : Set (Points (2 * m)) :=
  {y | ∀ k, activeConstraint hm s k y = activeConstraint hm s k x}

def logDiscriminant {n : ℕ} (x : Points n) : ℝ :=
  Real.log (discriminant x)

theorem edgeConstraint_contDiff {n : ℕ} (p q : Fin n) :
    ContDiff ℝ ∞ (fun x : Points n => edgeConstraint x p q) := by
  have hz : ContDiff ℝ ∞ (fun x : Points n => x p - x q) :=
    (contDiff_apply ℝ ℂ p).sub (contDiff_apply ℝ ℂ q)
  have hre : ContDiff ℝ ∞ (fun x : Points n => (x p - x q).re) :=
    Complex.reCLM.contDiff.comp hz
  have him : ContDiff ℝ ∞ (fun x : Points n => (x p - x q).im) :=
    Complex.imCLM.contDiff.comp hz
  have hsq : ContDiff ℝ ∞ (fun x : Points n => Complex.normSq (x p - x q)) := by
    simpa only [Complex.normSq_apply] using (hre.mul hre).add (him.mul him)
  convert hsq using 1
  funext y
  exact (Complex.normSq_eq_norm_sq (y p - y q)).symm

theorem activeConstraint_contDiff {m : ℕ} (hm : 0 < m) (s : Fin m → ℝ)
    (k : Sum (Fin m) (Fin m)) :
    ContDiff ℝ ∞ (activeConstraint hm s k) := by
  rcases k with i | i
  · exact edgeConstraint_contDiff _ _
  · exact edgeConstraint_contDiff _ _

theorem logDiscriminant_contDiffAt {n : ℕ} {x : Points n}
    (hx : Function.Injective x) : ContDiffAt ℝ ∞ logDiscriminant x := by
  have hd : ContDiffAt ℝ ∞ (fun y : Points n => discriminant y) x := by
    unfold discriminant
    apply contDiffAt_prod
    intro i _
    apply contDiffAt_prod
    intro j hj
    have hne : x i - x j ≠ 0 := sub_ne_zero.mpr (hx.ne (Finset.ne_of_mem_erase hj).symm)
    exact ((contDiffAt_apply ℝ ℂ i x).sub (contDiffAt_apply ℝ ℂ j x)).norm ℂ hne
  exact hd.log (discriminant_pos x hx).ne'

theorem fderiv_activeConstraint_apply {m : ℕ} (hm : 0 < m) (s : Fin m → ℝ)
    (k : Sum (Fin m) (Fin m)) (x U : Points (2 * m)) :
    fderiv ℝ (activeConstraint hm s k) x U =
      match k with
      | .inl i => edgeDifferential x U (matchingFirst i) (matchingSecond hm i)
      | .inr i => edgeDifferential x U (selectedFirst hm s i) (selectedSecond hm s i) := by
  let p : ℝ → Points (2 * m) := fun t => x + t • U
  have hp : HasDerivAt p U 0 := by
    simpa only [p, one_smul] using
      ((hasDerivAt_id' (0 : ℝ)).smul_const U).const_add x
  have hpj (j : Fin (2 * m)) : HasDerivAt (fun t => p t j) (U j) 0 :=
    (ContinuousLinearMap.proj j).hasFDerivAt.comp_hasDerivAt 0 hp
  have hsmooth : HasStrictFDerivAt (activeConstraint hm s k)
      (fderiv ℝ (activeConstraint hm s k) x) x :=
    (activeConstraint_contDiff hm s k).contDiffAt.hasStrictFDerivAt
      (by norm_num : (∞ : WithTop ℕ∞) ≠ 0)
  have hsmooth0 : HasFDerivAt (activeConstraint hm s k)
      (fderiv ℝ (activeConstraint hm s k) x) (p 0) := by
    simpa only [p, zero_smul, add_zero] using hsmooth.hasFDerivAt
  have hchain := hsmooth0.comp_hasDerivAt 0 hp
  rcases k with i | i
  · simpa only [activeConstraint, p, zero_smul, add_zero] using
      hchain.unique (matchingConstraint_hasDerivAt hm i hpj)
  · simpa only [activeConstraint, p, zero_smul, add_zero] using
      hchain.unique (selectedConstraint_hasDerivAt hm s i hpj)

theorem eventually_diameter_on_activeLevel {m : ℕ} (hm : 2 ≤ m)
    (σ : Fin (2 * m) → ℝ) (hσ : Antiperiodic (by omega) σ)
    (s : Fin m → ℝ) (hs : ∀ i, s i = σ (CommonClosureEnergy.halfIndex i))
    (x : Points (2 * m)) (hxdiam : DiameterAtMost 2 x)
    (hgraph : ∀ p q, ‖x p - x q‖ = 2 ↔ WordEdge σ p q)
    (hmatch : ∀ i, matchingConstraint (by omega) x i = 4)
    (hselected : ∀ i, selectedConstraint (by omega) s x i = 4) :
    ∀ᶠ y in 𝓝 x, y ∈ activeLevelSet (by omega) s x → DiameterAtMost 2 y := by
  have hnear (p q : Fin (2 * m)) :
      ∀ᶠ y in 𝓝 x, ¬WordEdge σ p q → edgeConstraint y p q < 4 := by
    by_cases he : WordEdge σ p q
    · exact Eventually.of_forall fun _ hn => (hn he).elim
    · have hlt : edgeConstraint x p q < 4 := by
        have hle := hxdiam p q
        have hne : ‖x p - x q‖ ≠ 2 := fun h => he ((hgraph p q).1 h)
        have hsqle : ‖x p - x q‖ ^ 2 ≤ 4 := by
          nlinarith [norm_nonneg (x p - x q)]
        have hsqne : ‖x p - x q‖ ^ 2 ≠ 4 := by
          intro heq
          apply hne
          nlinarith [norm_nonneg (x p - x q)]
        exact lt_of_le_of_ne hsqle hsqne
      filter_upwards [((edgeConstraint_contDiff p q).continuous.continuousAt.tendsto
        (Iio_mem_nhds hlt))] with y hy _
      exact hy
  have hall : ∀ᶠ y in 𝓝 x, ∀ p q, ¬WordEdge σ p q → edgeConstraint y p q < 4 := by
    rw [Filter.eventually_all]
    intro p
    rw [Filter.eventually_all]
    exact hnear p
  filter_upwards [hall] with y hy hlevel
  intro p q
  by_cases he : WordEdge σ p q
  · have hcov := covered_edgeConstraint (by omega) s (wordEdge_covered hm σ hσ s hs he) y
    rcases hcov with ⟨i, hi⟩ | ⟨i, hi⟩
    · have hlev := hlevel (Sum.inl i)
      change matchingConstraint (by omega) y i = matchingConstraint (by omega) x i at hlev
      have hed : edgeConstraint y p q = 4 := by
        rw [hi, hlev, hmatch i]
      unfold edgeConstraint at hed
      nlinarith [norm_nonneg (y p - y q)]
    · have hlev := hlevel (Sum.inr i)
      change selectedConstraint (by omega) s y i = selectedConstraint (by omega) s x i at hlev
      have hed : edgeConstraint y p q = 4 := by
        rw [hi, hlev, hselected i]
      unfold edgeConstraint at hed
      nlinarith [norm_nonneg (y p - y q)]
  · have hlt := hy p q he
    unfold edgeConstraint at hlt
    nlinarith [norm_nonneg (y p - y q)]

theorem logDiscriminant_localMaxOn_activeLevel {m : ℕ} (hm : 2 ≤ m)
    (σ : Fin (2 * m) → ℝ) (hσ : Antiperiodic (by omega) σ)
    (s : Fin m → ℝ) (hs : ∀ i, s i = σ (CommonClosureEnergy.halfIndex i))
    (x : Points (2 * m)) (hx : ExtremalNormalization.DiameterExtremal x)
    (hxinj : Function.Injective x) (hdisc : 1 ≤ discriminant x)
    (hgraph : ∀ p q, ‖x p - x q‖ = 2 ↔ WordEdge σ p q)
    (hmatch : ∀ i, matchingConstraint (by omega) x i = 4)
    (hselected : ∀ i, selectedConstraint (by omega) s x i = 4) :
    IsLocalMaxOn logDiscriminant (activeLevelSet (by omega) s x) x := by
  have hnear := eventually_diameter_on_activeLevel hm σ hσ s hs x hx.1 hgraph hmatch hselected
  change ∀ᶠ y in 𝓝[activeLevelSet (by omega) s x] x,
    logDiscriminant y ≤ logDiscriminant x
  filter_upwards [hnear.filter_mono inf_le_left, self_mem_nhdsWithin] with y hy hlevel
  have hD := hx.2 y (hy hlevel)
  by_cases hzero : discriminant y = 0
  · unfold logDiscriminant
    rw [hzero, Real.log_zero]
    exact Real.log_nonneg hdisc
  · unfold logDiscriminant
    have hypos : 0 < discriminant y :=
      lt_of_le_of_ne (discriminant_nonneg y) (Ne.symm hzero)
    exact Real.strictMonoOn_log.monotoneOn hypos (discriminant_pos x hxinj) hD

structure Multipliers {m : ℕ} (hm : 0 < m) (s : Fin m → ℝ)
    (x : Points (2 * m)) where
  matching : Fin m → ℝ
  crossing : Fin m → ℝ
  stationarity : ∀ U : Points (2 * m),
    fderiv ℝ logDiscriminant x U =
      (∑ i, matching i * edgeDifferential x U (matchingFirst i) (matchingSecond hm i)) +
      ∑ i, crossing i * edgeDifferential x U
        (selectedFirst hm s i) (selectedSecond hm s i)

theorem exists_multipliers {m : ℕ} (hm : 2 ≤ m)
    (σ : Fin (2 * m) → ℝ) (hσ : Antiperiodic (by omega) σ)
    (s : Fin m → ℝ) (hs : ∀ i, s i = σ (CommonClosureEnergy.halfIndex i))
    (x : Points (2 * m)) (hx : ExtremalNormalization.DiameterExtremal x)
    (hxinj : Function.Injective x) (hdisc : 1 ≤ discriminant x)
    (hgraph : ∀ p q, ‖x p - x q‖ = 2 ↔ WordEdge σ p q)
    (hmatch : ∀ i, matchingConstraint (by omega) x i = 4)
    (hselected : ∀ i, selectedConstraint (by omega) s x i = 4)
    (hind : ActiveConstraintDifferentialsIndependent (by omega) s x) :
    Nonempty (Multipliers (by omega) s x) := by
  have hlocal := logDiscriminant_localMaxOn_activeLevel hm σ hσ s hs x hx hxinj hdisc
    hgraph hmatch hselected
  have hstrict (k : Sum (Fin m) (Fin m)) :
      HasStrictFDerivAt (activeConstraint (by omega) s k)
        (fderiv ℝ (activeConstraint (by omega) s k) x) x :=
    (activeConstraint_contDiff (by omega) s k).contDiffAt.hasStrictFDerivAt
      (by norm_num : (∞ : WithTop ℕ∞) ≠ 0)
  have hobj := (logDiscriminant_contDiffAt hxinj).hasStrictFDerivAt
    (by norm_num : (∞ : WithTop ℕ∞) ≠ 0)
  obtain ⟨Λ, Λ₀, hnonzero, hrelation⟩ :=
    (show IsLocalExtrOn logDiscriminant (activeLevelSet (by omega) s x) x from Or.inr hlocal).exists_multipliers_of_hasStrictFDerivAt hstrict hobj
  have hΛ₀ : Λ₀ ≠ 0 := by
    intro hz
    have hsum (U : Points (2 * m)) :
        (∑ i, Λ (Sum.inl i) * edgeDifferential x U (matchingFirst i)
            (matchingSecond (by omega) i)) +
          ∑ i, Λ (Sum.inr i) * edgeDifferential x U
            (selectedFirst (by omega) s i) (selectedSecond (by omega) s i) = 0 := by
      rw [Fintype.sum_sum_type] at hrelation
      have hr := congrArg (fun L => L U) hrelation
      simp only [add_apply, sum_apply, smul_apply, zero_apply,
        smul_eq_mul, hz, zero_mul, add_zero] at hr
      simpa only [fderiv_activeConstraint_apply] using hr
    obtain ⟨hM, hX⟩ := hind (fun i => Λ (Sum.inl i)) (fun i => Λ (Sum.inr i)) hsum
    apply hnonzero
    simp only [Prod.mk_eq_zero, hz, and_true]
    funext k
    rcases k with i | i
    · exact congrFun hM i
    · exact congrFun hX i
  let lamM : Fin m → ℝ := fun i => -Λ (Sum.inl i) / Λ₀
  let lamX : Fin m → ℝ := fun i => -Λ (Sum.inr i) / Λ₀
  refine ⟨⟨lamM, lamX, ?_⟩⟩
  intro U
  rw [Fintype.sum_sum_type] at hrelation
  have hr := congrArg (fun L => L U) hrelation
  simp only [add_apply, sum_apply, smul_apply, zero_apply, smul_eq_mul] at hr
  simp only [fderiv_activeConstraint_apply] at hr
  dsimp only [lamM, lamX]
  simp_rw [div_mul_eq_mul_div, neg_mul]
  rw [← Finset.sum_div, ← Finset.sum_div,
    Finset.sum_neg_distrib, Finset.sum_neg_distrib]
  field_simp [hΛ₀]
  linear_combination hr

theorem multipliers_unique {m : ℕ} (hm : 0 < m) (s : Fin m → ℝ)
    (x : Points (2 * m)) (hind : ActiveConstraintDifferentialsIndependent hm s x)
    (K L : Multipliers hm s x) : K = L := by
  have hrel (U : Points (2 * m)) :
      (∑ i, (K.matching i - L.matching i) *
        edgeDifferential x U (matchingFirst i) (matchingSecond hm i)) +
      ∑ i, (K.crossing i - L.crossing i) *
        edgeDifferential x U (selectedFirst hm s i) (selectedSecond hm s i) = 0 := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
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

end
end StructuralNote.MatchingActivityKKTAnalytic
