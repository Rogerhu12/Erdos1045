import StructuralNote.ExplicitHessianThresholdFixedSchur
import StructuralNote.ExplicitHessianThresholdFixedSchurGeometry
import StructuralNote.ExplicitComparisonGeometry
import StructuralNote.ExplicitComparisonRotated
import StructuralNote.FixedSchurChosenLinearization
import StructuralNote.FixedSchurQuadraticDerivatives
import StructuralNote.FixedSchurChosenRemainderSecond
import StructuralNote.FixedSchurObjectivePaths

/-! Explicit pointwise path identities on the chosen fixed-Schur chart. -/

namespace StructuralNote.ExplicitCanonicalEntryObjectivePaths

open Complex Filter
open Erdos1045 Erdos1045.EventualExact
open FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open CommonClosureEnergy CommonDomainClosure CommonTangentialParameters
open CommonFiberSmooth CommonFiberCanonical CommonFiberCanonicalPaths
open CommonFiberCanonicalDirections CommonFiberGeometry
open EdgeCoordinates FixedSchurData FixedSchurEquationSmooth FixedSchurLinear
open FixedSchurHarmonicBounds FixedSchurNormalExpansion
open FixedSchurChart FixedSchurChartSmooth FixedSchurChartRotated
open FixedSchurRotatedPath FixedSchurRotatedSecondPath
open FixedSchurRotatedCoefficients FixedSchurFirstSource
open FixedSchurChosenPath FixedSchurChosenLinearization
open FixedSchurQuadraticDerivatives FixedSchurConfigurationDerivatives
open FixedSchurObjectivePaths LogDiscriminantSecondDerivative
open FixedSchurChosenRemainderSecond FixedSchurChartQuotients
open FixedSchurChartRemainder FixedSchurRemainderIdentity
open FixedSchurRemainderScalar
open FixedSchurGeometricRemainderHessian FixedSchurObjective
open GeometricRelativeRemainder SignedPressureAngular
open ExplicitHessianThreshold ExplicitHessianThresholdFixedSchur
open scoped BigOperators Topology ContDiff

noncomputable section

theorem chosenQPath_contDiffAt {m : ℕ}
    (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m)
    (hm : 0 < m) (w : FiniteBox.SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (hx : InDomain hm θ v) (hd : Admissible hm (η, h)) :
    ContDiffAt ℝ ∞ (chosenQPath hm w θ η v h) 0 := by
  let x : SchurParameters m := (θ, v)
  let d : SchurParameters m := (η, h)
  have hx' : InDomain hm x.1 x.2 := by simpa only [x]
  have hd' : Admissible hm d := by simpa only [d]
  have hdom0 := affine_domain_near_zero hm x d hx' hd'
  have hdom : ∀ᶠ z in 𝓝 (0 : ℝ),
      InDomain hm (chosenParameterPath θ η v h z).1
        (chosenParameterPath θ η v h z).2 := by
    simpa only [chosenParameterPath, x, d, CommonFiberCanonical.domain,
      Set.mem_ofPred_eq] using hdom0
  obtain ⟨g, hgx, hg, he⟩ := local_model hN hm w x hx'
  have hp : ContDiffAt ℝ ∞ (chosenParameterPath θ η v h) 0 := by
    unfold chosenParameterPath affinePath
    fun_prop
  have htend : Tendsto (chosenParameterPath θ η v h) (𝓝 (0 : ℝ)) (𝓝 x) := by
    rw [← show chosenParameterPath θ η v h 0 = x by
      simp [chosenParameterPath, affinePath, x]]
    exact hp.continuousAt
  have heq : ∀ᶠ z in 𝓝 (0 : ℝ),
      chosenQPath hm w θ η v h z = g (chosenParameterPath θ η v h z) := by
    filter_upwards [htend.eventually he, hdom] with z hz hzdom
    simpa only [chosenQPath] using (hz.2.2 hzdom).symm
  have hg0 : ContDiffAt ℝ ∞ g (chosenParameterPath θ η v h 0) := by
    simpa only [chosenParameterPath, x, d, affinePath, zero_smul, add_zero] using hg
  exact (hg0.comp 0 hp).congr_of_eventuallyEq heq

private theorem contDiffAt_second_derivatives {f : ℝ → ℝ}
    (hf : ContDiffAt ℝ ∞ f 0) :
    (∀ᶠ z in 𝓝 (0 : ℝ), HasDerivAt f (deriv f z) z) ∧
      HasDerivAt (deriv f) (deriv (deriv f) 0) 0 := by
  have hf2 : ContDiffAt ℝ 2 f 0 :=
    hf.of_le (WithTop.coe_le_coe.mpr le_top)
  constructor
  · filter_upwards [hf2.eventually (by norm_num)] with z hz
    exact (hz.differentiableAt (by norm_num)).hasDerivAt
  · have hd : ContDiffAt ℝ 1 (deriv f) 0 := hf2.derivWithin (by norm_num)
    exact (hd.differentiableAt (by norm_num)).hasDerivAt

theorem chosen_path_jets {m : ℕ}
    (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m)
    (hm : 2 ≤ m) (w : FiniteBox.SignPattern (by omega))
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (hx : InDomain (by omega) θ v) (hd : Admissible (by omega) (η, h)) :
    ∀ j : Fin (2 * m),
      (∀ᶠ z in 𝓝 (0 : ℝ),
        HasDerivAt (fun y : ℝ => chosenQPath (by omega) w θ η v h y j)
          (chosenQFirstPath (by omega) w θ η v h j z) z) ∧
      (∀ᶠ z in 𝓝 (0 : ℝ),
        HasDerivAt (chosenPPath (by omega) w θ η v h j)
          (chosenPFirstPath (by omega) w θ η v h j z) z) ∧
      HasDerivAt (chosenQFirstPath (by omega) w θ η v h j)
        (chosenQSecond (by omega) w θ η v h j) 0 ∧
      HasDerivAt (chosenPFirstPath (by omega) w θ η v h j)
        (chosenPSecond (by omega) w θ η v h j) 0 := by
  intro j
  have hqv := chosenQPath_contDiffAt hN (by omega) w θ η v h hx hd
  have hq : ContDiffAt ℝ ∞
      (fun z : ℝ => chosenQPath (by omega) w θ η v h z j) 0 := by
    exact (contDiffAt_apply ℝ ℝ j _).comp 0 hqv
  have hp := FixedSchurChosenPath.chosenPPath_contDiffAt
    (by omega) w θ η v h j hqv
  have hqjet := contDiffAt_second_derivatives hq
  have hpjet := contDiffAt_second_derivatives hp
  simpa only [chosenQFirstPath, chosenPFirstPath, chosenQSecond,
    chosenPSecond] using ⟨hqjet.1, hpjet.1, hqjet.2, hpjet.2⟩

private theorem J_smul {n : ℕ} (c : ℝ) (q : Fin n → ℝ) :
    J (c • q) = c • J q := by
  have hfc : firstCoefficient (c • q) = (c : ℂ) * firstCoefficient q := by
    unfold firstCoefficient
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
    calc
      (∑ x, (c : ℂ) * (q x : ℂ) * (starRingEnd ℂ) (frame n x)) / (n : ℂ) =
          ((c : ℂ) * ∑ x, (q x : ℂ) * (starRingEnd ℂ) (frame n x)) / (n : ℂ) := by
            congr 1
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = (c : ℂ) *
          ((∑ x, (q x : ℂ) * (starRingEnd ℂ) (frame n x)) / (n : ℂ)) := by ring
  funext j
  simp only [J, hfc, Pi.smul_apply, smul_eq_mul, mul_assoc, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  ring

private def JLinearMap {n : ℕ} (hn : 0 < n) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  LinearMap.mkContinuous
    { toFun := J
      map_add' := J_add
      map_smul' := J_smul }
    2 (J_norm_le hn)

private def JCoordinateMap {n : ℕ} (hn : 0 < n) (j : Fin n) :
    (Fin n → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j).comp (JLinearMap hn)

private theorem tangent_smul {m : ℕ} (hm : 0 < m) (c : ℝ)
    (h : Fin (2 * m) → ℂ) :
    tangent (by omega) (c • h) = c • tangent (by omega) h := by
  funext j
  have he : edgeRatio (by omega) (c • h) j =
      (c : ℂ) * edgeRatio (by omega) h j := by
    unfold edgeRatio LocalDFT.pairRatio periodize
    simp only [Pi.smul_apply, Complex.real_smul]
    ring
  unfold tangent
  rw [he]
  simp
  ring

private theorem hasDerivAt_tangent_parameterPath {m : ℕ} (hm : 2 ≤ m)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (j : Fin (2 * m)) (z : ℝ) :
    HasDerivAt
      (fun y : ℝ => tangent (by omega) (chosenParameterPath θ η v h y).2 j)
      (tangent (by omega) h j) z := by
  have heq :
      (fun y : ℝ => tangent (by omega) (chosenParameterPath θ η v h y).2 j) =
        fun y : ℝ => tangent (by omega) v j + y * tangent (by omega) h j := by
    funext y
    rw [show (chosenParameterPath θ η v h y).2 = v + y • h by
      rfl, tangent_add hm, tangent_smul (by omega)]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [heq]
  have ht := (hasDerivAt_const z (tangent (by omega) v j)).add
    ((hasDerivAt_id z).mul_const (tangent (by omega) h j))
  change HasDerivAt
    ((fun _ : ℝ => tangent (by omega) v j) +
      fun y : ℝ => y * tangent (by omega) h j)
    (tangent (by omega) h j) z
  simpa only [id_eq, zero_add, one_mul] using ht

private theorem chosenPFirst_eq_aux {m : ℕ} (hm : 2 ≤ m)
    (w : FiniteBox.SignPattern (by omega))
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (z : ℝ)
    (hqv : DifferentiableAt ℝ (chosenQPath (by omega) w θ η v h) z)
    (hq : ∀ i : Fin (2 * m),
      HasDerivAt (fun y : ℝ => chosenQPath (by omega) w θ η v h y i)
        (chosenQFirstPath (by omega) w θ η v h i z) z)
    (hp : ∀ j : Fin (2 * m),
      HasDerivAt (chosenPPath (by omega) w θ η v h j)
        (chosenPFirstPath (by omega) w θ η v h j z) z) :
    (fun j => chosenPFirstPath (by omega) w θ η v h j z) =
      J (fun i => chosenQFirstPath (by omega) w θ η v h i z) +
        tangent (by omega) h := by
  let qdot : Fin (2 * m) → ℝ :=
    (fderiv ℝ (chosenQPath (by omega) w θ η v h) z) 1
  have hqdot : qdot =
      fun i => chosenQFirstPath (by omega) w θ η v h i z := by
    funext i
    have hi := ((ContinuousLinearMap.proj i).hasFDerivAt.comp z
      hqv.hasFDerivAt).hasDerivAt
    exact hi.unique (hq i)
  funext j
  have hJ := ((JCoordinateMap (show 0 < 2 * m by omega) j).hasFDerivAt.comp z
    hqv.hasFDerivAt).hasDerivAt
  have ht := hasDerivAt_tangent_parameterPath hm θ η v h j z
  have hsum := hJ.add ht
  have hp' : HasDerivAt (chosenPPath (by omega) w θ η v h j)
      (J qdot j + tangent (by omega) h j) z := by
    change HasDerivAt
      (fun y : ℝ => J (chosenQPath (by omega) w θ η v h y) j +
        tangent (by omega) (chosenParameterPath θ η v h y).2 j)
      (J qdot j + tangent (by omega) h j) z
    have hsum' := hsum.congr_of_eventuallyEq
      (f₁ := fun y : ℝ => J (chosenQPath (by omega) w θ η v h y) j +
        tangent (by omega) (chosenParameterPath θ η v h y).2 j) (by
        filter_upwards [] with y
        simp [JCoordinateMap, JLinearMap])
    exact hsum'.congr_deriv (by simp [JCoordinateMap, JLinearMap, qdot])
  rw [← hqdot]
  exact (hp j).unique hp'

theorem chosenP_derivatives {m : ℕ}
    (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m)
    (hm : 2 ≤ m) (w : FiniteBox.SignPattern (by omega))
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (hx : InDomain (by omega) θ v) (hd : Admissible (by omega) (η, h)) :
    (fun j => chosenPFirstPath (by omega) w θ η v h j 0) =
        J (fun i => chosenQFirstPath (by omega) w θ η v h i 0) +
          tangent (by omega) h ∧
    (fun j => chosenPSecond (by omega) w θ η v h j) =
        J (fun i => chosenQSecond (by omega) w θ η v h i) := by
  have hqv := chosenQPath_contDiffAt hN (by omega) w θ η v h hx hd
  have hjets := chosen_path_jets hN hm w θ η v h hx hd
  have hqv1 : ContDiffAt ℝ 1
      (chosenQPath (by omega) w θ η v h) 0 :=
    hqv.of_le (WithTop.coe_le_coe.mpr le_top)
  have hqdiff : ∀ᶠ z in 𝓝 (0 : ℝ),
      DifferentiableAt ℝ (chosenQPath (by omega) w θ η v h) z := by
    filter_upwards [hqv1.eventually (by norm_num)] with z hz
    exact hz.differentiableAt (by norm_num)
  have hq : ∀ᶠ z in 𝓝 (0 : ℝ), ∀ i : Fin (2 * m),
      HasDerivAt (fun y : ℝ => chosenQPath (by omega) w θ η v h y i)
        (chosenQFirstPath (by omega) w θ η v h i z) z := by
    rw [Filter.eventually_all]
    intro i
    exact (hjets i).1
  have hp : ∀ᶠ z in 𝓝 (0 : ℝ), ∀ j : Fin (2 * m),
      HasDerivAt (chosenPPath (by omega) w θ η v h j)
        (chosenPFirstPath (by omega) w θ η v h j z) z := by
    rw [Filter.eventually_all]
    intro j
    exact (hjets j).2.1
  have hfirst : ∀ᶠ z in 𝓝 (0 : ℝ),
      (fun j => chosenPFirstPath (by omega) w θ η v h j z) =
        J (fun i => chosenQFirstPath (by omega) w θ η v h i z) +
          tangent (by omega) h := by
    filter_upwards [hqdiff, hq, hp] with z hzd hzq hzp
    exact chosenPFirst_eq_aux hm w θ η v h z hzd hzq hzp
  refine ⟨hfirst.self_of_nhds, ?_⟩
  let q₁ : ℝ → (Fin (2 * m) → ℝ) :=
    fun z i => chosenQFirstPath (by omega) w θ η v h i z
  have hq₁diff : DifferentiableAt ℝ q₁ 0 := by
    apply differentiableAt_pi.mpr
    intro i
    exact (hjets i).2.2.1.differentiableAt
  let q₂ : Fin (2 * m) → ℝ := (fderiv ℝ q₁ 0) 1
  have hq₂ : q₂ = fun i => chosenQSecond (by omega) w θ η v h i := by
    funext i
    have hi := ((ContinuousLinearMap.proj i).hasFDerivAt.comp 0
      hq₁diff.hasFDerivAt).hasDerivAt
    exact hi.unique (hjets i).2.2.1
  funext j
  have hJ := ((JCoordinateMap (show 0 < 2 * m by omega) j).hasFDerivAt.comp 0
    hq₁diff.hasFDerivAt).hasDerivAt
  have hJ' : HasDerivAt
      (fun z : ℝ => J (q₁ z) j + tangent (by omega) h j)
      (J q₂ j) 0 := by
    have hsum := hJ.add_const (tangent (by omega) h j)
    have hsum' := hsum.congr_of_eventuallyEq
      (f₁ := fun z : ℝ => J (q₁ z) j + tangent (by omega) h j) (by
        filter_upwards [] with z
        simp [JCoordinateMap, JLinearMap])
    exact hsum'.congr_deriv (by simp [JCoordinateMap, JLinearMap, q₂])
  have hpsecond : HasDerivAt
      (chosenPFirstPath (by omega) w θ η v h j)
      (J q₂ j) 0 := by
    apply hJ'.congr_of_eventuallyEq
    filter_upwards [hfirst] with z hz
    simpa only [q₁, Pi.add_apply] using congrFun hz j
  rw [← hq₂]
  exact (hjets j).2.2.2.unique hpsecond

private theorem branch_constraint_and_height {ε σ a b q p : ℝ}
    (hε : 0 < ε) (hσ : σ = 1 ∨ σ = -1)
    (hroot : FixedSchurRotatedPath.r q p b = σ / ε *
      (FixedSchurRotatedPath.H ε (FixedSchurRotatedPath.s q p b) -
        FixedSchurRotatedPath.L a))
    (hpos : 0 < FixedSchurRotatedPath.L a + σ * ε *
      FixedSchurRotatedPath.r q p b) :
    0 < FixedSchurRotatedPath.H ε (FixedSchurRotatedPath.s q p b) ∧
      FixedSchurRotatedPath.r q p b + σ / ε *
        (FixedSchurRotatedPath.L a -
          FixedSchurRotatedPath.H ε (FixedSchurRotatedPath.s q p b)) = 0 := by
  have hσsq : σ ^ 2 = 1 := by
    rcases hσ with rfl | rfl <;> norm_num
  have heq : FixedSchurRotatedPath.L a + σ * ε * FixedSchurRotatedPath.r q p b =
      FixedSchurRotatedPath.H ε (FixedSchurRotatedPath.s q p b) := by
    rw [hroot]
    field_simp [hε.ne']
    rw [hσsq]
    ring
  constructor
  · rwa [← heq]
  · rw [hroot]
    field_simp [hε.ne']
    ring

theorem chosen_path_constraint {m : ℕ}
    (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m)
    (hm : 2 ≤ m) (w : FiniteBox.SignPattern (by omega))
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (hx : InDomain (by omega) θ v) (hd : Admissible (by omega) (η, h))
    (j : Fin (2 * m)) :
    (∀ᶠ z in 𝓝 (0 : ℝ),
      0 < H (epsilon (2 * m))
        (tangentialPath
          (fun y : ℝ => chosenQPath (by omega) w θ η v h y j)
          (chosenPPath (by omega) w θ η v h j)
          (chosenBPath (by omega) θ η j) z)) ∧
    (∀ᶠ z in 𝓝 (0 : ℝ),
      constraintPath (epsilon (2 * m)) (FiniteBox.patternSign w j)
        (fun y : ℝ => chosenQPath (by omega) w θ η v h y j)
        (chosenPPath (by omega) w θ η v h j)
        (chosenAPath (by omega) θ η j)
        (chosenBPath (by omega) θ η j) z = 0) := by
  have hrot := ExplicitComparisonRotated.coordinate_rotated hN
  let x : SchurParameters m := (θ, v)
  let d : SchurParameters m := (η, h)
  have hx' : InDomain (by omega) x.1 x.2 := by simpa only [x] using hx
  have hd' : Admissible (by omega) d := by simpa only [d] using hd
  have hdom0 := affine_domain_near_zero (by omega) x d hx' hd'
  have hdom : ∀ᶠ z in 𝓝 (0 : ℝ),
      InDomain (by omega) (chosenParameterPath θ η v h z).1
        (chosenParameterPath θ η v h z).2 := by
    simpa only [chosenParameterPath, x, d, CommonFiberCanonical.domain,
      Set.mem_ofPred_eq] using hdom0
  have hgeom : ∀ᶠ z in 𝓝 (0 : ℝ),
      (0 < chordLength (by omega) (chosenParameterPath θ η v h z).1 j +
        FiniteBox.patternSign w j * epsilon (2 * m) *
          FixedSchurRotatedAlgebra.radial
            (angleAverage (by omega) (chosenParameterPath θ η v h z).1 j)
            (chosenQPath (by omega) w θ η v h z j)
            (chosenPPath (by omega) w θ η v h j z)) ∧
      FixedSchurRotatedAlgebra.radial
          (angleAverage (by omega) (chosenParameterPath θ η v h z).1 j)
          (chosenQPath (by omega) w θ η v h z j)
          (chosenPPath (by omega) w θ η v h j z) =
        FiniteBox.patternSign w j / epsilon (2 * m) *
          (Real.sqrt (4 -
            (epsilon (2 * m) *
              FixedSchurRotatedAlgebra.tangential
                (angleAverage (by omega) (chosenParameterPath θ η v h z).1 j)
                (chosenQPath (by omega) w θ η v h z j)
                (chosenPPath (by omega) w θ η v h j z)) ^ 2) -
            chordLength (by omega) (chosenParameterPath θ η v h z).1 j) := by
    filter_upwards [hdom] with z hz
    exact ⟨(hrot hm w _ _ hz j).2.2.2.1,
      (hrot hm w _ _ hz j).2.2.2.2.1⟩
  constructor <;> filter_upwards [hgeom] with z hz
  · have hroot :
        FixedSchurRotatedPath.r (chosenQPath (by omega) w θ η v h z j)
            (chosenPPath (by omega) w θ η v h j z)
            (chosenBPath (by omega) θ η j z) =
          FiniteBox.patternSign w j / epsilon (2 * m) *
            (FixedSchurRotatedPath.H (epsilon (2 * m))
              (FixedSchurRotatedPath.s (chosenQPath (by omega) w θ η v h z j)
                (chosenPPath (by omega) w θ η v h j z)
                (chosenBPath (by omega) θ η j z)) -
              FixedSchurRotatedPath.L (chosenAPath (by omega) θ η j z)) := by
      simpa [FixedSchurRotatedPath.r, FixedSchurRotatedPath.s,
        FixedSchurRotatedAlgebra.radial, FixedSchurRotatedAlgebra.tangential,
        FixedSchurRotatedPath.L, FixedSchurRotatedPath.H, chosenAPath, chosenBPath,
        chosenParameterPath, affinePath, chordLength] using hz.2
    have hpos : 0 < FixedSchurRotatedPath.L (chosenAPath (by omega) θ η j z) +
        FiniteBox.patternSign w j * epsilon (2 * m) *
          FixedSchurRotatedPath.r (chosenQPath (by omega) w θ η v h z j)
            (chosenPPath (by omega) w θ η v h j z)
            (chosenBPath (by omega) θ η j z) := by
      simpa [FixedSchurRotatedPath.r, FixedSchurRotatedAlgebra.radial,
        FixedSchurRotatedPath.L, chosenAPath, chosenBPath, chosenParameterPath,
        affinePath, chordLength] using hz.1
    exact (branch_constraint_and_height (epsilon_pos (by omega))
      (FiniteBox.patternSign_is_sign w j) hroot hpos).1
  · have hroot :
        FixedSchurRotatedPath.r (chosenQPath (by omega) w θ η v h z j)
            (chosenPPath (by omega) w θ η v h j z)
            (chosenBPath (by omega) θ η j z) =
          FiniteBox.patternSign w j / epsilon (2 * m) *
            (FixedSchurRotatedPath.H (epsilon (2 * m))
              (FixedSchurRotatedPath.s (chosenQPath (by omega) w θ η v h z j)
                (chosenPPath (by omega) w θ η v h j z)
                (chosenBPath (by omega) θ η j z)) -
              FixedSchurRotatedPath.L (chosenAPath (by omega) θ η j z)) := by
      simpa [FixedSchurRotatedPath.r, FixedSchurRotatedPath.s,
        FixedSchurRotatedAlgebra.radial, FixedSchurRotatedAlgebra.tangential,
        FixedSchurRotatedPath.L, FixedSchurRotatedPath.H, chosenAPath, chosenBPath,
        chosenParameterPath, affinePath, chordLength] using hz.2
    have hpos : 0 < FixedSchurRotatedPath.L (chosenAPath (by omega) θ η j z) +
        FiniteBox.patternSign w j * epsilon (2 * m) *
          FixedSchurRotatedPath.r (chosenQPath (by omega) w θ η v h z j)
            (chosenPPath (by omega) w θ η v h j z)
            (chosenBPath (by omega) θ η j z) := by
      simpa [FixedSchurRotatedPath.r, FixedSchurRotatedAlgebra.radial,
        FixedSchurRotatedPath.L, chosenAPath, chosenBPath, chosenParameterPath,
        affinePath, chordLength] using hz.1
    simpa only [constraintPath, radialPath, tangentialPath] using
      (branch_constraint_and_height (epsilon_pos (by omega))
        (FiniteBox.patternSign_is_sign w j) hroot hpos).2

theorem chosen_rotated_identities {m : ℕ}
    (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m)
    (hm : 2 ≤ m) (w : FiniteBox.SignPattern (by omega))
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (hx : InDomain (by omega) θ v) (hd : Admissible (by omega) (η, h))
    (j : Fin (2 * m)) :
    alpha (epsilon (2 * m)) (FiniteBox.patternSign w j)
        (chosenBPath (by omega) θ η j 0)
        (chosenS (by omega) w θ η v h j) *
        chosenQFirstPath (by omega) w θ η v h j 0 +
      beta (epsilon (2 * m)) (FiniteBox.patternSign w j)
        (chosenBPath (by omega) θ η j 0)
        (chosenS (by omega) w θ η v h j) *
        chosenPFirstPath (by omega) w θ η v h j 0 =
      FiniteBox.patternSign w j / epsilon (2 * m) *
          Real.sin (chosenAPath (by omega) θ η j 0) *
            angleDifferenceDirection (by omega) η j -
        (L (chosenAPath (by omega) θ η j 0) /
            H (epsilon (2 * m)) (chosenS (by omega) w θ η v h j)) *
          chosenS (by omega) w θ η v h j *
            angleAverageDirection (by omega) η j ∧
    alpha (epsilon (2 * m)) (FiniteBox.patternSign w j)
        (chosenBPath (by omega) θ η j 0)
        (chosenS (by omega) w θ η v h j) *
        chosenQSecond (by omega) w θ η v h j +
      beta (epsilon (2 * m)) (FiniteBox.patternSign w j)
        (chosenBPath (by omega) θ η j 0)
        (chosenS (by omega) w θ η v h j) *
        chosenPSecond (by omega) w θ η v h j =
      FiniteBox.patternSign w j / (2 * epsilon (2 * m)) *
          Real.cos (chosenAPath (by omega) θ η j 0) *
            angleDifferenceDirection (by omega) η j ^ 2 -
        2 * chosenT (by omega) w θ η v h j *
          angleAverageDirection (by omega) η j +
        chosenR (by omega) w θ η v h j *
          angleAverageDirection (by omega) η j ^ 2 +
        FiniteBox.patternSign w j * epsilon (2 * m) *
            chosenS (by omega) w θ η v h j /
            H (epsilon (2 * m)) (chosenS (by omega) w θ η v h j) *
          (2 * chosenU (by omega) w θ η v h j *
              angleAverageDirection (by omega) η j +
            chosenS (by omega) w θ η v h j *
              angleAverageDirection (by omega) η j ^ 2) -
        4 * FiniteBox.patternSign w j * epsilon (2 * m) /
            H (epsilon (2 * m)) (chosenS (by omega) w θ η v h j) ^ 3 *
          (chosenT (by omega) w θ η v h j -
            chosenR (by omega) w θ η v h j *
              angleAverageDirection (by omega) η j) ^ 2 := by
  have hj := chosen_path_jets hN hm w θ η v h hx hd j
  have hc := chosen_path_constraint hN hm w θ η v h hx hd j
  have ha : ∀ᶠ z in 𝓝 (0 : ℝ),
      HasDerivAt (chosenAPath (by omega) θ η j)
        (angleDifferenceDirection (by omega) η j / 2) z :=
    Filter.Eventually.of_forall (hasDerivAt_chosenAPath (by omega) θ η j)
  have hb : ∀ᶠ z in 𝓝 (0 : ℝ),
      HasDerivAt (chosenBPath (by omega) θ η j)
        (angleAverageDirection (by omega) η j) z :=
    Filter.Eventually.of_forall (hasDerivAt_chosenBPath (by omega) θ η j)
  have hfirst := rotated_first_derivative
    (epsilon_pos (show 2 ≤ 2 * m by omega))
    (FiniteBox.patternSign_is_sign w j)
    hj.1.self_of_nhds hj.2.1.self_of_nhds ha.self_of_nhds hb.self_of_nhds
    hc.1.self_of_nhds hc.2
  have hsecond := rotated_second_derivative
    (epsilon_pos (show 2 ≤ 2 * m by omega))
    (FiniteBox.patternSign_is_sign w j)
    hj.1 hj.2.1 hj.2.2.1 hj.2.2.2 ha hb hc.1 hc.2
  simpa only [chosenR, chosenS, chosenU, chosenT] using ⟨hfirst, hsecond⟩

@[simp] private theorem chosenAPath_zero {m : ℕ} (hm : 0 < m)
    (θ η : Fin (2 * m) → ℝ) (j : Fin (2 * m)) :
    chosenAPath hm θ η j 0 =
      Real.pi / (2 * m : ℝ) + angleDifference (by omega) θ j / 2 := by
  simp [chosenAPath, chosenParameterPath, CommonFiberCanonicalPaths.affinePath]

@[simp] private theorem chosenBPath_zero {m : ℕ} (hm : 0 < m)
    (θ η : Fin (2 * m) → ℝ) (j : Fin (2 * m)) :
    chosenBPath hm θ η j 0 = angleAverage (by omega) θ j := by
  simp [chosenBPath, chosenParameterPath, CommonFiberCanonicalPaths.affinePath]

@[simp] private theorem chosenS_eq_rotatedS {m : ℕ} (hm : 0 < m)
    (w : FiniteBox.SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (j : Fin (2 * m)) :
    chosenS hm w θ η v h j =
      rotatedS (by omega) θ v (coordinate hm w θ v) j := by
  simp [chosenS, tangentialPath, FixedSchurRotatedPath.s,
    FixedSchurNormalExpansion.rotatedS, FixedSchurRotatedAlgebra.tangential]

@[simp] private theorem chosenR_eq_baseRadial {m : ℕ} (hm : 0 < m)
    (w : FiniteBox.SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (j : Fin (2 * m)) :
    chosenR hm w θ η v h j =
      baseRadial hm w θ v j := by
  simp [chosenR, radialPath, FixedSchurRotatedPath.r, baseRadial,
    FixedSchurRotatedAlgebra.radial]

theorem chosen_normalLinearizations {m : ℕ}
    (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m)
    (hm : 2 ≤ m) (w : FiniteBox.SignPattern (by omega))
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (hx : InDomain (by omega) θ v) (hd : Admissible (by omega) (η, h)) :
    normalLinearization (by omega) w θ v
        (chosenFirstDerivative (by omega) w θ η v h) =
      source (by omega) w θ η v h ∧
    normalLinearization (by omega) w θ v
        (chosenSecondDerivative (by omega) w θ η v h) =
      secondSource (by omega) w θ η v h := by
  have hp := chosenP_derivatives hN hm w θ η v h hx hd
  have hi := chosen_rotated_identities hN hm w θ η v h hx hd
  constructor
  · funext j
    have hj := (hi j).1
    have hpj := congrFun hp.1 j
    rw [hpj] at hj
    simp only [Pi.add_apply] at hj
    unfold normalLinearization FixedSchurRotatedInverse.linearized
      chosenFirstDerivative source angularCoefficient rotationCoefficient
      coefficientA coefficientB
    simp only [chosenAPath_zero, chosenBPath_zero, chosenS_eq_rotatedS,
      angleDifferenceDirection, angleAverageDirection] at hj
    linear_combination hj
  · funext j
    have hj := (hi j).2
    have hpfirstj := congrFun hp.1 j
    have hqfirst :
        (fun i => chosenQFirstPath (by omega) w θ η v h i 0) =
          chosenFirstDerivative (by omega) w θ η v h := by
      rfl
    have hpfirstj' : chosenPFirstPath (by omega) w θ η v h j 0 =
        (J (chosenFirstDerivative (by omega) w θ η v h) +
          tangent (by omega) h) j := by
      rw [← hqfirst]
      exact hpfirstj
    have hU : chosenU (by omega) w θ η v h j =
        firstRadial (by omega) w θ η v h j := by
      simp [chosenU, UPath, firstRadial, chosenFirstDerivative,
        FixedSchurRotatedPath.r, FixedSchurRotatedAlgebra.radial,
        hpfirstj', Pi.add_apply]
    have hT : chosenT (by omega) w θ η v h j =
        firstTangential (by omega) w θ η v h j := by
      simp [chosenT, TPath, firstTangential, chosenFirstDerivative,
        FixedSchurRotatedPath.s, FixedSchurRotatedAlgebra.tangential,
        hpfirstj', Pi.add_apply]
    have hpj := congrFun hp.2 j
    rw [hpj] at hj
    simp only [chosenAPath_zero, chosenBPath_zero, chosenS_eq_rotatedS,
      chosenR_eq_baseRadial, hU, hT, angleDifferenceDirection,
      angleAverageDirection] at hj
    unfold normalLinearization FixedSchurRotatedInverse.linearized
      chosenSecondDerivative coefficientA coefficientB secondSource
    simpa only using hj

theorem chosen_quadratic_second {m : ℕ}
    (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m)
    (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (hdom : InDomain (by omega) θ v) (hdir : Admissible (by omega) (η, h)) :
    HasDerivAt (deriv (fun t => normalizedBoxEnergy (operator (2 * m))
      (chosenQPath (by omega) s θ η v h t)))
      (quadraticSecond (FixedSchurChart.coordinate (by omega) s θ v)
        (chosenFirstDerivative (by omega) s θ η v h)
        (chosenSecondDerivative (by omega) s θ η v h)) 0 := by
  have hj := chosen_path_jets hN hm s θ η v h hdom hdir
  have hq := Filter.eventually_all.mpr (fun j => (hj j).1)
  have hd := energy_second_derivative hq (fun j => (hj j).2.2.1)
  have hz : chosenQPath (by omega) s θ η v h 0 =
      FixedSchurChart.coordinate (by omega) s θ v := by
    simp [chosenQPath, chosenParameterPath, CommonFiberCanonicalPaths.affinePath]
  rw [hz] at hd
  exact hd

theorem remainder_identity {m : ℕ}
    (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m)
    (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (hdom : InDomain (by omega) θ v) :
    newRemainder (by omega) θ
        (FixedSchurLinear.center (coordinate (by omega) s θ v) v) =
      (∑ p : Fin (2 * m) × Fin (2 * m),
        (R (quotient (FixedSchurLinear.center (coordinate (by omega) s θ v) v)
            (root (2 * m)) p)
          (quotient (diameterVector θ - root (2 * m)) (root (2 * m)) p)).re) / 2 := by
  have hp := ExplicitHessianThresholdFixedSchur.coordinate_properties
    hN hm s θ v hdom
  have hq := ExplicitComparisonGeometry.quotient_properties hN hm s θ v hdom
  exact newRemainder_eq_sum (by omega) θ _ hdom.1
    (FixedSchurLinear.center_halfPeriodic hm _ v hp.antiperiodic
      hdom.2.2.1.1)
    hq.1 (HessianAngularReference.root_injective (by omega))
    (fun p => (hq.2.2.2 p).trans_lt (by norm_num))

theorem actual_remainder_second {m : ℕ}
    (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m)
    (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (hdom : InDomain (by omega) θ v) (hdir : Admissible (by omega) (η, h)) :
    HasDerivAt (deriv (fun t => newRemainder (by omega)
      (chosenParameterPath θ η v h t).1 (centerPath (by omega) s θ η v h t)))
      (analyticSecond (centerPath (by omega) s θ η v h 0)
        (angularErrorPath θ η v h 0)
        (centerVelocityPath (by omega) s θ η v h 0)
        (angularVelocityPath θ η v h 0)
        (canonicalLift (chosenSecondDerivative (by omega) s θ η v h))
        (angularAcceleration θ η)) 0 := by
  have hj := chosen_path_jets hN hm s θ η v h hdom hdir
  have hq := Filter.eventually_all.mpr (fun j => (hj j).1)
  have hn := affine_domain_near_zero (show 0 < m by omega)
    (θ, v) (η, h) hdom hdir
  have hfirst : ∀ᶠ t in 𝓝 (0 : ℝ),
      (∀ j, HasDerivAt (fun r => centerPath (by omega) s θ η v h r j)
        (centerVelocityPath (by omega) s θ η v h t j) t) ∧
      (∀ j, HasDerivAt (fun r => angularErrorPath θ η v h r j)
        (angularVelocityPath θ η v h t j) t) ∧
      (∀ p, ‖quotient (centerPath (by omega) s θ η v h t)
          (root (2 * m)) p‖ ≤ 1 / 4) ∧
      (∀ p, ‖quotient (angularErrorPath θ η v h t)
          (root (2 * m)) p‖ ≤ 1 / 4) := by
    filter_upwards [hq, hn] with t ht htdom
    have hb := ExplicitComparisonGeometry.quotient_properties
      hN hm s _ _ htdom
    exact ⟨centerPath_hasDerivAt (by omega) s θ η v h t ht,
      angularErrorPath_hasDerivAt θ η v h t, hb.2.1, hb.2.2.1⟩
  have hd := analytic_second_derivative hfirst
    (centerVelocityPath_hasDerivAt (by omega) s θ η v h
      (fun j => (hj j).2.2.1))
    (angularVelocityPath_hasDerivAt θ η v h)
  have he : (fun t : ℝ => newRemainder (by omega)
      (chosenParameterPath θ η v h t).1 (centerPath (by omega) s θ η v h t)) =ᶠ[𝓝 0]
      (fun t => analyticRemainder (centerPath (by omega) s θ η v h t)
        (angularErrorPath θ η v h t)) := by
    filter_upwards [hn] with t ht
    simpa only [centerPath, chosenQPath, chosenParameterPath, analyticRemainder,
      angularErrorPath, Complex.re_sum] using
      remainder_identity hN hm s _ _ ht
  exact hd.congr_of_eventuallyEq he.deriv

theorem actual_log_second_derivative {m : ℕ}
    (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m)
    (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (hdom : InDomain (by omega) θ v) (hdir : Admissible (by omega) (η, h)) :
    HasDerivAt (deriv (fun t => Real.log (Configuration.discriminant
      (configurationPath (by omega) s θ η v h t))))
      (second (FixedSchurChart.configuration (by omega) s θ v)
        (velocityPath (by omega) s θ η v h 0)
        (acceleration (by omega) s θ η v h)) 0 := by
  have hj := chosen_path_jets hN hm s θ η v h hdom hdir
  have hgeo := ExplicitHessianThresholdFixedSchurGeometry.geometric_properties
    hN hm s θ v hdom
  have hq : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ j,
      HasDerivAt (fun r => chosenQPath (by omega) s θ η v h r j)
        (chosenQFirstPath (by omega) s θ η v h j t) t :=
    Filter.eventually_all.mpr (fun j => (hj j).1)
  have hz : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ j,
      HasDerivAt (fun r => configurationPath (by omega) s θ η v h r j)
        (velocityPath (by omega) s θ η v h t j) t := by
    filter_upwards [hq] with t ht
    exact configurationPath_hasDerivAt (by omega) s θ η v h t ht
  have hv := velocityPath_hasDerivAt (by omega) s θ η v h
    (fun j => (hj j).2.2.1)
  have hi : Function.Injective (configurationPath (by omega) s θ η v h 0) := by
    simpa only [configurationPath, chosenParameterPath, affinePath, zero_smul, add_zero]
      using hgeo.injective
  simpa only [configurationPath, chosenParameterPath, affinePath, zero_smul, add_zero]
    using log_second_derivative hz hv hi

theorem affine_deriv2_eq {m : ℕ}
    (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m)
    (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
    (x d : SchurParameters m) (t : ℝ)
    (hx : affinePath x d t ∈ FixedSchurChartSmooth.domain (by omega))
    (hd : Admissible (by omega) d) :
    deriv (deriv (fun r => objective (by omega) s (affinePath x d r))) t =
      second
        (configuration (by omega) s (affinePath x d t).1 (affinePath x d t).2)
        (velocityPath (by omega) s (affinePath x d t).1 d.1
          (affinePath x d t).2 d.2 0)
        (acceleration (by omega) s (affinePath x d t).1 d.1
          (affinePath x d t).2 d.2) := by
  rw [← FixedSchurObjectivePaths.affine_deriv2_shift (by omega) s x d t]
  exact (actual_log_second_derivative hN hm s _ _ _ _ hx hd).deriv

end
end StructuralNote.ExplicitCanonicalEntryObjectivePaths
