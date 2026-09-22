import StructuralNote.FixedSchurChosenPath
import StructuralNote.FixedSchurRotatedCoefficients
import StructuralNote.FixedSchurFirstSource

/-! Vector form of the differentiated identities on the chosen chart. -/

namespace StructuralNote.FixedSchurChosenLinearization

open Complex Filter
open Erdos1045 Erdos1045.EventualExact
open FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open CommonClosureEnergy CommonDomainClosure CommonTangentialParameters
open CommonFiberCanonicalDirections
open EdgeCoordinates FixedSchurData FixedSchurLinear FixedSchurHarmonicBounds
open FixedSchurChart FixedSchurNormalExpansion
open FixedSchurRotatedPath FixedSchurRotatedSecondPath FixedSchurRotatedCoefficients
open FixedSchurFirstSource FixedSchurChosenPath
open scoped BigOperators Topology ContDiff

noncomputable section

private theorem J_smul {n : ℕ} (c : ℝ) (q : Fin n → ℝ) :
    J (c • q) = c • J q := by
  have hfc : firstCoefficient (c • q) = (c : ℂ) * firstCoefficient q := by
    unfold firstCoefficient
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
    calc
      (∑ x, (c : ℂ) * (q x : ℂ) * (starRingEnd ℂ) (frame n x)) / (n : ℂ) =
          ((c : ℂ) * ∑ x, (q x : ℂ) * (starRingEnd ℂ) (frame n x)) /
            (n : ℂ) := by
              congr 1
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = (c : ℂ) *
          ((∑ x, (q x : ℂ) * (starRingEnd ℂ) (frame n x)) / (n : ℂ)) := by
            ring
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

def chosenFirstDerivative {m : ℕ} (hm : 0 < m)
    (w : FiniteBox.SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ) :
    Fin (2 * m) → ℝ :=
  fun j => chosenQFirstPath hm w θ η v h j 0

def chosenSecondDerivative {m : ℕ} (hm : 0 < m)
    (w : FiniteBox.SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ) :
    Fin (2 * m) → ℝ :=
  fun j => chosenQSecond hm w θ η v h j

def baseRadial {m : ℕ} (hm : 0 < m) (w : FiniteBox.SignPattern hm)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (j : Fin (2 * m)) : ℝ :=
  FixedSchurRotatedAlgebra.radial (angleAverage (by omega) θ j)
    (coordinate hm w θ v j)
    (rotatedP (by omega) v (coordinate hm w θ v) j)

def firstRadial {m : ℕ} (hm : 0 < m) (w : FiniteBox.SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (j : Fin (2 * m)) : ℝ :=
  FixedSchurRotatedAlgebra.radial (angleAverage (by omega) θ j)
    (chosenFirstDerivative hm w θ η v h j)
    ((J (chosenFirstDerivative hm w θ η v h) + tangent (by omega) h) j)

def firstTangential {m : ℕ} (hm : 0 < m)
    (w : FiniteBox.SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (j : Fin (2 * m)) : ℝ :=
  FixedSchurRotatedAlgebra.tangential (angleAverage (by omega) θ j)
    (chosenFirstDerivative hm w θ η v h j)
    ((J (chosenFirstDerivative hm w θ η v h) + tangent (by omega) h) j)

def secondSource {m : ℕ} (hm : 0 < m) (w : FiniteBox.SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (j : Fin (2 * m)) : ℝ :=
  FiniteBox.patternSign w j / (2 * epsilon (2 * m)) *
      Real.cos (Real.pi / (2 * m : ℝ) +
        angleDifference (by omega) θ j / 2) *
        angleDifference (by omega) η j ^ 2 -
    2 * firstTangential hm w θ η v h j * angleAverage (by omega) η j +
    baseRadial hm w θ v j * angleAverage (by omega) η j ^ 2 +
    FiniteBox.patternSign w j * epsilon (2 * m) *
        rotatedS (by omega) θ v (coordinate hm w θ v) j /
        H (epsilon (2 * m))
          (rotatedS (by omega) θ v (coordinate hm w θ v) j) *
      (2 * firstRadial hm w θ η v h j * angleAverage (by omega) η j +
        rotatedS (by omega) θ v (coordinate hm w θ v) j *
          angleAverage (by omega) η j ^ 2) -
    4 * FiniteBox.patternSign w j * epsilon (2 * m) /
        H (epsilon (2 * m))
          (rotatedS (by omega) θ v (coordinate hm w θ v) j) ^ 3 *
      (firstTangential hm w θ η v h j -
        baseRadial hm w θ v j * angleAverage (by omega) η j) ^ 2

@[simp] private theorem chosenQPath_zero {m : ℕ} (hm : 0 < m)
    (w : FiniteBox.SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ) :
    chosenQPath hm w θ η v h 0 = coordinate hm w θ v := by
  simp [chosenQPath, chosenParameterPath, CommonFiberCanonicalPaths.affinePath]

@[simp] private theorem chosenPPath_zero {m : ℕ} (hm : 0 < m)
    (w : FiniteBox.SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (j : Fin (2 * m)) :
    chosenPPath hm w θ η v h j 0 =
      FixedSchurNormalExpansion.rotatedP (by omega) v (coordinate hm w θ v) j := by
  simp [chosenPPath, chosenParameterPath, CommonFiberCanonicalPaths.affinePath,
    FixedSchurNormalExpansion.rotatedP]

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
    chosenR hm w θ η v h j = baseRadial hm w θ v j := by
  simp [chosenR, radialPath, FixedSchurRotatedPath.r, baseRadial,
    FixedSchurRotatedAlgebra.radial]

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

theorem eventual_chosenP_derivatives : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (w : FiniteBox.SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      (fun j => chosenPFirstPath (by omega) w θ η v h j 0) =
          J (fun i => chosenQFirstPath (by omega) w θ η v h i 0) +
            tangent (by omega) h ∧
      (fun j => chosenPSecond (by omega) w θ η v h j) =
          J (fun i => chosenQSecond (by omega) w θ η v h i) := by
  filter_upwards [eventual_chosenQPath_contDiffAt,
    eventual_chosen_path_jets] with m hsmooth hjets
  intro hm w θ η v h hx hd
  have hqv := hsmooth (by omega) w θ η v h hx hd
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
    exact (hjets hm w θ η v h hx hd i).1
  have hp : ∀ᶠ z in 𝓝 (0 : ℝ), ∀ j : Fin (2 * m),
      HasDerivAt (chosenPPath (by omega) w θ η v h j)
        (chosenPFirstPath (by omega) w θ η v h j z) z := by
    rw [Filter.eventually_all]
    intro j
    exact (hjets hm w θ η v h hx hd j).2.1
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
    exact (hjets hm w θ η v h hx hd i).2.2.1.differentiableAt
  let q₂ : Fin (2 * m) → ℝ := (fderiv ℝ q₁ 0) 1
  have hq₂ : q₂ = fun i => chosenQSecond (by omega) w θ η v h i := by
    funext i
    have hi := ((ContinuousLinearMap.proj i).hasFDerivAt.comp 0
      hq₁diff.hasFDerivAt).hasDerivAt
    exact hi.unique (hjets hm w θ η v h hx hd i).2.2.1
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
  exact (hjets hm w θ η v h hx hd j).2.2.2.unique hpsecond

theorem eventual_chosen_normalLinearizations : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (w : FiniteBox.SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      normalLinearization (by omega) w θ v
          (chosenFirstDerivative (by omega) w θ η v h) =
        source (by omega) w θ η v h ∧
      normalLinearization (by omega) w θ v
          (chosenSecondDerivative (by omega) w θ η v h) =
        secondSource (by omega) w θ η v h := by
  filter_upwards [eventual_chosen_rotated_identities,
    eventual_chosenP_derivatives] with m hident hpder
  intro hm w θ η v h hx hd
  have hp := hpder hm w θ η v h hx hd
  have hi := hident hm w θ η v h hx hd
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

end
end StructuralNote.FixedSchurChosenLinearization
