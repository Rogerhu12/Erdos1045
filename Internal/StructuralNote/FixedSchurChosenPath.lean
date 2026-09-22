import StructuralNote.FixedSchurChartRegularity
import StructuralNote.FixedSchurChartRotated
import StructuralNote.FixedSchurRotatedSecondPath
import StructuralNote.CommonFiberCanonicalDirections
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Genuine first and second path identities on the chosen fixed-Schur chart. -/

namespace StructuralNote.FixedSchurChosenPath

open Complex Filter
open Erdos1045 Erdos1045.EventualExact
open FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open CommonClosureEnergy CommonDomainClosure CommonTangentialParameters
open CommonFiberSmooth CommonFiberCanonical CommonFiberCanonicalPaths
open CommonFiberCanonicalDirections
open EdgeCoordinates FixedSchurData FixedSchurEquationSmooth FixedSchurLinear
open FixedSchurChart FixedSchurChartSmooth FixedSchurChartRotated
open FixedSchurRotatedPath FixedSchurRotatedSecondPath
open scoped BigOperators Topology ContDiff

noncomputable section

def chosenParameterPath {m : ℕ}
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ) (z : ℝ) :
    SchurParameters m :=
  affinePath (θ, v) (η, h) z

def chosenQPath {m : ℕ} (hm : 0 < m) (w : FiniteBox.SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ) (z : ℝ) :
    SchurState m :=
  coordinate hm w (chosenParameterPath θ η v h z).1
    (chosenParameterPath θ η v h z).2

def chosenPPath {m : ℕ} (hm : 0 < m) (w : FiniteBox.SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (j : Fin (2 * m)) (z : ℝ) : ℝ :=
  (J (chosenQPath (by omega) w θ η v h z) +
    tangent (by omega) (chosenParameterPath θ η v h z).2) j

def chosenAPath {m : ℕ} (hm : 0 < m) (θ η : Fin (2 * m) → ℝ)
    (j : Fin (2 * m)) (z : ℝ) : ℝ :=
  Real.pi / (2 * m : ℝ) +
    angleDifference (by omega) (chosenParameterPath θ η (0 : Fin (2 * m) → ℂ)
      (0 : Fin (2 * m) → ℂ) z).1 j / 2

def chosenBPath {m : ℕ} (hm : 0 < m) (θ η : Fin (2 * m) → ℝ)
    (j : Fin (2 * m)) (z : ℝ) : ℝ :=
  angleAverage (by omega) (chosenParameterPath θ η (0 : Fin (2 * m) → ℂ)
    (0 : Fin (2 * m) → ℂ) z).1 j

def angleDifferenceDirection {m : ℕ} (hm : 0 < m)
    (η : Fin (2 * m) → ℝ) (j : Fin (2 * m)) : ℝ :=
  angleDifference (by omega) η j

def angleAverageDirection {m : ℕ} (hm : 0 < m)
    (η : Fin (2 * m) → ℝ) (j : Fin (2 * m)) : ℝ :=
  angleAverage (by omega) η j

def chosenQFirstPath {m : ℕ} (hm : 0 < m) (w : FiniteBox.SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (j : Fin (2 * m)) (z : ℝ) : ℝ :=
  deriv (fun y : ℝ => chosenQPath hm w θ η v h y j) z

def chosenPFirstPath {m : ℕ} (hm : 0 < m) (w : FiniteBox.SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (j : Fin (2 * m)) (z : ℝ) : ℝ :=
  deriv (chosenPPath hm w θ η v h j) z

def chosenQSecond {m : ℕ} (hm : 0 < m) (w : FiniteBox.SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (j : Fin (2 * m)) : ℝ :=
  deriv (chosenQFirstPath hm w θ η v h j) 0

def chosenPSecond {m : ℕ} (hm : 0 < m) (w : FiniteBox.SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (j : Fin (2 * m)) : ℝ :=
  deriv (chosenPFirstPath hm w θ η v h j) 0

def chosenR {m : ℕ} (hm : 0 < m) (w : FiniteBox.SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (j : Fin (2 * m)) : ℝ :=
  radialPath (fun z : ℝ => chosenQPath hm w θ η v h z j)
    (chosenPPath hm w θ η v h j) (chosenBPath hm θ η j) 0

def chosenS {m : ℕ} (hm : 0 < m) (w : FiniteBox.SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (j : Fin (2 * m)) : ℝ :=
  tangentialPath (fun z : ℝ => chosenQPath hm w θ η v h z j)
    (chosenPPath hm w θ η v h j) (chosenBPath hm θ η j) 0

def chosenU {m : ℕ} (hm : 0 < m) (w : FiniteBox.SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (j : Fin (2 * m)) : ℝ :=
  UPath (chosenQFirstPath hm w θ η v h j)
    (chosenPFirstPath hm w θ η v h j) (chosenBPath hm θ η j) 0

def chosenT {m : ℕ} (hm : 0 < m) (w : FiniteBox.SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (j : Fin (2 * m)) : ℝ :=
  TPath (chosenQFirstPath hm w θ η v h j)
    (chosenPFirstPath hm w θ η v h j) (chosenBPath hm θ η j) 0

theorem hasDerivAt_chosenAPath {m : ℕ} (hm : 0 < m)
    (θ η : Fin (2 * m) → ℝ) (j : Fin (2 * m)) (z : ℝ) :
    HasDerivAt (chosenAPath hm θ η j)
      (angleDifferenceDirection hm η j / 2) z := by
  have heq : chosenAPath hm θ η j = fun y : ℝ =>
      chosenAPath hm θ η j 0 + y * (angleDifferenceDirection hm η j / 2) := by
    funext y
    dsimp [chosenAPath, angleDifferenceDirection, chosenParameterPath, affinePath,
      angleDifference]
    ring
  rw [heq]
  have h := (hasDerivAt_const z (chosenAPath hm θ η j 0)).add
    ((hasDerivAt_id z).mul_const (angleDifferenceDirection hm η j / 2))
  have h' := h.congr_of_eventuallyEq
    (f₁ := fun y : ℝ => chosenAPath hm θ η j 0 +
      y * (angleDifferenceDirection hm η j / 2)) (by
    filter_upwards [] with y
    simp)
  exact h'.congr_deriv (by ring)

theorem hasDerivAt_chosenBPath {m : ℕ} (hm : 0 < m)
    (θ η : Fin (2 * m) → ℝ) (j : Fin (2 * m)) (z : ℝ) :
    HasDerivAt (chosenBPath hm θ η j) (angleAverageDirection hm η j) z := by
  have heq : chosenBPath hm θ η j = fun y : ℝ =>
      chosenBPath hm θ η j 0 + y * angleAverageDirection hm η j := by
    funext y
    dsimp [chosenBPath, angleAverageDirection, chosenParameterPath, affinePath,
      angleAverage]
    ring
  rw [heq]
  have h := (hasDerivAt_const z (chosenBPath hm θ η j 0)).add
    ((hasDerivAt_id z).mul_const (angleAverageDirection hm η j))
  have h' := h.congr_of_eventuallyEq
    (f₁ := fun y : ℝ => chosenBPath hm θ η j 0 +
      y * angleAverageDirection hm η j) (by
    filter_upwards [] with y
    simp)
  exact h'.congr_deriv (by ring)

theorem eventual_chosenQPath_contDiffAt : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (w : FiniteBox.SignPattern hm)
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain hm θ v → Admissible hm (η, h) →
      ContDiffAt ℝ ∞ (chosenQPath hm w θ η v h) 0 := by
  filter_upwards [eventual_local_model] with m hmodel
  intro hm w θ η v h hx hd
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
  obtain ⟨g, hgx, hg, he⟩ := hmodel hm w x hx'
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

theorem chosenPPath_contDiffAt {m : ℕ} (hm : 0 < m)
    (w : FiniteBox.SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (j : Fin (2 * m))
    (hq : ContDiffAt ℝ ∞ (chosenQPath hm w θ η v h) 0) :
    ContDiffAt ℝ ∞ (chosenPPath hm w θ η v h j) 0 := by
  have hJ : ContDiffAt ℝ ∞
      (fun z : ℝ => J (chosenQPath hm w θ η v h z) j) 0 := by
    change ContDiffAt ℝ ∞ (fun z : ℝ =>
      (2 : ℝ) • (firstCoefficient (chosenQPath hm w θ η v h z) *
        frame (2 * m) j).im) 0
    have hf0 : ContDiff ℝ ω (fun q : SchurState m => firstCoefficient q) := by
      unfold firstCoefficient frame
      have hcast : ContDiff ℝ ω (Complex.ofReal : ℝ → ℂ) :=
        Complex.ofRealCLM.contDiff
      fun_prop
    have hf : ContDiffAt ℝ ∞
        (fun z : ℝ => firstCoefficient (chosenQPath hm w θ η v h z)) 0 := by
      have hf0' : ContDiff ℝ ∞ (fun q : SchurState m => firstCoefficient q) :=
        hf0.of_le (show (∞ : ℕ∞ω) ≤ ω from le_top)
      exact hf0'.contDiffAt.comp 0 hq
    have hp : ContDiffAt ℝ ∞ (fun z : ℝ =>
        firstCoefficient (chosenQPath hm w θ η v h z) * frame (2 * m) j) 0 :=
      hf.mul contDiffAt_const
    have hi := Complex.imCLM.contDiff.contDiffAt.comp 0 hp
    simpa only [Function.comp_def, Complex.imCLM_apply] using hi.const_smul (2 : ℝ)
  have ht : ContDiffAt ℝ ∞
      (fun z : ℝ => tangent (by omega)
        (chosenParameterPath θ η v h z).2 j) 0 := by
    unfold tangent
    have he : ContDiffAt ℝ ∞ (fun z : ℝ =>
        edgeRatio (by omega) (chosenParameterPath θ η v h z).2 j) 0 := by
      unfold edgeRatio LocalDFT.pairRatio periodize chosenParameterPath affinePath
      fun_prop
    have hr := Complex.reCLM.contDiff.contDiffAt.comp 0 he
    change ContDiffAt ℝ ∞ (fun z : ℝ =>
      ((2 * m : ℕ) : ℝ) •
        (edgeRatio (by omega) (chosenParameterPath θ η v h z).2 j).re) 0
    simpa only [Function.comp_def, Complex.reCLM_apply, Nat.cast_mul,
      Nat.cast_ofNat] using hr.const_smul (2 * m : ℝ)
  change ContDiffAt ℝ ∞ (fun z : ℝ =>
    J (chosenQPath hm w θ η v h z) j +
      tangent (by omega) (chosenParameterPath θ η v h z).2 j) 0
  exact hJ.add ht

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

theorem eventual_chosen_path_jets : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (w : FiniteBox.SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
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
  filter_upwards [eventual_chosenQPath_contDiffAt] with m hsmooth
  intro hm w θ η v h hx hd j
  have hqv := hsmooth (by omega) w θ η v h hx hd
  have hq : ContDiffAt ℝ ∞
      (fun z : ℝ => chosenQPath (by omega) w θ η v h z j) 0 := by
    exact (contDiffAt_apply ℝ ℝ j _).comp 0 hqv
  have hp := chosenPPath_contDiffAt (by omega) w θ η v h j hqv
  have hqjet := contDiffAt_second_derivatives hq
  have hpjet := contDiffAt_second_derivatives hp
  simpa only [chosenQFirstPath, chosenPFirstPath, chosenQSecond,
    chosenPSecond] using ⟨hqjet.1, hpjet.1, hqjet.2, hpjet.2⟩

private theorem branch_constraint_and_height {ε σ a b q p : ℝ}
    (hε : 0 < ε) (hσ : σ = 1 ∨ σ = -1)
    (hroot : r q p b = σ / ε * (H ε (s q p b) - L a))
    (hpos : 0 < L a + σ * ε * r q p b) :
    0 < H ε (s q p b) ∧
      r q p b + σ / ε * (L a - H ε (s q p b)) = 0 := by
  have hσsq : σ ^ 2 = 1 := by
    rcases hσ with rfl | rfl <;> norm_num
  have heq : L a + σ * ε * r q p b = H ε (s q p b) := by
    rw [hroot]
    field_simp [hε.ne']
    rw [hσsq]
    ring
  constructor
  · rwa [← heq]
  · rw [hroot]
    field_simp [hε.ne']
    ring

theorem eventual_chosen_path_constraint : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (w : FiniteBox.SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      ∀ j : Fin (2 * m),
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
  filter_upwards [eventual_coordinate_rotated] with m hrot
  intro hm w θ η v h hx hd j
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
        r (chosenQPath (by omega) w θ η v h z j)
            (chosenPPath (by omega) w θ η v h j z)
            (chosenBPath (by omega) θ η j z) =
          FiniteBox.patternSign w j / epsilon (2 * m) *
            (H (epsilon (2 * m))
              (s (chosenQPath (by omega) w θ η v h z j)
                (chosenPPath (by omega) w θ η v h j z)
                (chosenBPath (by omega) θ η j z)) -
              L (chosenAPath (by omega) θ η j z)) := by
      simpa [r, s, FixedSchurRotatedAlgebra.radial,
        FixedSchurRotatedAlgebra.tangential, L, H, chosenAPath, chosenBPath,
        chosenParameterPath, affinePath, chordLength] using hz.2
    have hpos : 0 < L (chosenAPath (by omega) θ η j z) +
        FiniteBox.patternSign w j * epsilon (2 * m) *
          r (chosenQPath (by omega) w θ η v h z j)
            (chosenPPath (by omega) w θ η v h j z)
            (chosenBPath (by omega) θ η j z) := by
      simpa [r, FixedSchurRotatedAlgebra.radial, L, chosenAPath, chosenBPath,
        chosenParameterPath,
        affinePath, chordLength] using hz.1
    exact (branch_constraint_and_height (epsilon_pos (by omega))
      (FiniteBox.patternSign_is_sign w j) hroot hpos).1
  · have hroot :
        r (chosenQPath (by omega) w θ η v h z j)
            (chosenPPath (by omega) w θ η v h j z)
            (chosenBPath (by omega) θ η j z) =
          FiniteBox.patternSign w j / epsilon (2 * m) *
            (H (epsilon (2 * m))
              (s (chosenQPath (by omega) w θ η v h z j)
                (chosenPPath (by omega) w θ η v h j z)
                (chosenBPath (by omega) θ η j z)) -
              L (chosenAPath (by omega) θ η j z)) := by
      simpa [r, s, FixedSchurRotatedAlgebra.radial,
        FixedSchurRotatedAlgebra.tangential, L, H, chosenAPath, chosenBPath,
        chosenParameterPath, affinePath, chordLength] using hz.2
    have hpos : 0 < L (chosenAPath (by omega) θ η j z) +
        FiniteBox.patternSign w j * epsilon (2 * m) *
          r (chosenQPath (by omega) w θ η v h z j)
            (chosenPPath (by omega) w θ η v h j z)
            (chosenBPath (by omega) θ η j z) := by
      simpa [r, FixedSchurRotatedAlgebra.radial, L, chosenAPath, chosenBPath,
        chosenParameterPath,
        affinePath, chordLength] using hz.1
    simpa only [constraintPath, radialPath, tangentialPath] using
      (branch_constraint_and_height (epsilon_pos (by omega))
        (FiniteBox.patternSign_is_sign w j) hroot hpos).2

theorem eventual_chosen_rotated_identities : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (w : FiniteBox.SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      ∀ j : Fin (2 * m),
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
  filter_upwards [eventual_chosen_path_jets,
    eventual_chosen_path_constraint] with m hjets hconstraint
  intro hm w θ η v h hx hd j
  have hj := hjets hm w θ η v h hx hd j
  have hc := hconstraint hm w θ η v h hx hd j
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

end
end StructuralNote.FixedSchurChosenPath
