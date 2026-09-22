import StructuralNote.MatchingActivityRadialFeasible

/-! A genuine two-sided local crossing-control path.  The closure correction
is obtained from the implicit function theorem with the lens coordinate
`sigma` included among the parameters. -/

namespace StructuralNote.MatchingActivityCrossingVariationGraph

open Erdos1045 Erdos1045.EventualExact Complex Configuration Filter
open LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open CommonClosureEnergy CommonFiberGeometry CommonTangentialParameters BoxLensLift
open MatchingActivityRadialClosure MatchingActivityRadialGeometry
open MatchingActivityRadialIntegration MatchingActivityRadialConstraints
open CommonFiberSmooth
open scoped BigOperators Topology ContDiff
noncomputable section

def sigmaPath {m : ℕ} (s : Fin m → ℝ) (i : Fin m) (t : ℝ) : Fin m → ℝ :=
  Function.update s i (s i + t)

@[simp] theorem sigmaPath_zero {m : ℕ} (s : Fin m → ℝ) (i : Fin m) :
    sigmaPath s i 0 = s := by
  simp [sigmaPath]

theorem sigmaPath_contDiff {m : ℕ} (s : Fin m → ℝ) (i : Fin m) :
    ContDiff ℝ ∞ (sigmaPath s i) := by
  apply contDiff_pi.mpr
  intro j
  by_cases hj : j = i
  · subst j
    simp only [sigmaPath, Function.update_self]
    fun_prop
  · simp only [sigmaPath, Function.update_of_ne hj]
    exact contDiff_const

def sigmaParameters {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (s ν r : Fin m → ℝ) (i : Fin m) (t : ℝ) : Parameters m :=
  parameters hm θ (sigmaPath s i t) ν r

@[simp] theorem sigmaParameters_zero {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (s ν r : Fin m → ℝ) (i : Fin m) :
    sigmaParameters hm θ s ν r i 0 = parameters hm θ s ν r := by
  simp [sigmaParameters]

theorem sigmaParameters_contDiff {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (s ν r : Fin m → ℝ) (i : Fin m) :
    ContDiff ℝ ∞ (sigmaParameters hm θ s ν r i) := by
  unfold sigmaParameters parameters
  exact contDiff_const.prodMk (contDiff_const.prodMk
    ((sigmaPath_contDiff s i).prodMk contDiff_const))

/-- The actual integrated configuration is jointly smooth in the full lens
coordinate array and in the two-dimensional closure correction. -/
theorem radialConfiguration_sigma_contDiffAt {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (s ν r : Fin m → ℝ) (ξ a : ℂ)
    (ht : ∀ j, |heightParameter ν ξ j| < 2) :
    ContDiffAt ℝ ∞ (fun p : (Fin m → ℝ) × ℂ =>
      radialConfiguration hm θ p.1 ν r p.2 a) (s, ξ) := by
  have hinc (j : Fin m) : ContDiffAt ℝ ∞
      (fun p : (Fin m → ℝ) × ℂ => radialIncrement hm θ p.1 ν r p.2 j) (s, ξ) := by
    have hs : ContDiffAt ℝ ∞ (fun p : (Fin m → ℝ) × ℂ => p.1 j) (s, ξ) := by
      fun_prop
    have ht' : ContDiffAt ℝ ∞
        (fun p : (Fin m → ℝ) × ℂ => heightParameter ν p.2 j) (s, ξ) := by
      unfold heightParameter
      fun_prop
    have hh : ContDiffAt ℝ ∞
        (fun p : (Fin m → ℝ) × ℂ => Lens.height (heightParameter ν p.2 j)) (s, ξ) := by
      unfold Lens.height
      exact (contDiffAt_const.sub (ht'.pow 2)).sqrt (by
        have hx := ht j
        have hsq : heightParameter ν ξ j ^ 2 < 4 := by
          nlinarith [(abs_lt.mp hx).1, (abs_lt.mp hx).2]
        dsimp
        linarith)
    have hcast : ContDiff ℝ ∞ (Complex.ofReal : ℝ → ℂ) := Complex.ofRealCLM.contDiff
    unfold radialIncrement LensClosure.increment unit Lens.width
    fun_prop
  have hc : ContDiffAt ℝ ∞ (fun p : (Fin m → ℝ) × ℂ =>
      radialCenter hm θ p.1 ν r p.2) (s, ξ) := by
    apply (integral_contDiff (2 * m)).contDiffAt.comp (s, ξ)
    apply contDiffAt_pi.mpr
    intro j
    exact hinc ⟨j.val % m, Nat.mod_lt _ hm⟩
  apply contDiffAt_pi.mpr
  intro j
  have hcj := contDiffAt_pi.mp hc j
  unfold radialConfiguration vertices
  fun_prop

/-- The joint closure IFT, restricted to a one-coordinate affine line in
`sigma`.  This removes the fixed-`sigma` limitation of the older wrapper. -/
theorem exists_smooth_sigma_root {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (s ν r : Fin m → ℝ) (i : Fin m)
    (hs : ∀ j, |s j| ≤ 1)
    (hsmall : ∀ j, |radialPhase (by omega) θ r j - midpoint m j| + |ν j| ≤ 1 / 4)
    (hzero : closureFamily (parameters (by omega) θ s ν r) 0 = 0) :
    ∃ ξ : ℝ → ℂ, ξ 0 = 0 ∧ ContDiffAt ℝ ∞ ξ 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℝ),
        closureFamily (parameters (by omega) θ (sigmaPath s i t) ν r) (ξ t) = 0 := by
  let p := parameters (show 0 < m by omega) θ s ν r
  have hp (j : Fin m) : |p.1 j - midpoint m j| + |heightParameter p.2.2.2 0 j| ≤ 1 / 4 := by
    simpa only [p, parameters, heightParameter, map_zero, add_zero] using hsmall j
  obtain ⟨G, hG0, hG, hGe, _⟩ := exists_smooth_closure_root hm p 0 hs hp hzero
  let q := sigmaParameters (show 0 < m by omega) θ s ν r i
  have hq : ContDiff ℝ ∞ q := sigmaParameters_contDiff (show 0 < m by omega) θ s ν r i
  have hq0 : q 0 = p := by simp [q, p]
  refine ⟨fun t => G (q t), ?_, ?_, ?_⟩
  · change G (q 0) = 0
    rw [hq0]
    exact hG0
  · have hG' : ContDiffAt ℝ ∞ G (q 0) := by rwa [hq0]
    exact hG'.comp 0 hq.contDiffAt
  · have hnear : Tendsto q (𝓝 0) (𝓝 p) := by
      rw [← hq0]
      exact hq.continuous.continuousAt
    simpa only [q, sigmaParameters] using hnear.eventually hGe

def crossingPath {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (s ν r : Fin m → ℝ) (a : ℂ) (ξ : ℝ → ℂ) (i : Fin m) (t : ℝ) :
    Points (2 * m) :=
  radialConfiguration hm θ (sigmaPath s i t) ν r (ξ t) a

/-- If one lens coordinate is strictly interior, it admits a genuine
two-sided smooth feasible variation.  All matching edges stay exactly active,
all adjacent and nonlocal distances stay feasible, and the vertex derivative
exists at the base point. -/
theorem exists_feasible_sigma_path {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (s ν r : Fin m → ℝ) (a : ℂ) (i : Fin m)
    (hθ : HalfPeriodic (by omega) (fun j => (θ j : ℂ)))
    (hs : ∀ j, |s j| ≤ 1) (hi : |s i| < 1)
    (hr : ∀ j, r j = 1)
    (hsmall : ∀ j, |radialPhase (by omega) θ r j - midpoint m j| + |ν j| ≤ 1 / 4)
    (hzero : closureFamily (parameters (by omega) θ s ν r) 0 = 0)
    (hw : ∀ j, 0 < Lens.width (radialLength (by omega) θ r j) (ν j))
    (hfar : ∀ (j : Fin (2 * m)) (k : Fin (2 * m)),
      k.val ≠ m - 1 → k.val ≠ m → k.val ≠ m + 1 →
      ‖radialConfiguration (by omega) θ s ν r 0 a (cyclicAdvance j k.val) -
        radialConfiguration (by omega) θ s ν r 0 a j‖ < 2) :
    ∃ ξ : ℝ → ℂ,
      ξ 0 = 0 ∧ ContDiffAt ℝ ∞ ξ 0 ∧
      crossingPath (by omega) θ s ν r a ξ i 0 =
        radialConfiguration (by omega) θ s ν r 0 a ∧
      ContDiffAt ℝ ∞ (crossingPath (by omega) θ s ν r a ξ i) 0 ∧
      (∃ v : Points (2 * m), ∀ j, HasDerivAt
        (fun t => crossingPath (by omega) θ s ν r a ξ i t j) (v j) 0) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ),
        closureFamily (parameters (by omega) θ (sigmaPath s i t) ν r) (ξ t) = 0 ∧
        DiameterAtMost 2 (crossingPath (by omega) θ s ν r a ξ i t) ∧
        ∀ j : Fin (2 * m),
          ‖crossingPath (by omega) θ s ν r a ξ i t (halfTurn (by omega) j) -
            crossingPath (by omega) θ s ν r a ξ i t j‖ = 2) := by
  obtain ⟨ξ, hξ0, hξ, hz⟩ := exists_smooth_sigma_root hm θ s ν r i hs hsmall hzero
  have ht0 (j : Fin m) : |heightParameter ν 0 j| < 2 := by
    simp only [heightParameter, map_zero, add_zero]
    have hh := hsmall j
    linarith [abs_nonneg (radialPhase (by omega) θ r j - midpoint m j)]
  have hp : ContDiffAt ℝ ∞ (fun t : ℝ => (sigmaPath s i t, ξ t)) 0 :=
    (sigmaPath_contDiff s i).contDiffAt.prodMk hξ
  have hjoint := radialConfiguration_sigma_contDiffAt (show 0 < m by omega)
    θ s ν r 0 a ht0
  have hjoint' : ContDiffAt ℝ ∞ (fun p : (Fin m → ℝ) × ℂ =>
      radialConfiguration (by omega) θ p.1 ν r p.2 a)
      (sigmaPath s i 0, ξ 0) := by
    simpa only [sigmaPath_zero, hξ0] using hjoint
  have hc : ContDiffAt ℝ ∞ (crossingPath (by omega) θ s ν r a ξ i) 0 := by
    exact hjoint'.comp 0 hp
  refine ⟨ξ, hξ0, hξ, ?_, hc, ?_, ?_⟩
  · simp [crossingPath, hξ0]
  · refine ⟨fun j => deriv (fun t => crossingPath (by omega) θ s ν r a ξ i t j) 0, ?_⟩
    intro j
    exact ((contDiffAt_pi.mp hc j).differentiableAt (by norm_num)).hasDerivAt
  have hsnear : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ j, |sigmaPath s i t j| ≤ 1 := by
    have hmargin : (0 : ℝ) < 1 - |s i| := by linarith
    have he : ∀ᶠ t in 𝓝 (0 : ℝ), |t| < 1 - |s i| :=
      continuousAt_id.abs.tendsto.eventually (eventually_lt_nhds (by simpa using hmargin))
    filter_upwards [he] with t ht j
    by_cases hj : j = i
    · subst j
      simp only [sigmaPath, Function.update_self]
      exact (abs_add_le _ _).trans (by linarith)
    · simpa only [sigmaPath, Function.update_of_ne hj] using hs j
  have hh (j : Fin m) : ContinuousAt (fun t => heightParameter ν (ξ t) j) 0 := by
    unfold heightParameter
    fun_prop
  have hte : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ j, |heightParameter ν (ξ t) j| < 2 := by
    rw [Filter.eventually_all]
    intro j
    have hb : |heightParameter ν (ξ 0) j| < 2 := by simpa only [hξ0] using ht0 j
    exact (hh j).abs.tendsto.eventually (eventually_lt_nhds hb)
  have hwe : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ j,
      0 < Lens.width (radialLength (by omega) θ r j) (heightParameter ν (ξ t) j) := by
    rw [Filter.eventually_all]
    intro j
    have hcont : ContinuousAt (fun t =>
        Lens.width (radialLength (by omega) θ r j) (heightParameter ν (ξ t) j)) 0 := by
      unfold Lens.width Lens.height
      exact (continuousAt_const.sub ((hh j).pow 2)).sqrt.sub continuousAt_const
    have hb : 0 < Lens.width (radialLength (by omega) θ r j)
        (heightParameter ν (ξ 0) j) := by
      simpa only [hξ0, heightParameter, map_zero, add_zero] using hw j
    exact hcont.tendsto.eventually (eventually_gt_nhds hb)
  have hfe : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ (j : Fin (2 * m)) (k : Fin (2 * m)),
      k.val ≠ m - 1 → k.val ≠ m → k.val ≠ m + 1 →
      ‖crossingPath (by omega) θ s ν r a ξ i t (cyclicAdvance j k.val) -
        crossingPath (by omega) θ s ν r a ξ i t j‖ < 2 := by
    rw [Filter.eventually_all]
    intro j
    rw [Filter.eventually_all]
    intro k
    by_cases he : k.val ≠ m - 1 ∧ k.val ≠ m ∧ k.val ≠ m + 1
    · have h₁ := continuousAt_pi.mp hc.continuousAt (cyclicAdvance j k.val)
      have h₂ := continuousAt_pi.mp hc.continuousAt j
      have hb : ‖crossingPath (by omega) θ s ν r a ξ i 0 (cyclicAdvance j k.val) -
          crossingPath (by omega) θ s ν r a ξ i 0 j‖ < 2 := by
        simpa only [crossingPath, sigmaPath_zero, hξ0] using hfar j k he.1 he.2.1 he.2.2
      exact ((h₁.sub h₂).norm.tendsto.eventually (eventually_lt_nhds hb)).mono
        (fun _ h _ _ _ => h)
    · exact Eventually.of_forall (fun _ h₁ h₂ h₃ => False.elim (he ⟨h₁, h₂, h₃⟩))
  filter_upwards [hz, hsnear, hte, hwe, hfe] with t hz' hs' ht' hw' hfar'
  have ht2 (j : Fin m) : heightParameter ν (ξ t) j ^ 2 ≤ 4 := by
    have hj := ht' j
    nlinarith [(abs_lt.mp hj).1, (abs_lt.mp hj).2]
  have hrabs (j : Fin m) : |r j| ≤ 1 := by rw [hr j]; norm_num
  have hd := diameter_of_nonlocal (show 0 < m by omega) θ (sigmaPath s i t) ν r (ξ t) a
    hθ hz' hs' ht2 hw' hrabs hfar'
  refine ⟨hz', hd, ?_⟩
  intro j
  change ‖radialConfiguration (by omega) θ (sigmaPath s i t) ν r (ξ t) a
      (halfTurn (by omega) j) -
    radialConfiguration (by omega) θ (sigmaPath s i t) ν r (ξ t) a j‖ = 2
  rw [matching_distance (show 0 < m by omega) θ (sigmaPath s i t) ν r (ξ t) a hθ hz']
  unfold radiusFull
  rw [hr]
  norm_num

end
end StructuralNote.MatchingActivityCrossingVariationGraph
