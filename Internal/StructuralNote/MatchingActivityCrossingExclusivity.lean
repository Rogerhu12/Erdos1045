import StructuralNote.MatchingActivityCrossingPressure

/-! The two adjacent crossing constraints at one matching site cannot both be
active. The proof uses the actual physical center step, not the corrected polar
center. -/

noncomputable section
open scoped BigOperators Topology

namespace StructuralNote.MatchingActivityCrossingExclusivity

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization Filter
open FiniteFourierLift FourierMultiplier DiscreteEnergy LensClosure
open ExtremalPolarCenter NormalizedPolarRepresentation SinglePressureEstimate
open CommonClosureEnergy MatchingActivityRadialPair MatchingActivityRadialClosure
open MatchingActivityRadialGeometry MatchingActivityRadialActual
open StrongPointwiseCoordinates StrongPointwiseSmallness StrongBudgetConsequences
open SignedPressureRemainder StrongObjectiveEstimate MatchingActivityCrossingPressure

def plusCrossingVector {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (r : Fin m → ℝ) (c : Fin (2 * m) → ℂ) (j : Fin m) : ℂ :=
  (radialLength hm θ r j : ℂ) * unit (radialPhase hm θ r j) +
    difference (by omega) c (halfIndex j)

def minusCrossingVector {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (r : Fin m → ℝ) (c : Fin (2 * m) → ℂ) (j : Fin m) : ℂ :=
  (radialLength hm θ r j : ℂ) * unit (radialPhase hm θ r j) -
    difference (by omega) c (halfIndex j)

/-- If all matching semidiameters are one, the angular opening leaves a
quadratic amount of crossing slack. An actual center step of order `n⁻²`
cannot fill that slack in both signs. -/
theorem crossing_exclusive_of_matching {m : ℕ} (hm : 8 ≤ m)
    (θ : Fin (2 * m) → ℝ) (r : Fin m → ℝ) (c : Fin (2 * m) → ℂ)
    (hr : ∀ j, r j = 1)
    (hθ : ∀ j, |θ j| ≤ 1 / (1000 * (2 * m : ℝ)))
    (hc : ∀ j, ‖difference (by omega) c j‖ ≤
      StrongPointwiseSteps.physicalStepConstant / (2 * m : ℝ) ^ 2)
    (hsmallC : StrongPointwiseSteps.physicalStepConstant / (2 * m : ℝ) ≤ 1 / 1000)
    (j : Fin m) :
    ¬(‖plusCrossingVector (by omega) θ r c j‖ = 2 ∧
      ‖minusCrossingVector (by omega) θ r c j‖ = 2) := by
  let n : ℝ := 2 * m
  let φ : ℝ := halfAngle (by omega) θ j
  let D : ℂ := (radialLength (by omega) θ r j : ℂ) * unit (radialPhase (by omega) θ r j)
  let B : ℂ := difference (by omega) c (halfIndex j)
  have hn : 0 < n := by dsimp [n]; positivity
  have hhalf := small_half_angle hm θ hθ j
  have hsin : 1 / n ≤ Real.sin φ := by
    simpa only [n, φ, Nat.cast_mul, Nat.cast_ofNat] using hhalf.2.2
  have hsin0 : 0 ≤ Real.sin φ := (by positivity : 0 ≤ 1 / n).trans hsin
  have hsin2 : (1 / n) ^ 2 ≤ Real.sin φ ^ 2 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ 1 / n) hsin 2
  have hDsq : ‖D‖ ^ 2 = 4 * Real.cos φ ^ 2 := by
    have hlength : radialLength (by omega) θ r j ^ 2 = 4 * Real.cos φ ^ 2 := by
      rw [radialLength, length_sq, hr j, hr (nextIndex (by omega) j)]
      dsimp only [φ]
      ring
    dsimp only [D]
    rw [norm_mul, norm_real, Real.norm_eq_abs, norm_unit, mul_one, sq_abs]
    exact hlength
  have hB : ‖B‖ ≤ 1 / (1000 * n) := by
    calc
      ‖B‖ ≤ StrongPointwiseSteps.physicalStepConstant / (2 * m : ℝ) ^ 2 := hc (halfIndex j)
      _ = (StrongPointwiseSteps.physicalStepConstant / (2 * m : ℝ)) / n := by
        dsimp only [n]
        ring
      _ ≤ (1 / 1000) / n := div_le_div_of_nonneg_right hsmallC hn.le
      _ = 1 / (1000 * n) := by ring
  have hB2 : ‖B‖ ^ 2 ≤ (1 / (1000 * n)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg B) hB 2
  have hB2' : ‖B‖ ^ 2 ≤ (1 / 1000000) * (1 / n) ^ 2 := by
    calc
      _ ≤ (1 / (1000 * n)) ^ 2 := hB2
      _ = (1 / 1000000) * (1 / n) ^ 2 := by ring
  have hsmall : ‖D‖ ^ 2 + ‖B‖ ^ 2 < 4 := by
    have htrig := Real.cos_sq_add_sin_sq φ
    have hn2 : 0 < (1 / n) ^ 2 := by positivity
    rw [hDsq]
    nlinarith only [htrig, hsin2, hB2', hn2]
  intro hactive
  have hplus : Complex.normSq (D + B) = 4 := by
    rw [Complex.normSq_eq_norm_sq]
    change ‖plusCrossingVector (by omega) θ r c j‖ ^ 2 = 4
    rw [hactive.1]
    norm_num
  have hminus : Complex.normSq (D - B) = 4 := by
    rw [Complex.normSq_eq_norm_sq]
    change ‖minusCrossingVector (by omega) θ r c j‖ ^ 2 = 4
    rw [hactive.2]
    norm_num
  rw [Complex.normSq_add] at hplus
  rw [Complex.normSq_sub] at hminus
  have hsum : ‖D‖ ^ 2 + ‖B‖ ^ 2 = 4 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    linarith only [hplus, hminus]
  linarith

/-- For every sufficiently large actual even-order maximizer, at most one of
the two adjacent crossing constraints at each matching site is active. The
same witnesses retain matching saturation and nonzero pressure at every site. -/
theorem eventual_diameter_crossing_exclusive :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z : Points (2 * m),
      ExtremalNormalization.DiameterExtremal z →
      ∃ (hm : 0 < m) (σ : Equiv.Perm (Fin (2 * m))) (α β : ℂ)
        (u : ℕ → ℂ) (η : ℝ),
        NormalizedRelativeEdgeModel z σ α β u η ∧
        (∀ i : Fin m, modelRadii m β u i = 1) ∧
        (∀ k : Fin (2 * m),
          operator (2 * m) (polarConstraint hm β u) k ≠ 0) ∧
        ∀ j : Fin m,
          ¬(‖plusCrossingVector hm (normalizedAngle m u) (modelRadii m β u)
                (actualCenter m β u) j‖ = 2 ∧
            ‖minusCrossingVector hm (normalizedAngle m u) (modelRadii m β u)
                (actualCenter m β u) j‖ = 2) := by
  obtain ⟨m₀, h₀⟩ := eventual_diameter_matching_pressure_margin 0
  obtain ⟨m₁, h₁⟩ := eventually_atTop.1 eventual_coefficients_small
  refine ⟨max (max m₀ m₁) 8, ?_⟩
  intro m hm z hz
  obtain ⟨hmp, σ, α, β, u, η, hmodel, _, _, _, hcombined, hbounds, hsat, hmargin⟩ :=
    h₀ m (by omega) z hz
  have hG0 : 0 ≤ SolScalarGap.G hmp (polarConstraint hmp β u) :=
    SolScalarGap.gap_nonneg hmp _
  have hbudget : radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
      realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / (2 * m : ℝ) ^ 2 := by
    linarith only [hcombined, hG0]
  have hs := h₁ (2 * m) (by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hs
  have hθ := (model_nonlocal_smallness (show 8 ≤ m by omega) hmodel hz.1 hbounds hbudget
    hs.2.1 hs.2.2.1 hs.2.2.2.1).1
  refine ⟨hmp, σ, α, β, u, η, hmodel, hsat, (fun k => (hmargin k).2), ?_⟩
  intro j
  exact crossing_exclusive_of_matching (show 8 ≤ m by omega) (normalizedAngle m u)
    (modelRadii m β u) (actualCenter m β u) hsat hθ hbounds.2.2.2.2.2.2
    hs.2.2.1 j

end StructuralNote.MatchingActivityCrossingExclusivity
