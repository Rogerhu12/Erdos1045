import StructuralNote.FixedDualClassificationPhaseArc
import StructuralNote.FixedDualClassificationZeroArcs
import StructuralNote.FixedDualClassificationTrialNearMaximum
import StructuralNote.SolNearMaximumSigns

/-! Actual finite near maxima have the third-harmonic signs outside six fixed
radius arcs. The phase is extracted from the actual normalized step profile;
neither an energy threshold nor a potential comparison is assumed here. -/

namespace StructuralNote.FixedDualClassificationSixArcSigns

open Real Set Filter
open Erdos1045.EventualExact FourierMultiplier FiniteBox
open FixedDualClassificationStep FixedDualClassificationPeriodicStep
open FixedDualClassificationCircleShift FixedDualClassificationPhaseArc
open FixedDualClassificationParseval FixedDualClassificationMultiplierLimit
open FixedDualClassificationStepPotential FixedDualClassificationGridComparison
open FixedDualClassificationFunctional FixedDualClassificationLobeGeometry
open FixedDualClassificationTrialNearMaximum FixedDualClassificationFinite
open FixedDualClassificationZeroArcs SolNearMaximumSigns
open scoped Topology
noncomputable section

theorem thirdCoefficient_circleProfile {m : ℕ} (hm : 0 < m)
    (q : Fin (2 * m) → ℝ) :
    thirdCoefficient (circleProfile q (profileScale (2 * m))) =
      profileCoefficient (stepProfile q (profileScale (2 * m))) 3 := by
  unfold thirdCoefficient
  rw [circleProfile_fourierCoeff (by omega), profileCoefficient_eq (by omega)]

theorem normalized_potential_sign {m : ℕ} (hm : 0 < m)
    (q : Fin (2 * m) → ℝ) (hq : q ∈ Q hm)
    (hr : (24 : ℝ) / 25 ≤
      ‖profileCoefficient (stepProfile q (profileScale (2 * m))) 3‖) (θ : ℝ)
    (haway : sin (3 / 8 : ℝ) ≤
      |cos (thirdPhase (circleProfile q (profileScale (2 * m))) θ)|) :
    (0 ≤ cos (thirdPhase (circleProfile q (profileScale (2 * m))) θ) →
      (1 : ℝ) / 50 < continuousPotential q (profileScale (2 * m)) θ) ∧
    (cos (thirdPhase (circleProfile q (profileScale (2 * m))) θ) ≤ 0 →
      continuousPotential q (profileScale (2 * m)) θ < -(1 / 50 : ℝ)) := by
  have hb := normalized_profile_bound hm q hq
  have hf := circleProfile_measurable q (profileScale (2 * m))
  have hanti := circleProfile_antiperiodic hm q hq.1 (profileScale (2 * m))
  have hmom := reflected_third_moments hf hb hanti θ
  have hr' : (24 : ℝ) / 25 ≤ ‖thirdCoefficient (circleProfile q (profileScale (2 * m)))‖ := by
    rwa [thirdCoefficient_circleProfile hm]
  have hb' : ∀ u ∈ Icc 0 Real.pi,
      |reflected (circleProfile q (profileScale (2 * m))) θ u| ≤ Real.pi / 2 :=
    fun u _ => reflected_bound hb θ u
  exact ⟨fun hpos => positive_potential_of_phase (reflected_measurable hf θ) hb'
    hr' hmom.1 hmom.2 haway hpos,
    fun hneg => negative_potential_of_phase (reflected_measurable hf θ) hb'
      hr' hmom.1 hmom.2 haway hneg⟩

theorem eventually_near_maximum_signs_by_phase (C₀ : ℝ) :
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 0 < m) (s : SignPattern hm),
      deficit hm s ≤ C₀ / (2 * m : ℝ) ^ 2 → ∀ j : Fin (2 * m),
      let φ := thirdPhase
        (circleProfile (vertex (amplitude (2 * m)) s) (profileScale (2 * m)))
        (cellMidpoint (2 * m) j)
      sin (3 / 8 : ℝ) ≤ |cos φ| →
      (1 : ℝ) / 100 < |potential s j| ∧
      patternSign s j = if 0 ≤ cos φ then 1 else -1 := by
  filter_upwards [eventual_near_maximum_entry C₀, near_maximum_signs_eventually C₀]
    with m hentry halign hm s hdef j
  dsimp only
  intro haway
  let q := vertex (amplitude (2 * m)) s
  have hq : q ∈ Q hm := vertex_mem_box (amplitude_pos (by omega)).le s
  have hd : B hm - normalizedBoxEnergy (operator (2 * m)) q ≤ C₀ / (2 * m : ℝ) ^ 2 := hdef
  have he := hentry hm q hq hd
  have hsign := (halign hm s hdef j).2
  have hg := normalized_potential_sign hm q hq he.2.1.le (cellMidpoint (2 * m) j) haway
  have herr := abs_le.mp (he.2.2 j)
  change -(1 / 100 : ℝ) ≤ potential s j -
    continuousPotential q (profileScale (2 * m)) (cellMidpoint (2 * m) j) ∧
    potential s j - continuousPotential q (profileScale (2 * m))
      (cellMidpoint (2 * m) j) ≤ 1 / 100 at herr
  by_cases hpos : 0 ≤ cos (thirdPhase (circleProfile q (profileScale (2 * m)))
      (cellMidpoint (2 * m) j))
  · have hp := hg.1 hpos
    have hp' : (1 : ℝ) / 100 < potential s j := by linarith [herr.1]
    have hp0 : 0 < potential s j := by linarith
    rw [abs_of_pos hp0] at hsign ⊢
    refine ⟨hp', ?_⟩
    rw [if_pos hpos]
    rcases patternSign_is_sign s j with hs | hs
    · exact hs
    · rw [hs] at hsign
      nlinarith
  · have hp := hg.2 (le_of_not_ge hpos)
    have hp' : potential s j < -(1 / 100 : ℝ) := by linarith [herr.2]
    have hp0 : potential s j < 0 := by linarith
    rw [abs_of_neg hp0] at hsign ⊢
    refine ⟨by linarith, ?_⟩
    rw [if_neg hpos]
    rcases patternSign_is_sign s j with hs | hs
    · rw [hs] at hsign
      nlinarith
    · exact hs

/-- The phase is a real parameter of the comparison harmonic, not a rotation
of the finite grid. Modulo 2*pi the integer centers represent exactly six arcs. -/
theorem eventually_near_maximum_six_arc_signs (C₀ : ℝ) :
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 0 < m) (s : SignPattern hm),
      deficit hm s ≤ C₀ / (2 * m : ℝ) ^ 2 →
      ∃ α ∈ Icc (-(Real.pi / 3)) (Real.pi / 3), ∀ j : Fin (2 * m),
        (∀ k : ℤ, (1 : ℝ) / 8 ≤ |cellMidpoint (2 * m) j - zeroCenter α k|) →
        (1 : ℝ) / 100 < |potential s j| ∧
        patternSign s j = if 0 ≤ cos (3 * (cellMidpoint (2 * m) j - α)) then 1 else -1 := by
  filter_upwards [eventually_near_maximum_signs_by_phase C₀] with m h hm s hdef
  let F := circleProfile (vertex (amplitude (2 * m)) s) (profileScale (2 * m))
  let α := -(thirdCoefficient F).arg / 3
  refine ⟨α, ⟨?_, ?_⟩, ?_⟩
  · dsimp only [α]
    linarith [Complex.arg_le_pi (thirdCoefficient F)]
  · dsimp only [α]
    linarith [Complex.neg_pi_lt_arg (thirdCoefficient F)]
  · intro j haway
    have hp : thirdPhase F (cellMidpoint (2 * m) j) =
        3 * (cellMidpoint (2 * m) j - α) := by unfold thirdPhase α; ring
    have hout := cosine_away_of_outside_arcs haway
    have hsite := h hm s hdef j
    change sin (3 / 8 : ℝ) ≤ |cos (thirdPhase F (cellMidpoint (2 * m) j))| → _ at hsite
    rw [hp] at hsite
    exact hsite hout

end
end StructuralNote.FixedDualClassificationSixArcSigns
