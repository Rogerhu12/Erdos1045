import StructuralNote.PressureCoercivity
import EventualExact.ExtremalPolarCenter
import EventualExact.NormalizedPolarRepresentation

/-! The strict pressure gap for genuine even diameter maximizers. The objective
budget and the error caused by changing center coordinates are conclusions. -/

noncomputable section
open scoped BigOperators Topology

namespace StructuralNote.ActualPressureGap

open Erdos1045 Erdos1045.EventualExact
open Complex Filter Configuration CommonLocalization SchurSpectrum
open ExtremalEnergyBound ExtremalPolarCenter SchurLiftBounds PolarAngleControl
open PressureCoercivity

theorem periodize_restrict {n : ℕ} (hn : 0 < n) (u : ℕ → ℂ)
    (hu : Function.Periodic u n) : periodize hn (fun j : Fin n => u j) = u := by
  funext j
  exact (CyclicAngles.periodic_mod u hu j).symm

theorem model_first_zero {n : ℕ} (hn : 0 < n) {z : Points n}
    {σ : Equiv.Perm (Fin n)} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) :
    centerCoefficient hn (fun j : Fin n => u j) 0 = 0 := by
  unfold centerCoefficient
  rw [periodize_restrict hn u h.periodic]
  exact LocalDFT.coefficient_zero_of_similarity_normalization u h.similarity_zero

theorem evenNormal_restrict {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) :
    evenNormal hm (fun j : Fin (2 * m) => u j) = ExtremalSchurGap.evenConstraint m u := by
  unfold evenNormal
  rw [periodize_restrict (by omega) u hu]
  rfl

theorem model_objectiveDeficit_eq {n : ℕ} (hn : 4 ≤ n) {z : Points n}
    {σ : Equiv.Perm (Fin n)} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hsmall : η ≤ 1 / 4) :
    objectiveDeficit (by omega) (fun j : Fin n => u j) = objective (regular n) - objective (z ∘ σ) := by
  have hs : ∀ j, ‖periodize (by omega) (fun i : Fin n => u i) (j + 1) -
      periodize (by omega) (fun i : Fin n => u i) j‖ ≤ η * ‖LocalPhase.regularRoot n - 1‖ := by
    simpa only [periodize_restrict (by omega) u h.periodic] using h.relative_edges
  rw [objectiveDeficit_eq_neg_gain hn _ h.error_nonneg hsmall hs,
    periodize_restrict (by omega) u h.periodic]
  exact (model_deficit_eq h hn hsmall).symm

theorem polarCenter_eq_normalizedCenter (m : ℕ) (β : ℂ) (u : ℕ → ℂ) :
    polarCenter m β u = NormalizedPolarRepresentation.normalizedCenter m ‖β‖ u := rfl

theorem polarConstraint_eq_normal {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ) :
    polarConstraint hm β u = EdgeCoordinates.normal (by omega)
      (NormalizedPolarRepresentation.normalizedCenter m ‖β‖ u) := by
  funext j
  rw [polarConstraint, constraint_eq_edgeImaginary (show 2 ≤ 2 * m by omega)]
  rfl

/-- In the same actual coordinates, both numerical thresholds required by the
finite pressure estimate eventually hold for every extremizing sequence. -/
theorem diameter_sequence_pressure_gap {M : ℕ → ℕ} (hM2 : ∀ k, 2 ≤ M k)
    (hM : Tendsto M atTop atTop) (z : ∀ k, Points (2 * M k))
    (hz : ∀ k, ExtremalNormalization.DiameterExtremal (z k)) :
    ∃ (σ : ∀ k, Equiv.Perm (Fin (2 * M k))) (α β : ℕ → ℂ)
      (u : ℕ → ℕ → ℂ) (η : ℕ → ℝ),
      Tendsto η atTop (𝓝 0) ∧
      Tendsto (fun k => meanSquare (polarConstraint (by have := hM2 k; omega) (β k) (u k) -
        ExtremalSchurGap.evenConstraint (M k) (u k))) atTop (𝓝 0) ∧
      ∀ᶠ k in atTop,
        NormalizedRelativeEdgeModel (z k) (σ k) (α k) (β k) (u k) (η k) ∧
        CenterBounds (m := M k) (by have := hM2 k; omega) (β k) (u k) ∧
        η k ≤ 1 / 1024 ∧
        objective (regular (2 * M k)) - objective (z k ∘ σ k) ≤ 33 * Real.pi ^ 2 / 256 ∧
        meanSquare (polarConstraint (by have := hM2 k; omega) (β k) (u k) -
          ExtremalSchurGap.evenConstraint (M k) (u k)) ≤ Real.pi ^ 2 / 2048 ∧
        ‖FourierMultiplier.operator (2 * M k)
          (polarConstraint (by have := hM2 k; omega) (β k) (u k))‖ ≤ 31 * Real.pi / 64 := by
  have hN4 (k : ℕ) : 4 ≤ 2 * M k := by have := hM2 k; omega
  have hN : Tendsto (fun k => 2 * M k) atTop atTop :=
    tendsto_atTop_mono (fun _ => by omega) hM
  obtain ⟨σ, α, β, u, η, hη, hmodel⟩ := diameter_sequence_energy hN4 hN z hz
  have hcenter : ∀ᶠ k in atTop, CenterBounds (m := M k) (by have := hM2 k; omega) (β k) (u k) := by
    filter_upwards [hmodel,
      (sizeBudget_tendsto hN).eventually_le_const (by norm_num : (0 : ℝ) < 1 / 16),
      hη.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 4)] with k hk hs he
    have hE := hk.2.2.2.1
    have hp := model_polar_bounds (hM2 k) hk.1 hE (by linarith)
    have hscale := ExtremalScaleBound.model_matching_deficit_bound (hM2 k) hk.1 he (hz k) hE
    apply model_center_bounds (by have := hM2 k; omega) (β k) (u k)
      hk.1.periodic hk.1.mean_zero hE hp hscale.1 _ hs
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hscale.2.1
  have herr : Tendsto (fun k => meanSquare
      (polarConstraint (by have := hM2 k; omega) (β k) (u k) -
        ExtremalSchurGap.evenConstraint (M k) (u k))) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => meanSquare_nonneg _)) _
      (constraintErrorBudget_tendsto hN)
    exact hcenter.mono fun _ hk => hk.constraint_error
  have hbudget : ∀ᶠ k in atTop, diameterBudget (2 * M k) ≤ 33 * Real.pi ^ 2 / 256 :=
    (diameterBudget_tendsto hN).eventually_le_const (by nlinarith [Real.pi_pos])
  refine ⟨σ, α, β, u, η, hη, herr, ?_⟩
  filter_upwards [hmodel, hcenter, hbudget,
    hη.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 1024),
    herr.eventually_le_const (by positivity : (0 : ℝ) < Real.pi ^ 2 / 2048),
    hN.eventually (eventually_ge_atTop 2048)] with k hk hc hb he herrsmall hn
  have hfinite : objectiveDeficit (by have := hN4 k; omega)
      (fun j : Fin (2 * M k) => u k j) =
        objective (regular (2 * M k)) - objective (z k ∘ σ k) :=
    model_objectiveDeficit_eq (hN4 k) hk.1 (by linarith)
  have hJ : objective (regular (2 * M k)) - objective (z k ∘ σ k) ≤ 33 * Real.pi ^ 2 / 256 := by
    rw [model_deficit_eq hk.1 (hN4 k) (by linarith)]
    exact hk.2.2.1.trans hb
  have hs : ∀ i, ‖periodize (by have := hN4 k; omega) (fun j : Fin (2 * M k) => u k j) (i + 1) -
      periodize (by have := hN4 k; omega) (fun j : Fin (2 * M k) => u k j) i‖ ≤
        η k * ‖LocalPhase.regularRoot (2 * M k) - 1‖ := by
    simpa only [periodize_restrict _ _ hk.1.periodic] using hk.1.relative_edges
  refine ⟨hk.1, hc, he, hJ, herrsmall, ?_⟩
  apply operator_pressure_gap_of_perturbation hn (fun j : Fin (2 * M k) => u k j)
    (model_first_zero (by omega) hk.1) hk.1.error_nonneg he hs (hfinite.trans_le hJ)
  simpa only [evenNormal_restrict _ _ hk.1.periodic] using herrsmall

/-- A property of the actual point configuration: all coordinates and all
pressure estimates are existential conclusions. -/
def HasPressureCoordinates (m : ℕ) (z : Points (2 * m)) : Prop :=
  ∃ (hm : 0 < m) (σ : Equiv.Perm (Fin (2 * m))) (α β : ℂ) (u : ℕ → ℂ) (η : ℝ),
    NormalizedRelativeEdgeModel z σ α β u η ∧ CenterBounds hm β u ∧
    η ≤ 1 / 1024 ∧ objective (regular (2 * m)) - objective (z ∘ σ) ≤ 33 * Real.pi ^ 2 / 256 ∧
    meanSquare (polarConstraint hm β u - ExtremalSchurGap.evenConstraint m u) ≤ Real.pi ^ 2 / 2048 ∧
    ‖FourierMultiplier.operator (2 * m) (polarConstraint hm β u)‖ ≤ 31 * Real.pi / 64

/-- Uniformly over all sufficiently large even orders and all global maximizers.
There is no assumed local model, objective budget, or center-error bound. -/
theorem eventual_diameter_pressure_gap :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z : Points (2 * m),
      ExtremalNormalization.DiameterExtremal z → HasPressureCoordinates m z := by
  by_contra h
  push Not at h
  choose M hMk z hz hbad using fun k : ℕ => h (k + 2)
  have hM2 (k : ℕ) : 2 ≤ M k := by have := hMk k; omega
  have hM : Tendsto M atTop atTop :=
    tendsto_atTop_mono (fun k => by have := hMk k; omega : ∀ k, k ≤ M k) tendsto_id
  obtain ⟨σ, α, β, u, η, _, _, hg⟩ := diameter_sequence_pressure_gap hM2 hM z hz
  obtain ⟨k, hk⟩ := hg.exists
  exact hbad k ⟨by have := hM2 k; omega, σ k, α k, β k, u k, η k, hk⟩

end StructuralNote.ActualPressureGap
