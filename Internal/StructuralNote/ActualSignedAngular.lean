import StructuralNote.SignedPressureTangential

/-! The angular pressure error in the actual normalized coordinates of diameter maximizers. -/

noncomputable section
open scoped BigOperators Topology

namespace StructuralNote.ActualSignedAngular

open Erdos1045 Erdos1045.EventualExact Complex
open SchurSpectrum FiniteFourierLift DiscreteEnergy SchurLiftBounds FourierMultiplier
open Configuration CommonLocalization ExtremalPolarCenter NormalizedPolarRepresentation
open PressureCoercivity ActualPressureGap SignedPressureRemainder SignedPressureTangential

def actualAngularSum {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ) : ℝ :=
  (Real.pi / (2 * m)) / (2 * Real.sin (Real.pi / (2 * m))) *
      (∑ j, |operator (2 * m) (polarConstraint hm β u) j| *
        (normalizedAngle m u (successor (by omega) j) - normalizedAngle m u j)) +
    (1 / (4 * Real.sin (Real.pi / (2 * m)))) *
      (∑ j, operator (2 * m) (polarConstraint hm β u) j *
        tangentialSum (2 * m) (polarCenter m β u) j *
        (normalizedAngle m u (successor (by omega) j) - normalizedAngle m u j))

theorem actual_tangentialSum {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ)
    (j : Fin (2 * m)) :
    tangentialSum (2 * m) (polarCenter m β u) j =
      (rotatedCenter m β u j (successor (by omega) j) + rotatedCenter m β u j j).im := by
  unfold tangentialSum rotatedCenter
  rw [finRotate_eq_successor (by omega), mul_add]

/-- The constraint mass bound follows from the actual objective budget and the
proved change of center estimate. -/
theorem model_constraint_mass {m : ℕ} (hm : 2 ≤ m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hη : η ≤ 1 / 1024)
    (hJ : objective (regular (2 * m)) - objective (z ∘ σ) ≤ 33 * Real.pi ^ 2 / 256)
    (herr : meanSquare (polarConstraint (m := m) (by omega) β u - ExtremalSchurGap.evenConstraint m u) ≤
      Real.pi ^ 2 / 2048) :
    meanSquare (polarConstraint (m := m) (by omega) β u) ≤ 65 * Real.pi ^ 2 := by
  have hE := model_energy_le (show 4 ≤ 2 * m by omega) h hη hJ
  have hA := LocalMaximum.energyA_nonneg (2 * m) u
  have hqe := ExtremalSchurGap.evenConstraint_budget (show 0 < m by omega) u h.periodic
  apply constraint_size_of_difference _ (ExtremalSchurGap.evenConstraint m u)
  · unfold ExtremalEnergyBound.totalEnergy at hE
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hE
    nlinarith only [hE, hA, hqe]
  · nlinarith [sq_nonneg Real.pi]

/-- A closed energy bound for the genuine two angular sums, retaining the center
energy and size needed for the later absorption against the free-center defect. -/
theorem angularBudget_le {n : ℕ} (hn : 2 ≤ n) (q θ : Fin n → ℝ) (c : Fin n → ℂ)
    (hG : ‖operator n q‖ ≤ 31 * Real.pi / 64)
    (hM : meanSquare q ≤ 65 * Real.pi ^ 2) :
    angularBudget (by omega) q θ c ≤
      (24 * Real.pi ^ 3 + 33 * Real.pi ^ 2 *
        Real.sqrt (pairEnergy (by omega) c + (n : ℝ) ^ 2 * ‖c‖ ^ 2)) /
          n * Real.sqrt (realEnergy (by omega) θ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hA := pairEnergy_nonneg (show 0 < n by omega) c
  have hGn : ‖operator n q‖ ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hGsq := pow_le_pow_left₀ (norm_nonneg _) hGn 2
  have hroot₁ : Real.sqrt (2 * (n : ℝ) ^ 2 * meanSquare q) ≤ 12 * Real.pi * n := by
    apply (Real.sqrt_le_left (by positivity)).2
    have hh := mul_le_mul_of_nonneg_left hM (show 0 ≤ 2 * (n : ℝ) ^ 2 by positivity)
    nlinarith only [hh, mul_nonneg (sq_nonneg Real.pi) (sq_nonneg (n : ℝ))]
  have hroot₂ : Real.sqrt (48 * ‖operator n q‖ ^ 2 * pairEnergy (by omega) c +
      16 * (n : ℝ) ^ 2 * ‖c‖ ^ 2 * meanSquare q) ≤
      33 * Real.pi * Real.sqrt (pairEnergy (by omega) c + (n : ℝ) ^ 2 * ‖c‖ ^ 2) := by
    apply (Real.sqrt_le_left (by positivity)).2
    have hh₁ := mul_le_mul_of_nonneg_right hGsq hA
    have hh₂ := mul_le_mul_of_nonneg_left hM (show 0 ≤ (n : ℝ) ^ 2 * ‖c‖ ^ 2 by positivity)
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    nlinarith only [hh₁, hh₂, mul_nonneg (sq_nonneg Real.pi) hA,
      mul_nonneg (sq_nonneg Real.pi) (show 0 ≤ (n : ℝ) ^ 2 * ‖c‖ ^ 2 by positivity)]
  have h₁ := mul_le_mul_of_nonneg_left hroot₁
    (show 0 ≤ 2 * Real.pi ^ 2 / (n : ℝ) ^ 2 by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hroot₂ (show 0 ≤ Real.pi / n by positivity)
  have he : 2 * Real.pi ^ 2 / (n : ℝ) ^ 2 * (12 * Real.pi * n) + Real.pi / n *
      (33 * Real.pi * Real.sqrt (pairEnergy (by omega) c + (n : ℝ) ^ 2 * ‖c‖ ^ 2)) =
      (24 * Real.pi ^ 3 + 33 * Real.pi ^ 2 *
        Real.sqrt (pairEnergy (by omega) c + (n : ℝ) ^ 2 * ‖c‖ ^ 2)) / n := by
    field_simp
    ring
  unfold angularBudget
  exact mul_le_mul_of_nonneg_right ((add_le_add h₁ h₂).trans_eq he) (Real.sqrt_nonneg _)

def actualAngularBudget {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ) : ℝ :=
  (24 * Real.pi ^ 3 + 33 * Real.pi ^ 2 *
    Real.sqrt (pairEnergy (by omega) (polarCenter m β u) +
      (2 * m : ℝ) ^ 2 * ‖polarCenter m β u‖ ^ 2)) /
        (2 * m) * Real.sqrt (realEnergy (by omega) (normalizedAngle m u))

theorem model_angular_sum_le {m : ℕ} (hm : 2 ≤ m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hη : η ≤ 1 / 1024)
    (hJ : objective (regular (2 * m)) - objective (z ∘ σ) ≤ 33 * Real.pi ^ 2 / 256)
    (hc : CenterBounds (m := m) (by omega) β u)
    (herr : meanSquare (polarConstraint (m := m) (by omega) β u - ExtremalSchurGap.evenConstraint m u) ≤
      Real.pi ^ 2 / 2048)
    (hG : ‖operator (2 * m) (polarConstraint (m := m) (by omega) β u)‖ ≤ 31 * Real.pi / 64) :
    actualAngularSum (m := m) (by omega) β u ≤ actualAngularBudget (m := m) (by omega) β u := by
  have h₁ := signed_angular_terms_le (show 2 ≤ 2 * m by omega) (even_two_mul m)
    (polarConstraint (m := m) (by omega) β u) (normalizedAngle m u) (polarCenter m β u) hc.mean_zero
  have h₂ := angularBudget_le (show 2 ≤ 2 * m by omega)
    (polarConstraint (m := m) (by omega) β u) (normalizedAngle m u) (polarCenter m β u) hG
    (model_constraint_mass hm h hη hJ herr)
  simpa only [actualAngularSum, actualAngularBudget, Nat.cast_mul, Nat.cast_ofNat] using h₁.trans h₂

open Filter PolarAngleControl

/-- The angular and remainder estimates hold simultaneously for every actual
global maximizer of every sufficiently large even order. -/
theorem eventual_diameter_angular_and_remainder :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z : Points (2 * m),
      ExtremalNormalization.DiameterExtremal z →
      ∃ (hm : 0 < m) (σ : Equiv.Perm (Fin (2 * m))) (α β : ℂ) (u : ℕ → ℂ) (η : ℝ),
        NormalizedRelativeEdgeModel z σ α β u η ∧ CenterBounds hm β u ∧
        η ≤ 1 / 1024 ∧ objective (regular (2 * m)) - objective (z ∘ σ) ≤ 33 * Real.pi ^ 2 / 256 ∧
        meanSquare (polarConstraint hm β u) ≤ 65 * Real.pi ^ 2 ∧
        ‖operator (2 * m) (polarConstraint hm β u)‖ ≤ 31 * Real.pi / 64 ∧
        actualRemainder hm β u ≤ remainderBudget hm (31 * Real.pi / 64) β u ∧
        actualAngularSum hm β u ≤ actualAngularBudget hm β u := by
  obtain ⟨m₀, h₀⟩ := eventual_diameter_pressure_gap
  have hN : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 2 * m) tendsto_id
  obtain ⟨m₁, h₁⟩ := eventually_atTop.1 ((sizeBudget_tendsto hN).eventually_le_const
    (by norm_num : (0 : ℝ) < 1 / 16))
  refine ⟨max 8 (max m₀ m₁), ?_⟩
  intro m hm z hz
  have hm8 : 8 ≤ m := le_trans (le_max_left _ _) hm
  have hm0 : m₀ ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm
  have hm1 : m₁ ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm
  obtain ⟨hmp, σ, α, β, u, η, hmodel, hc, hη, hJ, herr, hG⟩ := h₀ m hm0 z hz
  refine ⟨hmp, σ, α, β, u, η, hmodel, hc, hη, hJ,
    model_constraint_mass (by omega) hmodel hη hJ herr, hG, ?_,
    model_angular_sum_le (by omega) hmodel hη hJ hc herr hG⟩
  simpa only [remainderBudget, radialErrorCoefficient, Nat.cast_mul, Nat.cast_ofNat] using
    model_remainder_le hm8 hmodel hη hz hJ hc (h₁ m hm1) hG

end StructuralNote.ActualSignedAngular
