import StructuralNote.SignedCrossingPressure
import EventualExact.DiscreteEnergyBounds

/-! Energy absorption of the explicit remainder in the signed crossing expansion. -/

noncomputable section
open scoped BigOperators

namespace StructuralNote.SignedPressureRemainder

open Erdos1045 Erdos1045.EventualExact GapRigidity SignedCrossingPressure

theorem fourth_sum_le (x y : ℝ) : (x + y) ^ 4 ≤ 8 * (x ^ 4 + y ^ 4) := by
  nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg ((x + y) ^ 2 - 2 * (x ^ 2 + y ^ 2)),
    sq_nonneg (x - y), sq_nonneg (x + y)]

theorem centerStep_norm_le {ρ : ℝ} (η : ℝ) {c₀ c₁ : ℂ}
    (h₀ : ‖c₀‖ ≤ ρ) (h₁ : ‖c₁‖ ≤ ρ) : ‖centerStep η c₀ c₁‖ ≤ 2 * ρ := by
  calc
    _ ≤ ‖circle (η / 2) * c₁‖ + ‖circle (-(η / 2)) * c₀‖ := norm_sub_le _ _
    _ = ‖c₁‖ + ‖c₀‖ := by rw [norm_mul, norm_mul, circle_norm, circle_norm]; ring
    _ ≤ _ := by linarith

/-- A direct scalar bound. Its inputs are pointwise geometric budgets, rather
than an assumed Taylor or summed-remainder estimate. -/
theorem remainder_le {a η b₀ b₁ g ρ B G : ℝ} {c₀ c₁ : ℂ}
    (ha0 : 0 ≤ a) (ha : a ≤ 1 / 4) (hη : |η| ≤ 1)
    (hρ : ρ ≤ 1) (h₀ : ‖c₀‖ ≤ ρ) (h₁ : ‖c₁‖ ≤ ρ)
    (hb0 : 0 ≤ b₀ + b₁) (hb : b₀ + b₁ ≤ B) (hg : |g| ≤ G) :
    remainder a η b₀ b₁ g c₀ c₁ ≤
      G * (2 * η ^ 2 + 9 * a ^ 4 + (B + 2 * ρ) * (b₀ + b₁)) := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg c₀).trans h₀
  have hG : 0 ≤ G := (abs_nonneg g).trans hg
  have hB : 0 ≤ B := hb0.trans hb
  have hη2 : η ^ 2 ≤ 1 := by nlinarith only [hη, sq_abs η, abs_nonneg η]
  have hη4 : η ^ 4 ≤ η ^ 2 := by nlinarith only [hη2, sq_nonneg η]
  have hη3 : |η| ^ 3 ≤ η ^ 2 := by
    calc
      _ = |η| * η ^ 2 := by rw [pow_succ, sq_abs]; ring
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hη (sq_nonneg η)]
  have hφ4 : (a + η / 2) ^ 4 ≤ 8 * a ^ 4 + η ^ 2 / 2 := by
    have h := fourth_sum_le a (η / 2)
    nlinarith only [h, hη4]
  have hφ : |a + η / 2| ≤ 1 := by
    calc
      _ ≤ |a| + |η / 2| := abs_add_le _ _
      _ = a + |η| / 2 := by rw [abs_of_nonneg ha0, abs_div]; norm_num
      _ ≤ _ := by linarith
  have hX : |(c₁ - c₀).re| ≤ 2 * ρ :=
    (Complex.abs_re_le_norm _).trans ((norm_sub_le _ _).trans (by linarith))
  have hY : |(c₁ + c₀).im| ≤ 2 * ρ :=
    (Complex.abs_im_le_norm _).trans ((norm_add_le _ _).trans (by linarith))
  have hI : |(centerStep η c₀ c₁).im| ≤ 2 * ρ :=
    (Complex.abs_im_le_norm _).trans (centerStep_norm_le η h₀ h₁)
  have hcross : (b₀ + b₁) * |a + η / 2| * |(centerStep η c₀ c₁).im| ≤
      2 * ρ * (b₀ + b₁) := by
    have hh := mul_le_mul hφ hI (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith only [mul_le_mul_of_nonneg_left hh hb0]
  have hb2 : (b₀ + b₁) ^ 2 ≤ B * (b₀ + b₁) := by
    nlinarith only [mul_le_mul_of_nonneg_right hb hb0]
  have hbase : η ^ 2 / 4 + (b₀ + b₁) ^ 2 + (a + η / 2) ^ 4 + a ^ 4 / 12 +
      (b₀ + b₁) * |a + η / 2| * |(centerStep η c₀ c₁).im| ≤
      η ^ 2 + 9 * a ^ 4 + (B + 2 * ρ) * (b₀ + b₁) := by
    nlinarith only [hφ4, hb2, hcross, sq_nonneg (a ^ 2), sq_nonneg η]
  have hmain := mul_le_mul hg hbase (by positivity) hG
  have hgre : |g * (c₁ - c₀).re| ≤ G * (2 * ρ) := by
    rw [abs_mul]
    exact mul_le_mul hg hX (abs_nonneg _) hG
  have hgim : |g * (c₁ + c₀).im| ≤ G * (2 * ρ) := by
    rw [abs_mul]
    exact mul_le_mul hg hY (abs_nonneg _) hG
  have ht₁ : η ^ 2 / 8 * |g * (c₁ - c₀).re| ≤ G * η ^ 2 / 4 := by
    have hh := mul_le_mul_of_nonneg_left hgre (show 0 ≤ η ^ 2 / 8 by positivity)
    have hr := mul_le_mul_of_nonneg_left hρ (show 0 ≤ G * η ^ 2 by positivity)
    nlinarith only [hh, hr]
  have ht₂ : |η| ^ 3 / 48 * |g * (c₁ + c₀).im| ≤ G * η ^ 2 / 24 := by
    have hh := mul_le_mul_of_nonneg_left hgim (show 0 ≤ |η| ^ 3 / 48 by positivity)
    have hr := mul_le_mul_of_nonneg_left hρ (show 0 ≤ G * |η| ^ 3 by positivity)
    have he := mul_le_mul_of_nonneg_left hη3 hG
    nlinarith only [hh, hr, he]
  unfold remainder
  nlinarith only [hmain, ht₁, ht₂, mul_nonneg hG (sq_nonneg η)]

/-- The cyclic sum of radial pair errors has exactly two copies of each deficit. -/
theorem sum_remainder_le {n : ℕ} (p : Equiv.Perm (Fin n)) (a : ℝ)
    (η b g : Fin n → ℝ) (c₀ c₁ : Fin n → ℂ) {ρ B G : ℝ}
    (ha0 : 0 ≤ a) (ha : a ≤ 1 / 4) (hη : ∀ j, |η j| ≤ 1)
    (hρ : ρ ≤ 1) (h₀ : ∀ j, ‖c₀ j‖ ≤ ρ) (h₁ : ∀ j, ‖c₁ j‖ ≤ ρ)
    (hb0 : ∀ j, 0 ≤ b j) (hb : ∀ j, b j + b (p j) ≤ B) (hg : ∀ j, |g j| ≤ G) :
    (∑ j, remainder a (η j) (b j) (b (p j)) (g j) (c₀ j) (c₁ j)) ≤
      G * (2 * (∑ j, η j ^ 2) + 9 * n * a ^ 4 +
        2 * (B + 2 * ρ) * ∑ j, b j) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    remainder_le ha0 ha (hη j) hρ (h₀ j) (h₁ j)
      (add_nonneg (hb0 j) (hb0 (p j))) (hb j) (hg j))
  have hp : (∑ j, b (p j)) = ∑ j, b j := Equiv.sum_comp p b
  rw [← Finset.mul_sum] at h
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hp] at h
  convert h using 1 <;> first | rfl | ring

theorem reciprocal_sine_le {n : ℕ} (hn : 2 ≤ n) :
    0 < Real.sin (Real.pi / n) ∧ 1 / (2 * Real.sin (Real.pi / n)) ≤ (n : ℝ) / 4 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hangle : Real.pi / n ≤ Real.pi / 2 := by
    apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hnR
  have hs := Real.mul_le_sin (show 0 ≤ Real.pi / n by positivity) hangle
  have he : 2 / Real.pi * (Real.pi / n) = 2 / (n : ℝ) := by field_simp
  rw [he] at hs
  have hpos : 0 < Real.sin (Real.pi / n) := (by positivity : 0 < 2 / (n : ℝ)).trans_le hs
  refine ⟨hpos, (div_le_iff₀ (by positivity : 0 < 2 * Real.sin (Real.pi / n))).2 ?_⟩
  have hprod := (div_le_iff₀ hn0).1 hs
  nlinarith

theorem normalized_remainder_le {n : ℕ} (hn : 16 ≤ n) (p : Equiv.Perm (Fin n))
    (η b g : Fin n → ℝ) (c₀ c₁ : Fin n → ℂ) {ρ B G : ℝ}
    (hη : ∀ j, |η j| ≤ 1) (hρ : ρ ≤ 1)
    (h₀ : ∀ j, ‖c₀ j‖ ≤ ρ) (h₁ : ∀ j, ‖c₁ j‖ ≤ ρ)
    (hb0 : ∀ j, 0 ≤ b j) (hb : ∀ j, b j + b (p j) ≤ B) (hg : ∀ j, |g j| ≤ G) :
    (∑ j, remainder (Real.pi / n) (η j) (b j) (b (p j)) (g j) (c₀ j) (c₁ j)) /
        (2 * Real.sin (Real.pi / n)) ≤
      G * n / 2 * (∑ j, η j ^ 2) + 9 * G * Real.pi ^ 4 / (4 * (n : ℝ) ^ 2) +
        G / 2 * (B + 2 * ρ) * ((n : ℝ) * ∑ j, b j) := by
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have ha : Real.pi / n ≤ (1 : ℝ) / 4 := by
    apply (div_le_iff₀ hn0).2
    nlinarith [Real.pi_lt_four]
  have h := sum_remainder_le p (Real.pi / n) η b g c₀ c₁
    (by positivity) ha hη hρ h₀ h₁ hb0 hb hg
  have hs := reciprocal_sine_le (show 2 ≤ n by omega)
  have hR : 0 ≤ ∑ j, remainder (Real.pi / n) (η j) (b j) (b (p j)) (g j) (c₀ j) (c₁ j) := by
    exact Finset.sum_nonneg fun j _ => remainder_nonneg _ _ _ _ _ _ _
      (add_nonneg (hb0 j) (hb0 (p j)))
  calc
    _ = (1 / (2 * Real.sin (Real.pi / n))) *
        ∑ j, remainder (Real.pi / n) (η j) (b j) (b (p j)) (g j) (c₀ j) (c₁ j) := by ring
    _ ≤ ((n : ℝ) / 4) * ∑ j, remainder (Real.pi / n) (η j) (b j) (b (p j)) (g j) (c₀ j) (c₁ j) :=
      mul_le_mul_of_nonneg_right hs.2 hR
    _ ≤ ((n : ℝ) / 4) * (G * (2 * (∑ j, η j ^ 2) + 9 * n * (Real.pi / n) ^ 4 +
        2 * (B + 2 * ρ) * ∑ j, b j)) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by field_simp; ring

/-- The required energy scale follows from the proved Fourier difference estimate. -/
theorem energy_remainder_le {n : ℕ} (hn : 16 ≤ n) (p : Equiv.Perm (Fin n))
    (θ b g : Fin n → ℝ) (c₀ c₁ : Fin n → ℂ) {ρ B G : ℝ}
    (hθ : ∀ j, |θ (FiniteFourierLift.successor (by omega) j) - θ j| ≤ 1)
    (hρ : ρ ≤ 1) (h₀ : ∀ j, ‖c₀ j‖ ≤ ρ) (h₁ : ∀ j, ‖c₁ j‖ ≤ ρ)
    (hb0 : ∀ j, 0 ≤ b j) (hb : ∀ j, b j + b (p j) ≤ B) (hg : ∀ j, |g j| ≤ G) :
    (∑ j, remainder (Real.pi / n) (θ (FiniteFourierLift.successor (by omega) j) - θ j)
      (b j) (b (p j)) (g j) (c₀ j) (c₁ j)) / (2 * Real.sin (Real.pi / n)) ≤
      4 * G * Real.pi ^ 2 / n * DiscreteEnergy.realEnergy (by omega) θ +
        9 * G * Real.pi ^ 4 / (4 * (n : ℝ) ^ 2) +
        G / 2 * (B + 2 * ρ) * ((n : ℝ) * ∑ j, b j) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hG : 0 ≤ G := (abs_nonneg (g ⟨0, by omega⟩)).trans (hg _)
  have h := normalized_remainder_le hn p (fun j => θ (FiniteFourierLift.successor (by omega) j) - θ j)
    b g c₀ c₁ hθ hρ h₀ h₁ hb0 hb hg
  have he := DiscreteEnergy.difference_energy_le (show 0 < n by omega) (fun j => (θ j : ℂ))
  simp only [FiniteFourierLift.difference, ← Complex.ofReal_sub, Complex.normSq_ofReal, ← pow_two] at he
  change (n : ℝ) ^ 2 * (∑ j, (θ (FiniteFourierLift.successor (by omega) j) - θ j) ^ 2) ≤
    8 * Real.pi ^ 2 * DiscreteEnergy.realEnergy (by omega) θ at he
  have hscaled := mul_le_mul_of_nonneg_left he (show 0 ≤ G / (2 * (n : ℝ)) by positivity)
  have hmain : G * n / 2 * (∑ j, (θ (FiniteFourierLift.successor (by omega) j) - θ j) ^ 2) ≤
      4 * G * Real.pi ^ 2 / n * DiscreteEnergy.realEnergy (by omega) θ := by
    convert hscaled using 1
    · rfl
    · field_simp
    · field_simp
      ring
  linarith

open Configuration CommonLocalization ExtremalPolarCenter PolarAngleControl
open NormalizedPolarRepresentation PressureCoercivity ActualPressureGap

theorem model_energy_le {n : ℕ} (hn : 4 ≤ n) {z : Points n}
    {σ : Equiv.Perm (Fin n)} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hη : η ≤ 1 / 1024)
    (hJ : objective (regular n) - objective (z ∘ σ) ≤ 33 * Real.pi ^ 2 / 256) :
    ExtremalEnergyBound.totalEnergy n u ≤ 32 * Real.pi ^ 2 := by
  have hj := (model_objectiveDeficit_eq hn h (by linarith)).trans_le hJ
  have hs : ∀ j, ‖SchurSpectrum.periodize (by omega) (fun j : Fin n => u j) (j + 1) -
      SchurSpectrum.periodize (by omega) (fun j : Fin n => u j) j‖ ≤ η * ‖LocalPhase.regularRoot n - 1‖ := by
    simpa only [ActualPressureGap.periodize_restrict _ _ h.periodic] using h.relative_edges
  have he := energy_le_objective_budget hn (fun j : Fin n => u j)
    (model_first_zero (by omega) h) h.error_nonneg (by linarith) hs hj
  change ExtremalEnergyBound.totalEnergy n
    (SchurSpectrum.periodize (by omega) (fun j : Fin n => u j)) ≤ _ at he
  rw [ActualPressureGap.periodize_restrict _ _ h.periodic] at he
  nlinarith [sq_nonneg Real.pi]

def radialDeficit (m : ℕ) (β : ℂ) (u : ℕ → ℂ) (j : Fin (2 * m)) : ℝ :=
  1 - PolarRepresentation.radius m ‖β‖ u j

def radialMass (m : ℕ) (β : ℂ) (u : ℕ → ℂ) : ℝ :=
  (2 * m : ℝ) * ∑ j, radialDeficit m β u j

theorem finRotate_eq_successor {n : ℕ} (hn : 2 ≤ n) (j : Fin n) :
    finRotate n j = FiniteFourierLift.successor (by omega) j := by
  let : NeZero n := ⟨by omega⟩
  rw [finRotate_apply]
  apply Fin.ext
  change (j.val + 1 % n) % n = (j.val + 1) % n
  rw [Nat.mod_eq_of_lt (show 1 < n by omega)]

def rotatedCenter (m : ℕ) (β : ℂ) (u : ℕ → ℂ) (j k : Fin (2 * m)) : ℂ :=
  (starRingEnd ℂ) (SchurLift.frame (2 * m) j) * polarCenter m β u k

def actualRemainder {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ) : ℝ :=
  (∑ j, remainder (Real.pi / (2 * m))
    (normalizedAngle m u (FiniteFourierLift.successor (by omega) j) - normalizedAngle m u j)
    (radialDeficit m β u j) (radialDeficit m β u (finRotate (2 * m) j))
    (FourierMultiplier.operator (2 * m) (polarConstraint hm β u) j)
    (rotatedCenter m β u j j)
    (rotatedCenter m β u j (FiniteFourierLift.successor (by omega) j))) /
      (2 * Real.sin (Real.pi / (2 * m)))

theorem rotatedCenter_norm (m : ℕ) (β : ℂ) (u : ℕ → ℂ) (j k : Fin (2 * m)) :
    ‖rotatedCenter m β u j k‖ = ‖polarCenter m β u k‖ := by
  have hf : ‖SchurLift.frame (2 * m) j‖ = 1 := by
    have h := SchurLift.frame_normSq (2 * m) j
    rw [Complex.normSq_eq_norm_sq] at h
    nlinarith [norm_nonneg (SchurLift.frame (2 * m) j)]
  simp only [rotatedCenter, norm_mul, Complex.norm_conj, hf, one_mul]

/-- The summed remainder estimate in the same coordinates as the actual pressure
gap. The objective budget implies the old energy and matching budgets internally. -/
theorem model_remainder_le {m : ℕ} (hm : 8 ≤ m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hη : η ≤ 1 / 1024)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (hJ : objective (regular (2 * m)) - objective (z ∘ σ) ≤ 33 * Real.pi ^ 2 / 256)
    (hc : CenterBounds (m := m) (by omega) β u)
    (hS : sizeBudget (2 * m) ≤ 1 / 16) {G : ℝ}
    (hg : ‖FourierMultiplier.operator (2 * m) (polarConstraint (by omega) β u)‖ ≤ G) :
    actualRemainder (m := m) (by omega) β u ≤
      4 * G * Real.pi ^ 2 / (2 * m) * DiscreteEnergy.realEnergy (by omega) (normalizedAngle m u) +
        9 * G * Real.pi ^ 4 / (4 * (2 * m : ℝ) ^ 2) +
        G / 2 * (512 * Real.pi ^ 2 / (2 * m) + 4 * Real.sqrt (sizeBudget (2 * m))) * radialMass m β u := by
  have hE := model_energy_le (show 4 ≤ 2 * m by omega) h hη hJ
  have hp := model_polar_bounds (show 2 ≤ m by omega) h hE (by linarith)
  have hS0 := sizeBudget_nonneg (show 1 ≤ 2 * m by omega)
  have hsqrt := Real.sq_sqrt hS0
  have hroot : Real.sqrt (sizeBudget (2 * m)) ≤ 1 / 4 := by
    nlinarith [Real.sqrt_nonneg (sizeBudget (2 * m))]
  have hθ : ∀ j, |normalizedAngle m u (FiniteFourierLift.successor (by omega) j) -
      normalizedAngle m u j| ≤ 1 := by
    intro j
    have ha (k : ℕ) : |angle m u k| ≤ 1 / 2 := by
      nlinarith [hp.angle_size k, abs_nonneg (angle m u k)]
    simp only [normalizedAngle, rawAngle, sub_sub_sub_cancel_right]
    exact (abs_sub _ _).trans (by linarith [ha j, ha (FiniteFourierLift.successor (by omega) j)])
  have hcenter : ∀ j k, ‖rotatedCenter m β u j k‖ ≤ 2 * Real.sqrt (sizeBudget (2 * m)) := by
    intro j k
    rw [rotatedCenter_norm]
    have hnorm := norm_le_pi_norm (polarCenter m β u) k
    have hbound : ‖polarCenter m β u‖ ≤ 2 * Real.sqrt (sizeBudget (2 * m)) := by
      nlinarith [hc.size, norm_nonneg (polarCenter m β u), Real.sqrt_nonneg (sizeBudget (2 * m))]
    exact hnorm.trans hbound
  have hb0 (j : Fin (2 * m)) : 0 ≤ radialDeficit m β u j :=
    sub_nonneg.mpr (PolarRepresentation.model_radius_le_one (by omega) h hz.1 j)
  have ht := (ExtremalScaleBound.model_matching_deficit_bound (show 2 ≤ m by omega)
    h (by linarith) hz hE).2.2
  simp_rw [PolarRepresentation.model_matching_norm (by omega) h] at ht
  change radialMass m β u ≤ 256 * Real.pi ^ 2 at ht
  have hn0 : (0 : ℝ) < 2 * m := by positivity
  have hb (j : Fin (2 * m)) : radialDeficit m β u j ≤ 256 * Real.pi ^ 2 / (2 * m) := by
    apply (le_div_iff₀ hn0).2
    have hh := Finset.single_le_sum (s := Finset.univ) (f := radialDeficit m β u)
      (fun k _ => hb0 k) (Finset.mem_univ j)
    have hmul := mul_le_mul_of_nonneg_left hh hn0.le
    unfold radialMass at ht
    nlinarith only [ht, hmul]
  have hgp (j : Fin (2 * m)) :
      |FourierMultiplier.operator (2 * m) (polarConstraint (by omega) β u) j| ≤ G := by
    have hh := norm_le_pi_norm
      (FourierMultiplier.operator (2 * m) (polarConstraint (by omega) β u)) j
    rw [Real.norm_eq_abs] at hh
    exact hh.trans hg
  have hr := energy_remainder_le (show 16 ≤ 2 * m by omega) (finRotate (2 * m))
    (normalizedAngle m u) (radialDeficit m β u)
    (FourierMultiplier.operator (2 * m) (polarConstraint (by omega) β u))
    (fun j => rotatedCenter m β u j j)
    (fun j => rotatedCenter m β u j (FiniteFourierLift.successor (by omega) j))
    hθ (show 2 * Real.sqrt (sizeBudget (2 * m)) ≤ 1 by linarith)
    (fun j => hcenter j j) (fun j => hcenter j _) hb0
    (fun j => show radialDeficit m β u j + radialDeficit m β u (finRotate (2 * m) j) ≤
      512 * Real.pi ^ 2 / (2 * m) by
        calc
          _ ≤ 256 * Real.pi ^ 2 / (2 * m) + 256 * Real.pi ^ 2 / (2 * m) :=
            add_le_add (hb j) (hb (finRotate (2 * m) j))
          _ = _ := by ring) hgp
  simpa only [actualRemainder, radialMass, Nat.cast_mul, Nat.cast_ofNat, show (2 : ℝ) * (2 * Real.sqrt (sizeBudget (2 * m))) =
    4 * Real.sqrt (sizeBudget (2 * m)) by ring] using hr

def radialErrorCoefficient (n : ℕ) (G : ℝ) : ℝ :=
  G / 2 * (512 * Real.pi ^ 2 / n + 4 * Real.sqrt (sizeBudget n))

def remainderBudget {m : ℕ} (hm : 0 < m) (G : ℝ) (β : ℂ) (u : ℕ → ℂ) : ℝ :=
  4 * G * Real.pi ^ 2 / (2 * m) * DiscreteEnergy.realEnergy (by omega) (normalizedAngle m u) +
    9 * G * Real.pi ^ 4 / (4 * (2 * m : ℝ) ^ 2) +
    radialErrorCoefficient (2 * m) G * radialMass m β u

open Filter
open scoped Topology

theorem radialErrorCoefficient_tendsto {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) (G : ℝ) :
    Tendsto (fun k => radialErrorCoefficient (N k) G) atTop (𝓝 0) := by
  have hdiv := (tendsto_const_div_atTop_nhds_zero_nat (512 * Real.pi ^ 2)).comp hN
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp (sizeBudget_tendsto hN)
  simpa only [radialErrorCoefficient, Real.sqrt_zero, mul_zero, add_zero, Function.comp_def] using
    (hdiv.add (hs.const_mul 4)).const_mul (G / 2)

/-- Actual global maximizers acquire the pressure and remainder bounds in one
and the same set of normalized coordinates. No remainder budget is an input. -/
theorem eventual_diameter_remainder :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z : Points (2 * m),
      ExtremalNormalization.DiameterExtremal z →
      ∃ (hm : 0 < m) (σ : Equiv.Perm (Fin (2 * m))) (α β : ℂ) (u : ℕ → ℂ) (η : ℝ),
        NormalizedRelativeEdgeModel z σ α β u η ∧ CenterBounds hm β u ∧
        η ≤ 1 / 1024 ∧ objective (regular (2 * m)) - objective (z ∘ σ) ≤ 33 * Real.pi ^ 2 / 256 ∧
        ‖FourierMultiplier.operator (2 * m) (polarConstraint hm β u)‖ ≤ 31 * Real.pi / 64 ∧
        actualRemainder hm β u ≤ remainderBudget hm (31 * Real.pi / 64) β u := by
  obtain ⟨m₀, hpressure⟩ := eventual_diameter_pressure_gap
  have hN : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_mono (fun m : ℕ => show m ≤ 2 * m by omega) tendsto_id
  have hs : ∀ᶠ m : ℕ in atTop, sizeBudget (2 * m) ≤ 1 / 16 :=
    (sizeBudget_tendsto hN).eventually_le_const (by norm_num : (0 : ℝ) < 1 / 16)
  obtain ⟨m₁, hsmall⟩ := eventually_atTop.1 hs
  refine ⟨max m₀ (max m₁ 8), ?_⟩
  intro m hm z hz
  obtain ⟨hmpos, σ, α, β, u, η, h, hc, hη, hJ, _, hg⟩ := hpressure m (by omega) z hz
  refine ⟨hmpos, σ, α, β, u, η, h, hc, hη, hJ, hg, ?_⟩
  have hr := model_remainder_le (show 8 ≤ m by omega) h hη hz hJ hc (hsmall m (by omega)) hg
  simpa only [remainderBudget, radialErrorCoefficient, Nat.cast_mul, Nat.cast_ofNat] using hr

end StructuralNote.SignedPressureRemainder
