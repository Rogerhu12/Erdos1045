import StructuralNote.FixedSchurChosenLinearization
import StructuralNote.FixedSchurSecondSourceTools

/-! Moment bounds for the actual first jet entering the second source. -/

namespace StructuralNote.FixedSchurChosenSecondMoments

open Filter Complex Erdos1045.EventualExact FiniteBox SchurSpectrum SchurLiftBounds
open CommonClosureEnergy CommonDomainClosure CommonTangentialParameters
open CommonFiberCanonicalDirections EdgeCoordinates
open FixedSchurData FixedSchurChart FixedSchurHarmonicBounds
open FixedSchurNormalExpansion FixedSchurRotatedPath
open FixedSchurRotatedCoefficients FixedSchurFirstSource
open FixedSchurRotatedInverse
open FixedSchurFirstSourceSup FixedSchurDerivativeScales
open FixedSchurSecondSourceTools FixedSchurChosenPath
open FixedSchurChosenLinearization FixedSchurQuadraticExpansion
open FixedSchurNormalInnerEnergy FixedSchurDirectionMoments
open scoped BigOperators Topology

noncomputable section

def firstP {m : ℕ} (hm : 0 < m) (w : SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ) :
    Fin (2 * m) → ℝ :=
  J (chosenFirstDerivative hm w θ η v h) + tangent (by omega) h

def rotationVelocity {m : ℕ} (hm : 0 < m) (w : SignPattern hm)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ) :
    Fin (2 * m) → ℝ :=
  fun j => firstTangential hm w θ η v h j -
    baseRadial hm w θ v j * angleAverage (by omega) η j

private theorem rotated_meanSquare_bounds {n : ℕ} (_hn : 0 < n)
    (b q p : Fin n → ℝ) :
    meanSquare (fun j => r (q j) (p j) (b j)) ≤
        2 * meanSquare q + 2 * meanSquare p ∧
      meanSquare (fun j => s (q j) (p j) (b j)) ≤
        2 * meanSquare q + 2 * meanSquare p := by
  let qc : Fin n → ℝ := fun j => q j * Real.cos (b j)
  let ps : Fin n → ℝ := fun j => p j * Real.sin (b j)
  let pc : Fin n → ℝ := fun j => p j * Real.cos (b j)
  let qs : Fin n → ℝ := fun j => q j * Real.sin (b j)
  have hqc : meanSquare qc ≤ meanSquare q := by
    have h := meanSquare_domination qc q (show 0 ≤ (1 : ℝ) by norm_num) (fun j => by
      dsimp [qc]
      rw [abs_mul, one_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
    simpa only [one_pow, one_mul] using h
  have hps : meanSquare ps ≤ meanSquare p := by
    have h := meanSquare_domination ps p (show 0 ≤ (1 : ℝ) by norm_num) (fun j => by
      dsimp [ps]
      rw [abs_mul, one_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _))
    simpa only [one_pow, one_mul] using h
  have hpc : meanSquare pc ≤ meanSquare p := by
    have h := meanSquare_domination pc p (show 0 ≤ (1 : ℝ) by norm_num) (fun j => by
      dsimp [pc]
      rw [abs_mul, one_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
    simpa only [one_pow, one_mul] using h
  have hqs : meanSquare qs ≤ meanSquare q := by
    have h := meanSquare_domination qs q (show 0 ≤ (1 : ℝ) by norm_num) (fun j => by
      dsimp [qs]
      rw [abs_mul, one_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _))
    simpa only [one_pow, one_mul] using h
  constructor
  · calc
      meanSquare (fun j => r (q j) (p j) (b j)) = meanSquare (qc + ps) := by
        congr 1
      _ ≤ 2 * meanSquare qc + 2 * meanSquare ps := meanSquare_add_le qc ps
      _ ≤ 2 * meanSquare q + 2 * meanSquare p := by
        linarith only [hqc, hps]
  · have ha := meanSquare_add_le pc (-qs)
    have hneg : meanSquare (-qs) = meanSquare qs := by
      unfold meanSquare
      simp
    rw [hneg] at ha
    calc
      meanSquare (fun j => s (q j) (p j) (b j)) = meanSquare (pc + (-qs)) := by
        congr 1
      _ ≤ 2 * meanSquare pc + 2 * meanSquare qs := ha
      _ ≤ 2 * meanSquare q + 2 * meanSquare p := by
        linarith only [hpc, hqs]

private theorem rotated_norm_sq_bounds {n : ℕ} (b q p : Fin n → ℝ) :
    ‖fun j => r (q j) (p j) (b j)‖ ^ 2 ≤
        2 * (‖q‖ ^ 2 + ‖p‖ ^ 2) ∧
      ‖fun j => s (q j) (p j) (b j)‖ ^ 2 ≤
        2 * (‖q‖ ^ 2 + ‖p‖ ^ 2) := by
  have hr (j : Fin n) : r (q j) (p j) (b j) ^ 2 ≤
      2 * (‖q‖ ^ 2 + ‖p‖ ^ 2) := by
    have hq : |q j| ≤ ‖q‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm q j
    have hp : |p j| ≤ ‖p‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm p j
    have hc := Real.abs_cos_le_one (b j)
    have hs := Real.abs_sin_le_one (b j)
    have hqa := mul_le_mul hq hc (abs_nonneg _) (norm_nonneg _)
    have hpa := mul_le_mul hp hs (abs_nonneg _) (norm_nonneg _)
    have hsum := abs_add_le (q j * Real.cos (b j)) (p j * Real.sin (b j))
    have habs : |q j * Real.cos (b j) + p j * Real.sin (b j)| ≤
        ‖q‖ + ‖p‖ := by
      rw [abs_mul, abs_mul] at hsum
      norm_num at hqa hpa
      linarith only [hsum, hqa, hpa]
    have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
    rw [sq_abs] at hsq
    dsimp [r]
    nlinarith [hsq, sq_nonneg (‖q‖ - ‖p‖)]
  have hs (j : Fin n) : s (q j) (p j) (b j) ^ 2 ≤
      2 * (‖q‖ ^ 2 + ‖p‖ ^ 2) := by
    have hq : |q j| ≤ ‖q‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm q j
    have hp : |p j| ≤ ‖p‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm p j
    have hc := Real.abs_cos_le_one (b j)
    have hsi := Real.abs_sin_le_one (b j)
    have hpa := mul_le_mul hp hc (abs_nonneg _) (norm_nonneg _)
    have hqa := mul_le_mul hq hsi (abs_nonneg _) (norm_nonneg _)
    have hsub := abs_sub (p j * Real.cos (b j)) (q j * Real.sin (b j))
    have habs : |p j * Real.cos (b j) - q j * Real.sin (b j)| ≤
        ‖p‖ + ‖q‖ := by
      rw [abs_mul, abs_mul] at hsub
      norm_num at hpa hqa
      linarith only [hsub, hpa, hqa]
    have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
    rw [sq_abs] at hsq
    dsimp [s]
    nlinarith [hsq, sq_nonneg (‖q‖ - ‖p‖)]
  exact ⟨norm_sq_le_of_pointwise _ (by positivity) hr,
    norm_sq_le_of_pointwise _ (by positivity) hs⟩

theorem eventual_chosen_first_moments : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (w : SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      let E := pairEnergy (by omega) (fun j => (η j : ℂ))
      let A := pairEnergy (by omega) h
      let K := E + A
      let q := chosenFirstDerivative (by omega) w θ η v h
      let p := firstP (by omega) w θ η v h
      meanSquare q ≤ 80000 * K / (2 * m : ℝ) ∧
      ‖q‖ ^ 2 ≤ 200000 * K ∧
      meanSquare p ≤ 700000 * K / (2 * m : ℝ) +
        16 * (2 * m : ℝ) * A ∧
      ‖p‖ ^ 2 ≤ 1600000 * K + 16 * (2 * m : ℝ) ^ 2 * A ∧
      meanSquare (firstRadial (by omega) w θ η v h) ≤
        1600000 * K / (2 * m : ℝ) + 32 * (2 * m : ℝ) * A ∧
      ‖firstRadial (by omega) w θ η v h‖ ^ 2 ≤
        3600000 * K + 32 * (2 * m : ℝ) ^ 2 * A ∧
      meanSquare (firstTangential (by omega) w θ η v h) ≤
        1600000 * K / (2 * m : ℝ) + 32 * (2 * m : ℝ) * A ∧
      ‖firstTangential (by omega) w θ η v h‖ ^ 2 ≤
        3600000 * K + 32 * (2 * m : ℝ) ^ 2 * A ∧
      meanSquare (rotationVelocity (by omega) w θ η v h) ≤
        3300000 * K / (2 * m : ℝ) + 64 * (2 * m : ℝ) * A ∧
      ‖rotationVelocity (by omega) w θ η v h‖ ^ 2 ≤
        7200200 * K + 64 * (2 * m : ℝ) ^ 2 * A := by
  filter_upwards [eventual_chosen_normalLinearizations,
    eventual_first_solution_coarse, eventual_radialCoefficient_bound] with
      m hlin hcoarse hrad
  intro hm w θ η v h hdom hd
  dsimp only
  let E := pairEnergy (by omega) (fun j => (η j : ℂ))
  let A := pairEnergy (by omega) h
  let K := E + A
  let q := chosenFirstDerivative (by omega) w θ η v h
  let p := firstP (by omega) w θ η v h
  have hE : 0 ≤ E := by dsimp [E]; exact pairEnergy_nonneg (by omega) _
  have hA : 0 ≤ A := by dsimp [A]; exact pairEnergy_nonneg (by omega) _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hn : (1 : ℝ) ≤ 2 * m := by exact_mod_cast (show 1 ≤ 2 * m by omega)
  have hnpos : (0 : ℝ) < 2 * m := lt_of_lt_of_le (by norm_num) hn
  have hq := hcoarse hm w θ η v h hdom hd.2.1 q
    (hlin hm w θ η v h hdom hd).1
  change meanSquare q ≤ 80000 * K / (2 * m : ℝ) ∧
    ‖q‖ ^ 2 ≤ 200000 * K at hq
  have hpi : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
  have htms0 := tangent_meanSquare_le (show 2 ≤ 2 * m by omega) h
  simp only [Nat.cast_mul, Nat.cast_ofNat] at htms0
  change meanSquare (tangent (by omega) h) ≤
    (Real.pi ^ 2 / 2) * (2 * m : ℝ) * A at htms0
  have hpiA := mul_le_mul_of_nonneg_right hpi
    (mul_nonneg (show 0 ≤ (2 * m : ℝ) by positivity) hA)
  have htms : meanSquare (tangent (by omega) h) ≤ 8 * (2 * m : ℝ) * A := by
    nlinarith only [htms0, hpiA]
  have htnorm : ‖tangent (by omega) h‖ ^ 2 ≤
      8 * (2 * m : ℝ) ^ 2 * A := by
    apply norm_sq_le_of_pointwise _ (by positivity)
    intro j
    have ht := tangent_pointwise_sq_le (show 2 ≤ 2 * m by omega) h j
    simp only [Nat.cast_mul, Nat.cast_ofNat] at ht
    change tangent (by omega) h j ^ 2 ≤
      (Real.pi ^ 2 / 2) * (2 * m : ℝ) ^ 2 * A at ht
    have hpiA2 := mul_le_mul_of_nonneg_right hpi
      (mul_nonneg (sq_nonneg (2 * m : ℝ)) hA)
    nlinarith only [ht, hpiA2]
  have hJms := J_meanSquare_le (show 0 < 2 * m by omega) q
  have hpms0 := meanSquare_add_le (J q) (tangent (by omega) h)
  change meanSquare p ≤ 2 * meanSquare (J q) +
    2 * meanSquare (tangent (by omega) h) at hpms0
  have hpms : meanSquare p ≤ 700000 * K / (2 * m : ℝ) +
      16 * (2 * m : ℝ) * A := by
    calc
      _ ≤ 2 * meanSquare (J q) + 2 * meanSquare (tangent (by omega) h) := hpms0
      _ ≤ 8 * meanSquare q + 2 * meanSquare (tangent (by omega) h) := by
        linarith only [hJms]
      _ ≤ 8 * (80000 * K / (2 * m : ℝ)) +
          2 * (8 * (2 * m : ℝ) * A) :=
        add_le_add (mul_le_mul_of_nonneg_left hq.1 (by norm_num))
          (mul_le_mul_of_nonneg_left htms (by norm_num))
      _ ≤ _ := by
        have hKn : 0 ≤ K / (2 * m : ℝ) := div_nonneg hK hnpos.le
        ring_nf at hKn ⊢
        linarith only [hKn]
  have hJnorm0 := J_norm_le (show 0 < 2 * m by omega) q
  have hJnorm := pow_le_pow_left₀ (norm_nonneg _) hJnorm0 2
  have hpadd := norm_add_le (J q) (tangent (by omega) h)
  change ‖p‖ ≤ ‖J q‖ + ‖tangent (by omega) h‖ at hpadd
  have hpnorm : ‖p‖ ^ 2 ≤ 1600000 * K + 16 * (2 * m : ℝ) ^ 2 * A := by
    have hqnorm := hq.2
    ring_nf at hJnorm hqnorm htnorm ⊢
    nlinarith only [norm_nonneg p, norm_nonneg (J q),
      norm_nonneg (tangent (by omega) h), hpadd, hJnorm, hqnorm, htnorm,
      sq_nonneg (‖J q‖ - ‖tangent (by omega) h‖)]
  have hrotms := rotated_meanSquare_bounds (show 0 < 2 * m by omega)
    (angleAverage (by omega) θ) q p
  have hrotnorm := rotated_norm_sq_bounds (angleAverage (by omega) θ) q p
  have hUdef : firstRadial (by omega) w θ η v h =
      fun j => r (q j) (p j) (angleAverage (by omega) θ j) := by
    funext j
    rfl
  have hTdef : firstTangential (by omega) w θ η v h =
      fun j => s (q j) (p j) (angleAverage (by omega) θ j) := by
    funext j
    rfl
  rw [← hUdef] at hrotms hrotnorm
  rw [← hTdef] at hrotms hrotnorm
  have hUms : meanSquare (firstRadial (by omega) w θ η v h) ≤
      1600000 * K / (2 * m : ℝ) + 32 * (2 * m : ℝ) * A := by
    calc
      _ ≤ 2 * meanSquare q + 2 * meanSquare p := hrotms.1
      _ ≤ 2 * (80000 * K / (2 * m : ℝ)) +
          2 * (700000 * K / (2 * m : ℝ) + 16 * (2 * m : ℝ) * A) :=
        add_le_add (mul_le_mul_of_nonneg_left hq.1 (by norm_num))
          (mul_le_mul_of_nonneg_left hpms (by norm_num))
      _ ≤ _ := by
        have hKn : 0 ≤ K / (2 * m : ℝ) := div_nonneg hK hnpos.le
        ring_nf at hKn ⊢
        linarith only [hKn]
  have hTms : meanSquare (firstTangential (by omega) w θ η v h) ≤
      1600000 * K / (2 * m : ℝ) + 32 * (2 * m : ℝ) * A := by
    calc
      _ ≤ 2 * meanSquare q + 2 * meanSquare p := hrotms.2
      _ ≤ 2 * (80000 * K / (2 * m : ℝ)) +
          2 * (700000 * K / (2 * m : ℝ) + 16 * (2 * m : ℝ) * A) :=
        add_le_add (mul_le_mul_of_nonneg_left hq.1 (by norm_num))
          (mul_le_mul_of_nonneg_left hpms (by norm_num))
      _ ≤ _ := by
        have hKn : 0 ≤ K / (2 * m : ℝ) := div_nonneg hK hnpos.le
        ring_nf at hKn ⊢
        linarith only [hKn]
  have hUnorm : ‖firstRadial (by omega) w θ η v h‖ ^ 2 ≤
      3600000 * K + 32 * (2 * m : ℝ) ^ 2 * A := by
    nlinarith only [hrotnorm.1, hq.2, hpnorm]
  have hTnorm : ‖firstTangential (by omega) w θ η v h‖ ^ 2 ≤
      3600000 * K + 32 * (2 * m : ℝ) ^ 2 * A := by
    nlinarith only [hrotnorm.2, hq.2, hpnorm]
  let u : Fin (2 * m) → ℝ := angleAverage (by omega) η
  let ru : Fin (2 * m) → ℝ := fun j => baseRadial (by omega) w θ v j * u j
  have hu := angleAverage_meanSquare_le (show 2 ≤ 2 * m by omega) η hd.2.1
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hu
  change meanSquare u ≤ 4 * E / (2 * m : ℝ) ^ 2 at hu
  have hru : meanSquare ru ≤ (25 / 4 : ℝ) * meanSquare u := by
    have hh := meanSquare_domination ru u (K := (5 / 2 : ℝ)) (by norm_num) (fun j => by
      dsimp [ru]
      rw [abs_mul]
      have hrj := hrad hm w θ v hdom j
      change |baseRadial (by omega) w θ v j| ≤ (5 / 2 : ℝ) at hrj
      exact mul_le_mul_of_nonneg_right hrj (abs_nonneg _))
    norm_num at hh ⊢
    exact hh
  have hvms0 := meanSquare_add_le
    (firstTangential (by omega) w θ η v h) (-ru)
  have hneg : meanSquare (-ru) = meanSquare ru := by unfold meanSquare; simp
  rw [hneg] at hvms0
  change meanSquare (rotationVelocity (by omega) w θ η v h) ≤
      2 * meanSquare (firstTangential (by omega) w θ η v h) +
        2 * meanSquare ru at hvms0
  have hEn : E / (2 * m : ℝ) ^ 2 ≤ K / (2 * m : ℝ) := by
    have hEK : E ≤ K := by dsimp [K]; linarith
    calc
      _ ≤ K / (2 * m : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hEK (sq_nonneg _)
      _ ≤ K / (2 * m : ℝ) := by
        apply div_le_div_of_nonneg_left hK hnpos
        nlinarith only [hn]
  have hvms : meanSquare (rotationVelocity (by omega) w θ η v h) ≤
      3300000 * K / (2 * m : ℝ) + 64 * (2 * m : ℝ) * A := by
    calc
      _ ≤ 2 * meanSquare (firstTangential (by omega) w θ η v h) +
          2 * meanSquare ru := hvms0
      _ ≤ 2 * (1600000 * K / (2 * m : ℝ) + 32 * (2 * m : ℝ) * A) +
          2 * ((25 / 4 : ℝ) * (4 * E / (2 * m : ℝ) ^ 2)) :=
        add_le_add (mul_le_mul_of_nonneg_left hTms (by norm_num))
          (mul_le_mul_of_nonneg_left
            ((hru.trans (mul_le_mul_of_nonneg_left hu (by norm_num))))
            (by norm_num))
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hEn (show (0 : ℝ) ≤ 50 by norm_num)
        have hKn : 0 ≤ K / (2 * m : ℝ) := div_nonneg hK hnpos.le
        ring_nf at hh hKn ⊢
        linarith only [hh, hKn]
  have hulog := angleAverage_pointwise_sq_le (show 2 ≤ 2 * m by omega) η hd.2.1
  have hlog0 : 0 ≤ Real.log (2 * m : ℝ) :=
    Real.log_nonneg hn
  have hrunorm : ‖ru‖ ^ 2 ≤
      75 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 * E := by
    apply norm_sq_le_of_pointwise _ (by positivity)
    intro j
    have hrj := hrad hm w θ v hdom j
    change |baseRadial (by omega) w θ v j| ≤ (5 / 2 : ℝ) at hrj
    have hrsq := pow_le_pow_left₀ (abs_nonneg _) hrj 2
    rw [sq_abs] at hrsq
    norm_num at hrsq
    dsimp [ru, u]
    have huj := hulog j
    simp only [Nat.cast_mul, Nat.cast_ofNat] at huj
    change angleAverage (by omega) η j ^ 2 ≤
      12 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 * E at huj
    calc
      (baseRadial (by omega) w θ v j * angleAverage (by omega) η j) ^ 2 =
          baseRadial (by omega) w θ v j ^ 2 *
            angleAverage (by omega) η j ^ 2 := by ring
      _ ≤ (25 / 4 : ℝ) *
          (12 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 * E) :=
        mul_le_mul hrsq huj (sq_nonneg _) (by positivity)
      _ = 75 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 * E := by ring
  have hlog : Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 ≤ 1 := by
    have hl := Real.log_le_sub_one_of_pos hnpos
    apply (div_le_iff₀ (sq_pos_of_pos hnpos)).2
    nlinarith
  have hrunorm' : ‖ru‖ ^ 2 ≤ 75 * K := by
    have hEK : E ≤ K := by dsimp [K]; linarith
    have hratioE :
        Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 * E ≤ E := by
      exact mul_le_of_le_one_left hE hlog
    calc
      _ ≤ 75 * (Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 * E) := by
        (convert hrunorm using 1; ring)
      _ ≤ 75 * E := mul_le_mul_of_nonneg_left hratioE (by norm_num)
      _ ≤ 75 * K := mul_le_mul_of_nonneg_left hEK (by norm_num)
  have hvadd := norm_add_le (firstTangential (by omega) w θ η v h) (-ru)
  have hvEq : rotationVelocity (by omega) w θ η v h =
      firstTangential (by omega) w θ η v h + (-ru) := by
    funext j
    rfl
  rw [← hvEq] at hvadd
  rw [norm_neg] at hvadd
  have hvnorm : ‖rotationVelocity (by omega) w θ η v h‖ ^ 2 ≤
      7200200 * K + 64 * (2 * m : ℝ) ^ 2 * A := by
    have hsquare := pow_le_pow_left₀
      (norm_nonneg (rotationVelocity (by omega) w θ η v h)) hvadd 2
    have hsum :
        (‖firstTangential (by omega) w θ η v h‖ + ‖ru‖) ^ 2 ≤
          2 * ‖firstTangential (by omega) w θ η v h‖ ^ 2 +
            2 * ‖ru‖ ^ 2 := by
      nlinarith only [sq_nonneg
        (‖firstTangential (by omega) w θ η v h‖ - ‖ru‖)]
    calc
      _ ≤ (‖firstTangential (by omega) w θ η v h‖ + ‖ru‖) ^ 2 := hsquare
      _ ≤ 2 * ‖firstTangential (by omega) w θ η v h‖ ^ 2 +
          2 * ‖ru‖ ^ 2 := hsum
      _ ≤ 2 * (3600000 * K + 32 * (2 * m : ℝ) ^ 2 * A) +
          2 * (75 * K) :=
        add_le_add (mul_le_mul_of_nonneg_left hTnorm (by norm_num))
          (mul_le_mul_of_nonneg_left hrunorm' (by norm_num))
      _ ≤ _ := by linarith only [hK]
  exact ⟨hq.1, hq.2, hpms, hpnorm, hUms, hUnorm, hTms, hTnorm, hvms, hvnorm⟩

end
end StructuralNote.FixedSchurChosenSecondMoments
