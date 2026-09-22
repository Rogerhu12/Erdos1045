import StructuralNote.ExplicitFixedSchurCoefficients
import StructuralNote.ExplicitCanonicalEntryObjectivePaths

/-! Explicit second-moment estimates for the fixed-Schur chosen chart. -/

namespace StructuralNote.ExplicitFixedSchurSecondMoments

open Filter Complex Erdos1045.EventualExact FiniteBox SchurSpectrum SchurLiftBounds
open CommonClosureEnergy CommonDomainClosure CommonDomainRadius CommonFiberBounds
open CommonTangentialParameters CommonFiberNormalAverage
open CommonFiberCanonicalDirections CommonFiberNormalProjectionScaled EdgeCoordinates
open FixedSchurData FixedSchurChart FixedSchurDomainBounds FixedSchurHarmonicBounds
open FixedSchurNormalExpansion FixedSchurRotatedPath
open FixedSchurRotatedCoefficients FixedSchurFirstSource
open FixedSchurRotatedInverse
open FixedSchurFirstSourceSup FixedSchurDerivativeScales
open FixedSchurSecondSourceTools FixedSchurChosenPath
open FixedSchurChosenLinearization FixedSchurQuadraticExpansion
open FixedSchurNormalInnerEnergy FixedSchurDirectionMoments
open ExplicitHessianThreshold ExplicitFixedSchurCoefficients
open ExplicitCanonicalEntryObjectivePaths
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
theorem chosen_first_moments_of_linearization {m : ℕ}
    (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m)
    (hm : 2 ≤ m) (w : SignPattern (by omega))
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (hdom : InDomain (by omega) θ v) (hd : Admissible (by omega) (η, h))
    (hlin : normalLinearization (by omega) w θ v
      (chosenFirstDerivative (by omega) w θ η v h) =
        source (by omega) w θ η v h) :
    let E := pairEnergy (by omega) (fun j => (η j : ℂ))
    let A := pairEnergy (by omega) h
    let K := E + A
    let q := chosenFirstDerivative (by omega) w θ η v h
    let p := firstP (by omega) w θ η v h
    meanSquare q ≤ 80000 * K / (2 * m : ℝ) ∧
    ‖q‖ ^ 2 ≤ 200000 * K ∧
    meanSquare p ≤ 700000 * K / (2 * m : ℝ) + 16 * (2 * m : ℝ) * A ∧
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
  have hcoarse := first_solution_coarse hN
  have hrad := radialCoefficient_bound hN
  clear hN
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
  have hq := hcoarse hm w θ η v h hdom hd.2.1 q hlin
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
private theorem sign_abs {m : ℕ} (hm : 0 < m) (w : SignPattern hm)
    (j : Fin (2 * m)) : |patternSign w j| = 1 := by
  rcases patternSign_is_sign w j with h | h <;> rw [h] <;> norm_num

theorem second_coefficient_bounds {m : ℕ}
    (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m)
    (hm : 2 ≤ m) (w : SignPattern (by omega))
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (hdom : InDomain (by omega) θ v) (j : Fin (2 * m)) :
    let S := rotatedS (by omega) θ v (coordinate (by omega) w θ v) j
    let HH := H (epsilon (2 * m)) S
    |patternSign w j / (2 * epsilon (2 * m)) *
        Real.cos (Real.pi / (2 * m : ℝ) + angleDifference (by omega) θ j / 2)| ≤
        (2 * m : ℝ) ^ 2 / 8 ∧
    |baseRadial (by omega) w θ v j| ≤ (5 / 2 : ℝ) ∧
    |S| ≤ 18 * (logOrder (2 * m) : ℝ) ∧
    1 ≤ HH ∧
    |patternSign w j * epsilon (2 * m) * S / HH| ≤ 1 ∧
    |4 * patternSign w j * epsilon (2 * m) / HH ^ 3| ≤
      32 / (2 * m : ℝ) ^ 2 := by
  have hcoeff := actual_coefficients_small hN
  have hcoord := ExplicitHessianThresholdFixedSchur.coordinate_properties hN
  have hrad := radialCoefficient_bound hN
  have horder := ExplicitHessianThreshold.order_bound hN
  clear hN
  dsimp only
  let S := rotatedS (by omega) θ v (coordinate (by omega) w θ v) j
  let HH := H (epsilon (2 * m)) S
  have hn : (0 : ℝ) < 2 * m := by positivity
  have hε : 0 < epsilon (2 * m) := epsilon_pos (show 2 ≤ 2 * m by omega)
  have hεle := epsilon_le (show 2 ≤ 2 * m by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hεle
  have hscale := (scale_bounds (show 2 ≤ 2 * m by omega)).2
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hscale
  have hq := (hcoord hm w θ v hdom).norm_le
  have hS : |S| ≤ 18 * (logOrder (2 * m) : ℝ) :=
    rotatedS_abs_le_log (by omega) θ v hdom _ hq j
  have hH : 1 ≤ HH := (hcoeff hm w θ v hdom j).2.2
  have hHpos : 0 < HH := lt_of_lt_of_le (by norm_num) hH
  have hsign := sign_abs (by omega) w j
  have hL : 144 * (logOrder (2 * m) : ℝ) ≤ (2 * m : ℝ) ^ 2 := by
    have ho : 10 * (logOrder (2 * m) : ℝ) + 1024 ≤ 2 * m := by
      exact_mod_cast horder
    have hL0 : 0 ≤ (logOrder (2 * m) : ℝ) := by positivity
    have hLm : 144 * (logOrder (2 * m) : ℝ) ≤ 15 * (2 * m : ℝ) := by
      nlinarith only [ho, hL0]
    have hmlarge : (15 : ℝ) ≤ 2 * m := by linarith
    nlinarith
  have hεS : |epsilon (2 * m) * S| ≤ 1 := by
    rw [abs_mul, abs_of_pos hε]
    calc
      epsilon (2 * m) * |S| ≤
          (8 / (2 * m : ℝ) ^ 2) *
            (18 * (logOrder (2 * m) : ℝ)) :=
        mul_le_mul hεle hS (abs_nonneg _) (by positivity)
      _ = 144 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2 := by ring
      _ ≤ 1 := (div_le_one (sq_pos_of_pos hn)).2 hL
  have hfirst : |patternSign w j / (2 * epsilon (2 * m)) *
        Real.cos (Real.pi / (2 * m : ℝ) + angleDifference (by omega) θ j / 2)| ≤
      (2 * m : ℝ) ^ 2 / 8 := by
    have hden : |patternSign w j / (2 * epsilon (2 * m))| =
        scale (2 * m) / 2 := by
      rw [abs_div, hsign, abs_mul, abs_of_pos hε]
      norm_num
      rw [epsilon_inv (show 2 ≤ 2 * m by omega)]
      ring
    rw [abs_mul, hden]
    calc
      (scale (2 * m) / 2) *
          |Real.cos (Real.pi / (2 * m : ℝ) + angleDifference (by omega) θ j / 2)| ≤
          (((2 * m : ℝ) ^ 2 / 4) / 2) * 1 :=
        mul_le_mul (div_le_div_of_nonneg_right hscale (by norm_num))
          (Real.abs_cos_le_one _) (abs_nonneg _) (by positivity)
      _ = (2 * m : ℝ) ^ 2 / 8 := by ring
  have hmiddle : |patternSign w j * epsilon (2 * m) * S / HH| ≤ 1 := by
    rw [abs_div, abs_mul, abs_mul, hsign, one_mul, abs_of_pos hε,
      abs_of_pos hHpos]
    have hnum : epsilon (2 * m) * |S| ≤ 1 := by
      simpa only [abs_mul, abs_of_pos hε] using hεS
    calc
      epsilon (2 * m) * |S| / HH ≤ epsilon (2 * m) * |S| :=
        div_le_self (mul_nonneg hε.le (abs_nonneg _)) hH
      _ ≤ 1 := hnum
  have hlast : |4 * patternSign w j * epsilon (2 * m) / HH ^ 3| ≤
      32 / (2 * m : ℝ) ^ 2 := by
    rw [abs_div, abs_mul, abs_mul, hsign, abs_of_pos hε,
      abs_of_pos (pow_pos hHpos 3)]
    norm_num
    calc
      4 * epsilon (2 * m) / HH ^ 3 ≤ 4 * epsilon (2 * m) :=
        div_le_self (by positivity) (by exact one_le_pow₀ hH)
      _ ≤ 4 * (8 / (2 * m : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hεle (by norm_num)
      _ = 32 / (2 * m : ℝ) ^ 2 := by ring
  exact ⟨hfirst, hrad hm w θ v hdom j, hS, hH, hmiddle, hlast⟩
private theorem mixed_sqrt_bound (N E A K x y : ℝ)
    (hN : 1 ≤ N) (hE : 0 ≤ E) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hEK : E ≤ K) (_hAK : A ≤ K) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxb : x ≤ 1600000 * K / N + 32 * N * A)
    (hyb : y ≤ 4 * E / N ^ 2) :
    Real.sqrt x * Real.sqrt y ≤
      3000 * K / N + 12 * Real.sqrt (A * E) / Real.sqrt N := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hrootN : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hsN : Real.sqrt N ^ 2 = N := Real.sq_sqrt hNpos.le
  have hAE : 0 ≤ A * E := mul_nonneg hA hE
  have hsAE : Real.sqrt (A * E) ^ 2 = A * E := Real.sq_sqrt hAE
  have hsx : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have hsy : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
  have hxb0 : 0 ≤ 1600000 * K / N + 32 * N * A := by positivity
  have hxy := mul_le_mul hxb hyb hy hxb0
  have hxy' : x * y ≤
      6400000 * K ^ 2 / N ^ 3 + 128 * A * E / N := by
    calc
      x * y ≤ (1600000 * K / N + 32 * N * A) * (4 * E / N ^ 2) := hxy
      _ ≤ 6400000 * K ^ 2 / N ^ 3 + 128 * A * E / N := by
        have hKE : K * E ≤ K ^ 2 :=
          by simpa only [pow_two] using mul_le_mul_of_nonneg_left hEK hK
        have hN2 : 1 ≤ N ^ 2 := by nlinarith
        field_simp [ne_of_gt hNpos]
        nlinarith only [hKE, hN2, hA, hE]
  have htarget :
      6400000 * K ^ 2 / N ^ 3 + 128 * A * E / N ≤
        (3000 * K / N + 12 * Real.sqrt (A * E) / Real.sqrt N) ^ 2 := by
    field_simp [ne_of_gt hNpos, ne_of_gt hrootN]
    ring_nf
    rw [hsN, hsAE]
    have hN2 : N ≤ N ^ 2 := by nlinarith
    have hK2 : 0 ≤ K ^ 2 := sq_nonneg K
    have hKN : K ^ 2 * N ≤ K ^ 2 * N ^ 2 :=
      mul_le_mul_of_nonneg_left hN2 hK2
    have hAEN : 0 ≤ A * E * N ^ 3 := by positivity
    have hcross : 0 ≤ K * N ^ 2 * Real.sqrt N * Real.sqrt (A * E) := by positivity
    nlinarith only [hKN, hAEN, hcross]
  have hsquare :
      (Real.sqrt x * Real.sqrt y) ^ 2 ≤
        (3000 * K / N + 12 * Real.sqrt (A * E) / Real.sqrt N) ^ 2 := by
    rw [mul_pow, hsx, hsy]
    exact hxy'.trans htarget
  have hleft : 0 ≤ Real.sqrt x * Real.sqrt y := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hright : 0 ≤ 3000 * K / N +
      12 * Real.sqrt (A * E) / Real.sqrt N := by positivity
  exact (sq_le_sq₀ hleft hright).mp hsquare
set_option maxHeartbeats 800000 in
theorem second_source_l1_of_linearization {m : ℕ}
    (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m)
    (hm : 2 ≤ m) (w : SignPattern (by omega))
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (hdom : InDomain (by omega) θ v) (hd : Admissible (by omega) (η, h))
    (hlin : normalLinearization (by omega) w θ v
      (chosenFirstDerivative (by omega) w θ η v h) =
        source (by omega) w θ η v h) :
    let E := pairEnergy (by omega) (fun j => (η j : ℂ))
    let A := pairEnergy (by omega) h
    let K := E + A
    (∑ j, |secondSource (by omega) w θ η v h j|) / (2 * m : ℝ) ≤
      120000000 *
        (K / (2 * m : ℝ) + Real.sqrt (A * E) / Real.sqrt (2 * m : ℝ)) := by
  have hcoef := second_coefficient_bounds hN
  have hmom := chosen_first_moments_of_linearization hN hm w θ η v h hdom hd hlin
  have horder := ExplicitHessianThreshold.order_bound hN
  clear hN hlin
  dsimp only
  let N : ℝ := 2 * m
  let E := pairEnergy (by omega) (fun j => (η j : ℂ))
  let A := pairEnergy (by omega) h
  let K := E + A
  let d := angleDifference (by omega) η
  let u := angleAverage (by omega) η
  let U := firstRadial (by omega) w θ η v h
  let T := firstTangential (by omega) w θ η v h
  let V := rotationVelocity (by omega) w θ η v h
  have hN : 1 ≤ N := by dsimp [N]; exact_mod_cast (show 1 ≤ 2 * m by omega)
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hE : 0 ≤ E := by dsimp [E]; exact pairEnergy_nonneg (by omega) _
  have hA : 0 ≤ A := by dsimp [A]; exact pairEnergy_nonneg (by omega) _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hEK : E ≤ K := by dsimp [K]; linarith
  have hAK : A ≤ K := by dsimp [K]; linarith
  rcases hmom with
    ⟨_hqms, _hqnorm, _hpms, _hpnorm, hUms, _hUnorm,
      hTms, _hTnorm, hVms, _hVnorm⟩
  change meanSquare U ≤ 1600000 * K / N + 32 * N * A at hUms
  change meanSquare T ≤ 1600000 * K / N + 32 * N * A at hTms
  change meanSquare V ≤ 3300000 * K / N + 64 * N * A at hVms
  have hdms := angleDifference_meanSquare_le (show 0 < 2 * m by omega) η
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hdms
  change meanSquare d ≤ 8 * Real.pi ^ 2 * E / N ^ 3 at hdms
  have hums := angleAverage_meanSquare_le (show 2 ≤ 2 * m by omega) η hd.2.1
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hums
  change meanSquare u ≤ 4 * E / N ^ 2 at hums
  have hpi : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hdms' : meanSquare d ≤ 128 * E / N ^ 3 := by
    calc
      _ ≤ 8 * Real.pi ^ 2 * E / N ^ 3 := hdms
      _ ≤ 128 * E / N ^ 3 := by
        apply div_le_div_of_nonneg_right _ (pow_nonneg hNpos.le 3)
        have hh := mul_le_mul_of_nonneg_right hpi hE
        nlinarith only [hh]
  have hTmix : Real.sqrt (meanSquare T) * Real.sqrt (meanSquare u) ≤
      3000 * K / N + 12 * Real.sqrt (A * E) / Real.sqrt N :=
    mixed_sqrt_bound N E A K _ _ hN hE hA hK hEK hAK
      (by unfold meanSquare; positivity)
      (by unfold meanSquare; positivity) hTms hums
  have hUmix : Real.sqrt (meanSquare U) * Real.sqrt (meanSquare u) ≤
      3000 * K / N + 12 * Real.sqrt (A * E) / Real.sqrt N :=
    mixed_sqrt_bound N E A K _ _ hN hE hA hK hEK hAK
      (by unfold meanSquare; positivity)
      (by unfold meanSquare; positivity) hUms hums
  have hL : (logOrder (2 * m) : ℝ) ≤ N := by
    have hL0 : 0 ≤ (logOrder (2 * m) : ℝ) := by positivity
    have horder' : 10 * (logOrder (2 * m) : ℝ) + 1024 ≤ N := by
      simpa only [N, Nat.cast_mul, Nat.cast_ofNat] using horder
    linarith only [horder', hL0]
  have hpoint (j : Fin (2 * m)) :
      |secondSource (by omega) w θ η v h j| ≤
        N ^ 2 / 8 * d j ^ 2 + 2 * |T j * u j| +
        (5 / 2 : ℝ) * u j ^ 2 +
        (2 * |U j * u j| + 18 * (logOrder (2 * m) : ℝ) * u j ^ 2) +
        32 / N ^ 2 * V j ^ 2 := by
    rcases hcoef hm w θ v hdom j with ⟨hc, hr, hS, _hH, hmid, hlast⟩
    let S := rotatedS (by omega) θ v (coordinate (by omega) w θ v) j
    let c := patternSign w j / (2 * epsilon (2 * m)) *
      Real.cos (Real.pi / (2 * m : ℝ) + angleDifference (by omega) θ j / 2)
    have h1 : |c * d j ^ 2| ≤ N ^ 2 / 8 * d j ^ 2 := by
      simp only [abs_mul, abs_pow, sq_abs]
      exact mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    have h2 : |2 * T j * u j| ≤ 2 * |T j * u j| := by
      rw [show 2 * T j * u j = 2 * (T j * u j) by ring, abs_mul]
      norm_num
    have h3 : |baseRadial (by omega) w θ v j * u j ^ 2| ≤
        (5 / 2 : ℝ) * u j ^ 2 := by
      simp only [abs_mul, abs_pow, sq_abs]
      exact mul_le_mul_of_nonneg_right hr (sq_nonneg _)
    have h4 : |patternSign w j * epsilon (2 * m) * S /
          H (epsilon (2 * m)) S * (2 * U j * u j + S * u j ^ 2)| ≤
        2 * |U j * u j| + 18 * (logOrder (2 * m) : ℝ) * u j ^ 2 := by
      rw [abs_mul]
      calc
        _ ≤ 1 * |2 * U j * u j + S * u j ^ 2| :=
          mul_le_mul hmid le_rfl (abs_nonneg _) (by norm_num)
        _ ≤ 1 * (|2 * U j * u j| + |S * u j ^ 2|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
        _ ≤ 2 * |U j * u j| +
            18 * (logOrder (2 * m) : ℝ) * u j ^ 2 := by
          simp only [abs_mul, abs_pow, sq_abs]
          norm_num
          have hsPart := mul_le_mul_of_nonneg_right hS (sq_nonneg (u j))
          nlinarith only [hsPart]
    have h5 : |4 * patternSign w j * epsilon (2 * m) /
          H (epsilon (2 * m)) S ^ 3 * V j ^ 2| ≤
        32 / N ^ 2 * V j ^ 2 := by
      simp only [abs_mul, abs_pow, sq_abs]
      exact mul_le_mul_of_nonneg_right hlast (sq_nonneg _)
    change |c * d j ^ 2 - 2 * T j * u j +
        baseRadial (by omega) w θ v j * u j ^ 2 +
        patternSign w j * epsilon (2 * m) * S / H (epsilon (2 * m)) S *
          (2 * U j * u j + S * u j ^ 2) -
        4 * patternSign w j * epsilon (2 * m) / H (epsilon (2 * m)) S ^ 3 * V j ^ 2| ≤ _
    have ha := abs_sub (c * d j ^ 2 - 2 * T j * u j +
      baseRadial (by omega) w θ v j * u j ^ 2 +
      patternSign w j * epsilon (2 * m) * S / H (epsilon (2 * m)) S *
        (2 * U j * u j + S * u j ^ 2))
      (4 * patternSign w j * epsilon (2 * m) / H (epsilon (2 * m)) S ^ 3 * V j ^ 2)
    have hb := abs_add_le (c * d j ^ 2 - 2 * T j * u j +
      baseRadial (by omega) w θ v j * u j ^ 2)
      (patternSign w j * epsilon (2 * m) * S / H (epsilon (2 * m)) S *
        (2 * U j * u j + S * u j ^ 2))
    have hc' := abs_add_le (c * d j ^ 2 - 2 * T j * u j)
      (baseRadial (by omega) w θ v j * u j ^ 2)
    have hd' := abs_sub (c * d j ^ 2) (2 * T j * u j)
    linarith only [ha, hb, hc', hd', h1, h2, h3, h4, h5]
  have hraw : (∑ j, |secondSource (by omega) w θ η v h j|) / N ≤
      N ^ 2 / 8 * meanSquare d +
      2 * ((∑ j, |T j * u j|) / N) +
      (5 / 2 : ℝ) * meanSquare u +
      (2 * ((∑ j, |U j * u j|) / N) +
        18 * (logOrder (2 * m) : ℝ) * meanSquare u) +
      32 / N ^ 2 * meanSquare V := by
    have havg := average_mono hpoint
    simp only [average_add, average_mul] at havg
    unfold average at havg
    simpa only [meanSquare, N, Nat.cast_mul, Nat.cast_ofNat] using havg
  have hTl1 : (∑ j, |T j * u j|) / N ≤
      Real.sqrt (meanSquare T) * Real.sqrt (meanSquare u) := by
    simpa only [N, Nat.cast_mul, Nat.cast_ofNat] using normalized_product_l1 T u
  have hUl1 : (∑ j, |U j * u j|) / N ≤
      Real.sqrt (meanSquare U) * Real.sqrt (meanSquare u) := by
    simpa only [N, Nat.cast_mul, Nat.cast_ofNat] using normalized_product_l1 U u
  have hVterm : 32 / N ^ 2 * meanSquare V ≤ 108000000 * K / N := by
    calc
      _ ≤ 32 / N ^ 2 * (3300000 * K / N + 64 * N * A) :=
        mul_le_mul_of_nonneg_left hVms (by positivity)
      _ ≤ 108000000 * K / N := by
        field_simp [ne_of_gt hNpos]
        have hN2 : 1 ≤ N ^ 2 := by nlinarith
        have hKN : K ≤ K * N ^ 2 := by nlinarith
        have hAN : A * N ^ 2 ≤ K * N ^ 2 :=
          mul_le_mul_of_nonneg_right hAK (sq_nonneg N)
        nlinarith only [hKN, hAN, hK]
  calc
    _ ≤ N ^ 2 / 8 * meanSquare d +
        2 * ((∑ j, |T j * u j|) / N) +
        (5 / 2 : ℝ) * meanSquare u +
        (2 * ((∑ j, |U j * u j|) / N) +
          18 * (logOrder (2 * m) : ℝ) * meanSquare u) +
        32 / N ^ 2 * meanSquare V := hraw
    _ ≤ N ^ 2 / 8 * (128 * E / N ^ 3) +
        2 * (3000 * K / N + 12 * Real.sqrt (A * E) / Real.sqrt N) +
        (5 / 2 : ℝ) * (4 * E / N ^ 2) +
        (2 * (3000 * K / N + 12 * Real.sqrt (A * E) / Real.sqrt N) +
          18 * (logOrder (2 * m) : ℝ) * (4 * E / N ^ 2)) +
        108000000 * K / N := by
      have hdB := mul_le_mul_of_nonneg_left hdms' (show 0 ≤ N ^ 2 / 8 by positivity)
      have hTB := mul_le_mul_of_nonneg_left (hTl1.trans hTmix) (by norm_num : (0 : ℝ) ≤ 2)
      have huB := mul_le_mul_of_nonneg_left hums (by norm_num : (0 : ℝ) ≤ 5 / 2)
      have hUB := mul_le_mul_of_nonneg_left (hUl1.trans hUmix) (by norm_num : (0 : ℝ) ≤ 2)
      have hL0 : 0 ≤ (logOrder (2 * m) : ℝ) := Nat.cast_nonneg _
      have hLcoef : 0 ≤ 18 * (logOrder (2 * m) : ℝ) :=
        mul_nonneg (by norm_num) hL0
      have hLuB := mul_le_mul_of_nonneg_left hums hLcoef
      linarith only [hdB, hTB, huB, hUB, hLuB, hVterm]
    _ ≤ 120000000 *
        (K / N + Real.sqrt (A * E) / Real.sqrt N) := by
      have hroot : 0 ≤ Real.sqrt (A * E) / Real.sqrt N := by positivity
      have hE1 : E / N ^ 2 ≤ K / N := by
        calc
          _ ≤ K / N ^ 2 := div_le_div_of_nonneg_right hEK (sq_nonneg _)
          _ ≤ K / N := by
            apply div_le_div_of_nonneg_left hK hNpos
            nlinarith
      have hEN : E / N ≤ K / N := div_le_div_of_nonneg_right hEK hNpos.le
      have hLN : (logOrder (2 * m) : ℝ) * E / N ^ 2 ≤ K / N := by
        have hLE := mul_le_mul hL hEK hE hNpos.le
        calc
          _ ≤ N * K / N ^ 2 := div_le_div_of_nonneg_right hLE (sq_nonneg _)
          _ = K / N := by field_simp [ne_of_gt hNpos]
      calc
        _ = 108012000 * K / N + 16 * E / N + 10 * E / N ^ 2 +
            72 * ((logOrder (2 * m) : ℝ) * E / N ^ 2) +
            48 * (Real.sqrt (A * E) / Real.sqrt N) := by
          field_simp [ne_of_gt hNpos]
          ring
        _ ≤ 108012098 * K / N +
            48 * (Real.sqrt (A * E) / Real.sqrt N) := by
          have h1 := mul_le_mul_of_nonneg_left hEN (by norm_num : (0 : ℝ) ≤ 16)
          have h2 := mul_le_mul_of_nonneg_left hE1 (by norm_num : (0 : ℝ) ≤ 10)
          have h3 := mul_le_mul_of_nonneg_left hLN (by norm_num : (0 : ℝ) ≤ 72)
          have hrest : 16 * (E / N) + 10 * (E / N ^ 2) +
              72 * ((logOrder (2 * m) : ℝ) * E / N ^ 2) ≤
              98 * (K / N) := by
            calc
              _ ≤ 16 * (K / N) + 10 * (K / N) + 72 * (K / N) :=
                add_le_add (add_le_add h1 h2) h3
              _ = 98 * (K / N) := by ring
          calc
            _ = 108012000 * (K / N) +
                (16 * (E / N) + 10 * (E / N ^ 2) +
                  72 * ((logOrder (2 * m) : ℝ) * E / N ^ 2)) +
                48 * (Real.sqrt (A * E) / Real.sqrt N) := by ring
            _ ≤ 108012000 * (K / N) + 98 * (K / N) +
                48 * (Real.sqrt (A * E) / Real.sqrt N) := by
              gcongr
            _ = _ := by ring

        _ ≤ 120000000 *
            (K / N + Real.sqrt (A * E) / Real.sqrt N) := by
          have hKN : 0 ≤ K / N := div_nonneg hK hNpos.le
          have h1 : 108012098 * (K / N) ≤ 120000000 * (K / N) :=
            mul_le_mul_of_nonneg_right (by norm_num) hKN
          have h2 : 48 * (Real.sqrt (A * E) / Real.sqrt N) ≤
              120000000 * (Real.sqrt (A * E) / Real.sqrt N) :=
            mul_le_mul_of_nonneg_right (by norm_num) hroot
          calc
            _ = 108012098 * (K / N) +
                48 * (Real.sqrt (A * E) / Real.sqrt N) := by ring
            _ ≤ 120000000 * (K / N) +
                120000000 * (Real.sqrt (A * E) / Real.sqrt N) := add_le_add h1 h2
            _ = _ := by ring



private theorem meanSquare_five_add_le {n : ℕ}
    (f₁ f₂ f₃ f₄ f₅ : Fin n → ℝ) :
    meanSquare (fun j => (((f₁ j + f₂ j) + f₃ j) + f₄ j) + f₅ j) ≤
      16 * (meanSquare f₁ + meanSquare f₂ + meanSquare f₃ +
        meanSquare f₄ + meanSquare f₅) := by
  have h₁₂ := meanSquare_add_le f₁ f₂
  have h₁₂₃ := meanSquare_add_le (fun j => f₁ j + f₂ j) f₃
  have h₁₂₃₄ := meanSquare_add_le (fun j => (f₁ j + f₂ j) + f₃ j) f₄
  have h₁₂₃₄₅ := meanSquare_add_le
    (fun j => ((f₁ j + f₂ j) + f₃ j) + f₄ j) f₅
  change meanSquare (fun j => f₁ j + f₂ j) ≤
    2 * meanSquare f₁ + 2 * meanSquare f₂ at h₁₂
  change meanSquare (fun j => (f₁ j + f₂ j) + f₃ j) ≤
    2 * meanSquare (fun j => f₁ j + f₂ j) + 2 * meanSquare f₃ at h₁₂₃
  change meanSquare (fun j => ((f₁ j + f₂ j) + f₃ j) + f₄ j) ≤
    2 * meanSquare (fun j => (f₁ j + f₂ j) + f₃ j) +
      2 * meanSquare f₄ at h₁₂₃₄
  change meanSquare (fun j => (((f₁ j + f₂ j) + f₃ j) + f₄ j) + f₅ j) ≤
    2 * meanSquare (fun j => ((f₁ j + f₂ j) + f₃ j) + f₄ j) +
      2 * meanSquare f₅ at h₁₂₃₄₅
  have hnonneg (f : Fin n → ℝ) : 0 ≤ meanSquare f := by
    unfold meanSquare
    positivity
  linarith only [h₁₂, h₁₂₃, h₁₂₃₄, h₁₂₃₄₅,
    hnonneg f₁, hnonneg f₂, hnonneg f₃, hnonneg f₄, hnonneg f₅]
set_option maxHeartbeats 2000000 in
theorem second_source_meanSquare_of_linearization {m : ℕ}
    (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m)
    (hm : 2 ≤ m) (w : SignPattern (by omega))
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (hdom : InDomain (by omega) θ v) (hd : Admissible (by omega) (η, h))
    (hlin : normalLinearization (by omega) w θ v
      (chosenFirstDerivative (by omega) w θ η v h) = source (by omega) w θ η v h) :
    let E := pairEnergy (by omega) (fun j => (η j : ℂ))
    let A := pairEnergy (by omega) h
    let K := E + A
    meanSquare (secondSource (by omega) w θ η v h) ≤
      1000000000000000000 * (1 + Real.log (2 * m : ℝ)) * K ^ 2 /
        (2 * m : ℝ) := by
  have hcoef := second_coefficient_bounds hN
  have hmom := chosen_first_moments_of_linearization hN hm w θ η v h hdom hd hlin
  have horder := ExplicitHessianThreshold.order_bound hN
  clear hN hlin
  dsimp only
  let N : ℝ := 2 * m
  let E := pairEnergy (by omega) (fun j => (η j : ℂ))
  let A := pairEnergy (by omega) h
  let K := E + A
  let d := angleDifference (by omega) η
  let u := angleAverage (by omega) η
  let U := firstRadial (by omega) w θ η v h
  let T := firstTangential (by omega) w θ η v h
  let V := rotationVelocity (by omega) w θ η v h
  let ell := 1 + Real.log N
  have hN : 1 ≤ N := by dsimp [N]; exact_mod_cast (show 1 ≤ 2 * m by omega)
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  have hell : 1 ≤ ell := by dsimp [ell]; linarith
  have hE : 0 ≤ E := by dsimp [E]; exact pairEnergy_nonneg (by omega) _
  have hA : 0 ≤ A := by dsimp [A]; exact pairEnergy_nonneg (by omega) _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hEK : E ≤ K := by dsimp [K]; linarith
  have hAK : A ≤ K := by dsimp [K]; linarith
  rcases hmom with
    ⟨_hqms, _hqnorm, _hpms, _hpnorm, hUms, _hUnorm,
      hTms, _hTnorm, hVms, hVnorm⟩
  change meanSquare U ≤ 1600000 * K / N + 32 * N * A at hUms
  change meanSquare T ≤ 1600000 * K / N + 32 * N * A at hTms
  change meanSquare V ≤ 3300000 * K / N + 64 * N * A at hVms
  change ‖V‖ ^ 2 ≤ 7200200 * K + 64 * N ^ 2 * A at hVnorm
  have hKN : K / N ≤ N * K := by
    apply (div_le_iff₀ hNpos).2
    have hN2 : 1 ≤ N ^ 2 := by nlinarith
    nlinarith only [hN2, hK]
  have hUms' : meanSquare U ≤ 1600032 * N * K := by
    have h1 := mul_le_mul_of_nonneg_left hKN (by norm_num : (0 : ℝ) ≤ 1600000)
    have h1' : 1600000 * K / N ≤ 1600000 * (N * K) := by
      simpa only [mul_div_assoc] using h1
    have h2 := mul_le_mul_of_nonneg_left hAK
      (show 0 ≤ 32 * N by positivity)
    calc
      _ ≤ 1600000 * (N * K) + 32 * N * K := by
        exact hUms.trans (add_le_add h1' h2)
      _ = 1600032 * N * K := by ring
  have hTms' : meanSquare T ≤ 1600032 * N * K := by
    have h1 := mul_le_mul_of_nonneg_left hKN (by norm_num : (0 : ℝ) ≤ 1600000)
    have h1' : 1600000 * K / N ≤ 1600000 * (N * K) := by
      simpa only [mul_div_assoc] using h1
    have h2 := mul_le_mul_of_nonneg_left hAK
      (show 0 ≤ 32 * N by positivity)
    calc
      _ ≤ 1600000 * (N * K) + 32 * N * K := by
        exact hTms.trans (add_le_add h1' h2)
      _ = 1600032 * N * K := by ring
  have hVms' : meanSquare V ≤ 3300064 * N * K := by
    have h1 := mul_le_mul_of_nonneg_left hKN (by norm_num : (0 : ℝ) ≤ 3300000)
    have h1' : 3300000 * K / N ≤ 3300000 * (N * K) := by
      simpa only [mul_div_assoc] using h1
    have h2 := mul_le_mul_of_nonneg_left hAK
      (show 0 ≤ 64 * N by positivity)
    calc
      _ ≤ 3300000 * (N * K) + 64 * N * K := by
        exact hVms.trans (add_le_add h1' h2)
      _ = 3300064 * N * K := by ring
  have hVnorm' : ‖V‖ ^ 2 ≤ 7200264 * N ^ 2 * K := by
    have hKscale : K ≤ N ^ 2 * K := by
      have hN2 : 1 ≤ N ^ 2 := by nlinarith
      nlinarith only [hN2, hK]
    have h1 := mul_le_mul_of_nonneg_left hKscale (by norm_num : (0 : ℝ) ≤ 7200200)
    have h2 := mul_le_mul_of_nonneg_left hAK
      (show 0 ≤ 64 * N ^ 2 by positivity)
    calc
      _ ≤ 7200200 * (N ^ 2 * K) + 64 * N ^ 2 * K := by
        exact hVnorm.trans (add_le_add h1 h2)
      _ = 7200264 * N ^ 2 * K := by ring
  have hdms := angleDifference_meanSquare_le (show 0 < 2 * m by omega) η
  have hdnorm0 := angleDifference_pointwise_sq_le (show 0 < 2 * m by omega) η
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hdms hdnorm0
  change meanSquare d ≤ 8 * Real.pi ^ 2 * E / N ^ 3 at hdms
  have hpi : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hdms' : meanSquare d ≤ 128 * K / N ^ 3 := by
    calc
      _ ≤ 8 * Real.pi ^ 2 * E / N ^ 3 := hdms
      _ ≤ 128 * K / N ^ 3 := by
        apply div_le_div_of_nonneg_right _ (pow_nonneg hNpos.le 3)
        have h1 := mul_le_mul_of_nonneg_right hpi hE
        have h2 := mul_le_mul_of_nonneg_left hEK (by norm_num : (0 : ℝ) ≤ 128)
        nlinarith only [h1, h2]
  have hdnorm : ‖d‖ ^ 2 ≤ 128 * K / N ^ 2 := by
    apply norm_sq_le_of_pointwise _ (by positivity)
    intro j
    have hj := hdnorm0 j
    change d j ^ 2 ≤ 8 * Real.pi ^ 2 * E / N ^ 2 at hj
    apply hj.trans
    apply div_le_div_of_nonneg_right _ (sq_nonneg N)
    have h1 := mul_le_mul_of_nonneg_right hpi hE
    have h2 := mul_le_mul_of_nonneg_left hEK (by norm_num : (0 : ℝ) ≤ 128)
    nlinarith only [h1, h2]
  have hums := angleAverage_meanSquare_le (show 2 ≤ 2 * m by omega) η hd.2.1
  have hunorm0 := angleAverage_pointwise_sq_le (show 2 ≤ 2 * m by omega) η hd.2.1
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hums hunorm0
  change meanSquare u ≤ 4 * E / N ^ 2 at hums
  have hums' : meanSquare u ≤ 4 * K / N ^ 2 :=
    hums.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hEK (by norm_num)) (sq_nonneg N))
  have hunorm : ‖u‖ ^ 2 ≤ 12 * ell * K / N ^ 2 := by
    apply norm_sq_le_of_pointwise _ (by positivity)
    intro j
    have hj := hunorm0 j
    change u j ^ 2 ≤ 12 * Real.log N / N ^ 2 * E at hj
    calc
      _ ≤ 12 * Real.log N / N ^ 2 * E := hj
      _ ≤ 12 * ell * K / N ^ 2 := by
        have hl : Real.log N ≤ ell := by dsimp [ell]; linarith
        have hh := mul_le_mul hl hEK hE (by linarith : 0 ≤ ell)
        have hnum : 12 * Real.log N * E ≤ 12 * ell * K :=
          by nlinarith only [hh]
        calc
          12 * Real.log N / N ^ 2 * E =
              (12 * Real.log N * E) / N ^ 2 := by ring
          _ ≤ (12 * ell * K) / N ^ 2 :=
            div_le_div_of_nonneg_right hnum (sq_nonneg N)
          _ = 12 * ell * K / N ^ 2 := by ring
  have hL : (logOrder (2 * m) : ℝ) ≤ N := by
    have hL0 : 0 ≤ (logOrder (2 * m) : ℝ) := by positivity
    have horder' : 10 * (logOrder (2 * m) : ℝ) + 1024 ≤ N := by
      simpa only [N, Nat.cast_mul, Nat.cast_ofNat] using horder
    linarith only [horder', hL0]
  let f₁ : Fin (2 * m) → ℝ := fun j =>
    patternSign w j / (2 * epsilon (2 * m)) *
      Real.cos (Real.pi / (2 * m : ℝ) + angleDifference (by omega) θ j / 2) * d j ^ 2
  let f₂ : Fin (2 * m) → ℝ := fun j => -2 * T j * u j
  let f₃ : Fin (2 * m) → ℝ := fun j => baseRadial (by omega) w θ v j * u j ^ 2
  let f₄ : Fin (2 * m) → ℝ := fun j =>
    let S := rotatedS (by omega) θ v (coordinate (by omega) w θ v) j
    patternSign w j * epsilon (2 * m) * S / H (epsilon (2 * m)) S *
      (2 * U j * u j + S * u j ^ 2)
  let f₅ : Fin (2 * m) → ℝ := fun j =>
    let S := rotatedS (by omega) θ v (coordinate (by omega) w θ v) j;
    -(4 * patternSign w j * epsilon (2 * m) / H (epsilon (2 * m)) S ^ 3 * V j ^ 2)
  have hsourceEq : secondSource (by omega) w θ η v h =
      fun j => (((f₁ j + f₂ j) + f₃ j) + f₄ j) + f₅ j := by
    funext j
    have hVj : V j = T j -
        baseRadial (by omega) w θ v j * u j := by rfl
    dsimp only [f₁, f₂, f₃, f₄, f₅]
    rw [hVj]
    dsimp only [secondSource, d, u, U, T]
    ring
  have hf₁dom : meanSquare f₁ ≤ (N ^ 2 / 8) ^ 2 *
      meanSquare (fun j => d j ^ 2) := by
    apply meanSquare_domination f₁ (fun j => d j ^ 2) (by positivity)
    intro j
    rcases hcoef hm w θ v hdom j with ⟨hc, _hr, _hS, _hH, _hmid, _hlast⟩
    have hc' : |patternSign w j / (2 * epsilon (2 * m)) *
          Real.cos (Real.pi / (2 * m : ℝ) +
            angleDifference (by omega) θ j / 2)| ≤ N ^ 2 / 8 := by
      simpa only [N, Nat.cast_mul, Nat.cast_ofNat] using hc
    dsimp [f₁]
    calc
      |_ * d j ^ 2| =
          |patternSign w j / (2 * epsilon (2 * m)) *
            Real.cos (Real.pi / (2 * m : ℝ) +
              angleDifference (by omega) θ j / 2)| * |d j ^ 2| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hc' (abs_nonneg _)
  have hf₁ : meanSquare f₁ ≤ 256 * ell * K ^ 2 / N := by
    have hsquare := square_meanSquare_le d
    calc
      _ ≤ (N ^ 2 / 8) ^ 2 * meanSquare (fun j => d j ^ 2) := hf₁dom
      _ ≤ (N ^ 2 / 8) ^ 2 * (‖d‖ ^ 2 * meanSquare d) :=
        mul_le_mul_of_nonneg_left hsquare (sq_nonneg _)
      _ ≤ (N ^ 2 / 8) ^ 2 *
          ((128 * K / N ^ 2) * (128 * K / N ^ 3)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact mul_le_mul hdnorm hdms'
          (by unfold meanSquare; positivity) (by positivity)
      _ ≤ 256 * ell * K ^ 2 / N := by
        field_simp [ne_of_gt hNpos]
        have hEllK : K ^ 2 ≤ ell * K ^ 2 := by
          nlinarith only [hell, sq_nonneg K]
        nlinarith only [hEllK]
  have hTu := product_meanSquare_le u T
  have hUu := product_meanSquare_le u U
  have hf₂dom : meanSquare f₂ ≤ 4 * meanSquare (fun j => T j * u j) := by
    have hh := meanSquare_domination f₂ (fun j => T j * u j)
      (K := 2) (by norm_num) (fun j => by
        dsimp [f₂]
        have heq : |-2 * T j * u j| = 2 * |T j * u j| := by
          rw [show -2 * T j * u j = (-2) * (T j * u j) by ring, abs_mul]
          norm_num
        exact heq.le)
    norm_num at hh ⊢
    exact hh
  have hf₂ : meanSquare f₂ ≤ 100000000 * ell * K ^ 2 / N := by
    have hprod : meanSquare (fun j => T j * u j) ≤
        (12 * ell * K / N ^ 2) * (1600032 * N * K) := by
      calc
        _ = meanSquare (fun j => u j * T j) := by congr 2; funext j; ring
        _ ≤ ‖u‖ ^ 2 * meanSquare T := hTu
        _ ≤ _ := mul_le_mul hunorm hTms' (by unfold meanSquare; positivity) (by positivity)
    calc
      _ ≤ 4 * meanSquare (fun j => T j * u j) := hf₂dom
      _ ≤ 4 * ((12 * ell * K / N ^ 2) * (1600032 * N * K)) :=
        mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ ≤ 100000000 * ell * K ^ 2 / N := by
        have hh : (76801536 : ℝ) ≤ 100000000 := by norm_num
        have hX : 0 ≤ ell * K ^ 2 / N := by positivity
        calc
          _ = 76801536 * (ell * K ^ 2 / N) := by
            field_simp [ne_of_gt hNpos]
            ring
          _ ≤ 100000000 * (ell * K ^ 2 / N) :=
            mul_le_mul_of_nonneg_right hh hX
          _ = _ := by ring
  have hf₃dom : meanSquare f₃ ≤ (5 / 2 : ℝ) ^ 2 *
      meanSquare (fun j => u j ^ 2) := by
    apply meanSquare_domination f₃ (fun j => u j ^ 2)
      (K := (5 / 2 : ℝ)) (by norm_num)
    intro j
    rcases hcoef hm w θ v hdom j with ⟨_hc, hr, _hS, _hH, _hmid, _hlast⟩
    dsimp [f₃]
    calc
      |_ * u j ^ 2| = |baseRadial (by omega) w θ v j| * |u j ^ 2| :=
        abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hr (abs_nonneg _)
  have huSquare := square_meanSquare_le u
  have hf₃ : meanSquare f₃ ≤ 1000 * ell * K ^ 2 / N := by
    calc
      _ ≤ (5 / 2 : ℝ) ^ 2 * meanSquare (fun j => u j ^ 2) := hf₃dom
      _ ≤ (5 / 2 : ℝ) ^ 2 * (‖u‖ ^ 2 * meanSquare u) :=
        mul_le_mul_of_nonneg_left huSquare (sq_nonneg _)
      _ ≤ (5 / 2 : ℝ) ^ 2 *
          ((12 * ell * K / N ^ 2) * (4 * K / N ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact mul_le_mul hunorm hums'
          (by unfold meanSquare; positivity) (by positivity)
      _ ≤ 1000 * ell * K ^ 2 / N := by
        have hfrac : (300 : ℝ) / N ^ 4 ≤ 1000 / N := by
          field_simp [ne_of_gt hNpos]
          have hN3 : 1 ≤ N ^ 3 := by
            nlinarith [show 0 ≤ N ^ 2 by positivity]
          nlinarith
        calc
          _ = (300 / N ^ 4) * (ell * K ^ 2) := by ring
          _ ≤ (1000 / N) * (ell * K ^ 2) :=
            mul_le_mul_of_nonneg_right hfrac (by positivity)
          _ = _ := by ring
  have hf₄ : meanSquare f₄ ≤ 300000000 * ell * K ^ 2 / N := by
    let g₁ : Fin (2 * m) → ℝ := fun j => 2 * U j * u j
    let g₂ : Fin (2 * m) → ℝ := fun j =>
      rotatedS (by omega) θ v (coordinate (by omega) w θ v) j * u j ^ 2
    have hfdom : meanSquare f₄ ≤ meanSquare (fun j => g₁ j + g₂ j) := by
      have hh := meanSquare_domination f₄ (fun j => g₁ j + g₂ j)
        (K := 1) (by norm_num) (fun j => by
          rcases hcoef hm w θ v hdom j with
            ⟨_hc, _hr, _hS, _hH, hmid, _hlast⟩
          dsimp [f₄, g₁, g₂]
          rw [abs_mul]
          simpa only [one_mul] using
            mul_le_mul hmid le_rfl (abs_nonneg _) (by norm_num))
      norm_num at hh ⊢
      exact hh
    have hgadd := meanSquare_add_le g₁ g₂
    change meanSquare (fun j => g₁ j + g₂ j) ≤
      2 * meanSquare g₁ + 2 * meanSquare g₂ at hgadd
    have hg₁dom : meanSquare g₁ ≤ 4 * meanSquare (fun j => U j * u j) := by
      have hh := meanSquare_domination g₁ (fun j => U j * u j)
        (K := 2) (by norm_num) (fun j => by
          dsimp [g₁]
          have heq : |2 * U j * u j| = 2 * |U j * u j| := by
            rw [show 2 * U j * u j = 2 * (U j * u j) by ring, abs_mul]
            norm_num
          exact heq.le)
      norm_num at hh ⊢
      exact hh
    have hg₁ : meanSquare g₁ ≤ 100000000 * ell * K ^ 2 / N := by
      have hprod : meanSquare (fun j => U j * u j) ≤
          (12 * ell * K / N ^ 2) * (1600032 * N * K) := by
        calc
          _ = meanSquare (fun j => u j * U j) := by congr 2; funext j; ring
          _ ≤ ‖u‖ ^ 2 * meanSquare U := hUu
          _ ≤ _ := mul_le_mul hunorm hUms' (by unfold meanSquare; positivity) (by positivity)
      calc
        _ ≤ 4 * meanSquare (fun j => U j * u j) := hg₁dom
        _ ≤ 4 * ((12 * ell * K / N ^ 2) * (1600032 * N * K)) :=
          mul_le_mul_of_nonneg_left hprod (by norm_num)
        _ ≤ 100000000 * ell * K ^ 2 / N := by
          have hh : (76801536 : ℝ) ≤ 100000000 := by norm_num
          have hX : 0 ≤ ell * K ^ 2 / N := by positivity
          calc
            _ = 76801536 * (ell * K ^ 2 / N) := by
              field_simp [ne_of_gt hNpos]
              ring
            _ ≤ 100000000 * (ell * K ^ 2 / N) :=
              mul_le_mul_of_nonneg_right hh hX
            _ = _ := by ring
    have hg₂dom : meanSquare g₂ ≤ (18 * N) ^ 2 *
        meanSquare (fun j => u j ^ 2) := by
      apply meanSquare_domination g₂ (fun j => u j ^ 2)
        (K := 18 * N) (by positivity)
      intro j
      rcases hcoef hm w θ v hdom j with ⟨_hc, _hr, hS, _hH, _hmid, _hlast⟩
      dsimp [g₂]
      calc
        |_ * u j ^ 2| =
            |rotatedS (by omega) θ v (coordinate (by omega) w θ v) j| *
              |u j ^ 2| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (hS.trans (mul_le_mul_of_nonneg_left hL (by norm_num))) (abs_nonneg _)
    have hg₂ : meanSquare g₂ ≤ 20000 * ell * K ^ 2 / N := by
      calc
        _ ≤ (18 * N) ^ 2 * meanSquare (fun j => u j ^ 2) := hg₂dom
        _ ≤ (18 * N) ^ 2 * (‖u‖ ^ 2 * meanSquare u) :=
          mul_le_mul_of_nonneg_left huSquare (sq_nonneg _)
        _ ≤ (18 * N) ^ 2 *
            ((12 * ell * K / N ^ 2) * (4 * K / N ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          exact mul_le_mul hunorm hums'
            (by unfold meanSquare; positivity) (by positivity)
        _ ≤ 20000 * ell * K ^ 2 / N := by
          have hfrac : (15552 : ℝ) / N ^ 2 ≤ 20000 / N := by
            field_simp [ne_of_gt hNpos]
            nlinarith
          calc
            _ = (15552 / N ^ 2) * (ell * K ^ 2) := by
              field_simp [ne_of_gt hNpos]
              ring
            _ ≤ (20000 / N) * (ell * K ^ 2) :=
              mul_le_mul_of_nonneg_right hfrac (by positivity)
            _ = _ := by ring
    calc
      _ ≤ meanSquare (fun j => g₁ j + g₂ j) := hfdom
      _ ≤ 2 * meanSquare g₁ + 2 * meanSquare g₂ := hgadd
      _ ≤ 2 * (100000000 * ell * K ^ 2 / N) +
          2 * (20000 * ell * K ^ 2 / N) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hg₁ (by norm_num))
          (mul_le_mul_of_nonneg_left hg₂ (by norm_num))
      _ ≤ 300000000 * ell * K ^ 2 / N := by
        have hh : (200040000 : ℝ) ≤ 300000000 := by norm_num
        have hX : 0 ≤ ell * K ^ 2 / N := by positivity
        calc
          _ = 200040000 * (ell * K ^ 2 / N) := by ring
          _ ≤ 300000000 * (ell * K ^ 2 / N) :=
            mul_le_mul_of_nonneg_right hh hX
          _ = _ := by ring
  have hf₅dom : meanSquare f₅ ≤ (32 / N ^ 2) ^ 2 *
      meanSquare (fun j => V j ^ 2) := by
    apply meanSquare_domination f₅ (fun j => V j ^ 2)
      (K := 32 / N ^ 2) (by positivity)
    intro j
    rcases hcoef hm w θ v hdom j with ⟨_hc, _hr, _hS, _hH, _hmid, hlast⟩
    dsimp [f₅]
    rw [abs_neg]
    calc
      |_ * V j ^ 2| =
          |4 * patternSign w j * epsilon (2 * m) /
            H (epsilon (2 * m))
              (rotatedS (by omega) θ v (coordinate (by omega) w θ v) j) ^ 3| *
            |V j ^ 2| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hlast (abs_nonneg _)
  have hVSquare := square_meanSquare_le V
  have hf₅ : meanSquare f₅ ≤ 30000000000000000 * ell * K ^ 2 / N := by
    calc
      _ ≤ (32 / N ^ 2) ^ 2 * meanSquare (fun j => V j ^ 2) := hf₅dom
      _ ≤ (32 / N ^ 2) ^ 2 * (‖V‖ ^ 2 * meanSquare V) :=
        mul_le_mul_of_nonneg_left hVSquare (sq_nonneg _)
      _ ≤ (32 / N ^ 2) ^ 2 *
          ((7200264 * N ^ 2 * K) * (3300064 * N * K)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact mul_le_mul hVnorm' hVms'
          (by unfold meanSquare; positivity) (by positivity)
      _ ≤ 30000000000000000 * ell * K ^ 2 / N := by
        have hc : (24331603985301504 : ℝ) ≤
            30000000000000000 * ell := by nlinarith
        have hX : 0 ≤ K ^ 2 / N := by positivity
        calc
          _ = 24331603985301504 * (K ^ 2 / N) := by
            field_simp [ne_of_gt hNpos]
            ring
          _ ≤ (30000000000000000 * ell) * (K ^ 2 / N) :=
            mul_le_mul_of_nonneg_right hc hX
          _ = _ := by ring
  rw [hsourceEq]
  calc
    _ ≤ 16 * (meanSquare f₁ + meanSquare f₂ + meanSquare f₃ +
        meanSquare f₄ + meanSquare f₅) := meanSquare_five_add_le _ _ _ _ _
    _ ≤ 16 * ((256 + 100000000 + 1000 + 300000000 +
        30000000000000000) * ell * K ^ 2 / N) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      calc
        _ ≤ 256 * ell * K ^ 2 / N +
            100000000 * ell * K ^ 2 / N +
            1000 * ell * K ^ 2 / N +
            300000000 * ell * K ^ 2 / N +
            30000000000000000 * ell * K ^ 2 / N := by
          exact add_le_add (add_le_add (add_le_add (add_le_add hf₁ hf₂) hf₃) hf₄) hf₅
        _ = _ := by ring
    _ ≤ 1000000000000000000 * ell * K ^ 2 / N := by
      have hh : 0 ≤ ell * K ^ 2 / N := by positivity
      ring_nf at hh ⊢
      nlinarith only [hh]

theorem chosen_second_l1_of_linearizations {m : ℕ}
    (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m)
    (hm : 2 ≤ m) (w : SignPattern (by omega))
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (hdom : InDomain (by omega) θ v) (hd : Admissible (by omega) (η, h))
    (hlin₁ : normalLinearization (by omega) w θ v
      (chosenFirstDerivative (by omega) w θ η v h) = source (by omega) w θ η v h)
    (hlin₂ : normalLinearization (by omega) w θ v
      (chosenSecondDerivative (by omega) w θ η v h) = secondSource (by omega) w θ η v h) :
    let E := pairEnergy (by omega) (fun j => (η j : ℂ))
    let A := pairEnergy (by omega) h
    let K := E + A
    (∑ j, |chosenSecondDerivative (by omega) w θ η v h j|) / (2 * m : ℝ) ≤
      240000000 *
        (K / (2 * m : ℝ) + Real.sqrt (A * E) / Real.sqrt (2 * m : ℝ)) := by
  have hinv := actual_solution_bounds hN
  have hs := second_source_l1_of_linearization hN hm w θ η v h hdom hd hlin₁
  clear hN hlin₁
  dsimp only
  have hi := (hinv hm w θ v hdom
    (chosenSecondDerivative (by omega) w θ η v h)).1
  rw [hlin₂] at hi
  dsimp only at hs
  calc
    _ ≤ 2 * ((∑ j, |secondSource (by omega) w θ η v h j|) /
        (2 * m : ℝ)) := hi
    _ ≤ 2 * (120000000 *
        ((pairEnergy (by omega) (fun j => (η j : ℂ)) + pairEnergy (by omega) h) /
          (2 * m : ℝ) +
        Real.sqrt (pairEnergy (by omega) h *
          pairEnergy (by omega) (fun j => (η j : ℂ))) /
          Real.sqrt (2 * m : ℝ))) :=
      mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = _ := by ring

theorem chosen_second_meanSquare_of_linearizations {m : ℕ}
    (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m)
    (hm : 2 ≤ m) (w : SignPattern (by omega))
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (hdom : InDomain (by omega) θ v) (hd : Admissible (by omega) (η, h))
    (hlin₁ : normalLinearization (by omega) w θ v
      (chosenFirstDerivative (by omega) w θ η v h) = source (by omega) w θ η v h)
    (hlin₂ : normalLinearization (by omega) w θ v
      (chosenSecondDerivative (by omega) w θ η v h) = secondSource (by omega) w θ η v h) :
    let K := pairEnergy (by omega) (fun j => (η j : ℂ)) + pairEnergy (by omega) h
    meanSquare (chosenSecondDerivative (by omega) w θ η v h) ≤
      4000000000000000000 * (1 + Real.log (2 * m : ℝ)) * K ^ 2 /
        (2 * m : ℝ) := by
  have hinv := actual_solution_bounds hN
  have hs := second_source_meanSquare_of_linearization hN hm w θ η v h hdom hd hlin₁
  clear hN hlin₁
  dsimp only
  let q := chosenSecondDerivative (by omega) w θ η v h
  let src := secondSource (by omega) w θ η v h
  have hqroot := (hinv hm w θ v hdom q).2.1
  rw [hlin₂] at hqroot
  change Real.sqrt (meanSquare q) ≤ 2 * Real.sqrt (meanSquare src) at hqroot
  have hq0 : 0 ≤ meanSquare q := by unfold meanSquare; positivity
  have hs0 : 0 ≤ meanSquare src := by unfold meanSquare; positivity
  have hqms := pow_le_pow_left₀ (Real.sqrt_nonneg _) hqroot 2
  rw [Real.sq_sqrt hq0, mul_pow, Real.sq_sqrt hs0] at hqms
  norm_num at hqms
  dsimp only at hs
  change meanSquare src ≤
    1000000000000000000 * (1 + Real.log (2 * m : ℝ)) *
      (pairEnergy (by omega) (fun j => (η j : ℂ)) + pairEnergy (by omega) h) ^ 2 /
        (2 * m : ℝ) at hs
  calc
    meanSquare q ≤ 4 * meanSquare src := hqms
    _ ≤ 4 * (1000000000000000000 * (1 + Real.log (2 * m : ℝ)) *
        (pairEnergy (by omega) (fun j => (η j : ℂ)) +
          pairEnergy (by omega) h) ^ 2 / (2 * m : ℝ)) :=
      mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = _ := by ring

theorem chosen_second_coarse_of_linearizations {m : ℕ}
    (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m)
    (hm : 2 ≤ m) (w : SignPattern (by omega))
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ)
    (hdom : InDomain (by omega) θ v) (hd : Admissible (by omega) (η, h))
    (hlin₁ : normalLinearization (by omega) w θ v
      (chosenFirstDerivative (by omega) w θ η v h) = source (by omega) w θ η v h)
    (hlin₂ : normalLinearization (by omega) w θ v
      (chosenSecondDerivative (by omega) w θ η v h) = secondSource (by omega) w θ η v h) :
    meanSquare (chosenSecondDerivative (by omega) w θ η v h) ≤
      (pairEnergy (by omega) (fun j => (η j : ℂ)) + pairEnergy (by omega) h) ^ 2 := by
  have hs := chosen_second_meanSquare_of_linearizations hN hm w θ η v h hdom hd hlin₁ hlin₂
  have hsmall := ExplicitHessianThreshold.log_monomial_div_small
    (j := 1) (c := 4000000000000000000) hN (by norm_num) (by norm_num)
  simp only [pow_one, Erdos1045.ExplicitThreshold.logBudget, Nat.cast_mul,
    Nat.cast_ofNat] at hsmall
  clear hN hlin₁ hlin₂
  let K := pairEnergy (by omega) (fun j => (η j : ℂ)) + pairEnergy (by omega) h
  have hK : 0 ≤ K := by
    dsimp [K]
    exact add_nonneg (pairEnergy_nonneg (by omega) _) (pairEnergy_nonneg (by omega) _)
  dsimp only at hs
  change meanSquare (chosenSecondDerivative (by omega) w θ η v h) ≤
    4000000000000000000 * (1 + Real.log (2 * m : ℝ)) * K ^ 2 /
      (2 * m : ℝ) at hs
  have hfactor : 4000000000000000000 * (1 + Real.log (2 * m : ℝ)) /
      (2 * m : ℝ) ≤ 1 := by
    linarith only [hsmall]
  calc
    _ ≤ 4000000000000000000 * (1 + Real.log (2 * m : ℝ)) /
        (2 * m : ℝ) * K ^ 2 := by
      calc
        _ ≤ 4000000000000000000 * (1 + Real.log (2 * m : ℝ)) * K ^ 2 /
            (2 * m : ℝ) := hs
        _ = _ := by ring
    _ ≤ 1 * K ^ 2 := mul_le_mul_of_nonneg_right hfactor (sq_nonneg K)
    _ = _ := by dsimp [K]; ring

theorem chosen_second_l1 {m : ℕ}
    (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (w : SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      let E := pairEnergy (by omega) (fun j => (η j : ℂ))
      let A := pairEnergy (by omega) h
      let K := E + A
      (∑ j, |chosenSecondDerivative (by omega) w θ η v h j|) /
          (2 * m : ℝ) ≤
        240000000 *
          (K / (2 * m : ℝ) + Real.sqrt (A * E) / Real.sqrt (2 * m : ℝ)) := by
  intro hm w θ η v h hdom hd
  have hlin := chosen_normalLinearizations hN hm w θ η v h hdom hd
  exact chosen_second_l1_of_linearizations hN hm w θ η v h hdom hd hlin.1 hlin.2

theorem chosen_second_coarse {m : ℕ}
    (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (w : SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      meanSquare (chosenSecondDerivative (by omega) w θ η v h) ≤
        (pairEnergy (by omega) (fun j => (η j : ℂ)) +
          pairEnergy (by omega) h) ^ 2 := by
  intro hm w θ η v h hdom hd
  have hlin := chosen_normalLinearizations hN hm w θ η v h hdom hd
  exact chosen_second_coarse_of_linearizations hN hm w θ η v h hdom hd hlin.1 hlin.2

end
end StructuralNote.ExplicitFixedSchurSecondMoments
