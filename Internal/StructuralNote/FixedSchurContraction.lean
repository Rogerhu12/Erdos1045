import StructuralNote.FixedSchurHarmonicBounds
import StructuralNote.FixedSchurScalarRoot

/-! A quantitative contraction for the actual normalized Schur coordinate.
The ball lies in the full real function space.  Antiperiodicity of its fixed
point follows separately from the symmetry of the crossing equation. -/

namespace StructuralNote.FixedSchurContraction

open Real Set Metric
open Erdos1045.EventualExact FourierMultiplier FiniteFourierLift SchurLift
open EdgeCoordinates FixedSchurHarmonicBounds FixedSchurScalarRoot
open scoped NNReal

noncomputable section

def crossingMap {n : ℕ} (ε : ℝ) (X Y pv σ q : Fin n → ℝ) : Fin n → ℝ :=
  fun j => rootValue (σ j) ε (X j) (Y j) (pv j + J q j)

theorem ball_input_bound {n : ℕ} (hn : 0 < n) {ε R : ℝ} (hε : 0 < ε)
    (Y pv σ f : Fin n → ℝ) (hσ : ∀ j, σ j = 1 ∨ σ j = -1)
    (hsmall : ∀ j, |Y j| + ε * (|pv j| + 2 * (‖f‖ + R)) ≤ 1 / 4)
    {q : Fin n → ℝ} (hq : q ∈ closedBall f R) (j : Fin n) :
    |Y j + σ j * ε * (pv j + J q j)| ≤ 1 / 4 := by
  have hqR : ‖q - f‖ ≤ R := by simpa only [mem_closedBall, dist_eq_norm] using hq
  have hqnorm : ‖q‖ ≤ ‖f‖ + R := by
    linarith [norm_sub_norm_le q f]
  have hJ : |J q j| ≤ 2 * (‖f‖ + R) := by
    have h := norm_le_pi_norm (J q) j
    rw [Real.norm_eq_abs] at h
    exact h.trans ((J_norm_le hn q).trans (by linarith))
  have hσabs : |σ j| = 1 := by rcases hσ j with h | h <;> rw [h] <;> norm_num
  calc
    |Y j + σ j * ε * (pv j + J q j)| ≤
        |Y j| + |σ j * ε * (pv j + J q j)| := abs_add_le _ _
    _ = |Y j| + ε * |pv j + J q j| := by
      rw [abs_mul, abs_mul, hσabs, abs_of_pos hε, one_mul]
    _ ≤ |Y j| + ε * (|pv j| + |J q j|) := by
      gcongr
      exact abs_add_le _ _
    _ ≤ |Y j| + ε * (|pv j| + 2 * (‖f‖ + R)) := by gcongr
    _ ≤ 1 / 4 := hsmall j

theorem crossingMap_lipschitz {n : ℕ} (hn : 0 < n) {ε R : ℝ} (hε : 0 < ε)
    (X Y pv σ f : Fin n → ℝ) (hσ : ∀ j, σ j = 1 ∨ σ j = -1)
    (hsmall : ∀ j, |Y j| + ε * (|pv j| + 2 * (‖f‖ + R)) ≤ 1 / 4) :
    LipschitzOnWith (1 / 2) (crossingMap ε X Y pv σ) (closedBall f R) := by
  apply lipschitzOnWith_iff_norm_sub_le.mpr
  intro q hq r hr
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro j
  have h := rootValue_lipschitz_of_le_one (X := X j) (hσ j) hε
    (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1)
    (ball_input_bound hn hε Y pv σ f hσ hsmall hq j)
    (ball_input_bound hn hε Y pv σ f hσ hsmall hr j)
  have hj : |J q j - J r j| ≤ 2 * ‖q - r‖ := by
    have hp := norm_le_pi_norm (J q - J r) j
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using hp.trans (J_sub_norm_le hn q r)
  simp only [add_sub_add_left_eq_sub] at h
  change |rootValue (σ j) ε (X j) (Y j) (pv j + J q j) -
    rootValue (σ j) ε (X j) (Y j) (pv j + J r j)| ≤ _
  norm_num
  linarith

theorem crossingMap_maps_ball {n : ℕ} (hn : 0 < n) {ε R : ℝ} (hε : 0 < ε)
    (hR : 0 ≤ R) (X Y pv σ f : Fin n → ℝ) (hσ : ∀ j, σ j = 1 ∨ σ j = -1)
    (hsmall : ∀ j, |Y j| + ε * (|pv j| + 2 * (‖f‖ + R)) ≤ 1 / 4)
    (hsource : ‖crossingMap ε X Y pv σ f - f‖ ≤ R / 2) :
    MapsTo (crossingMap ε X Y pv σ) (closedBall f R) (closedBall f R) := by
  have hLip := crossingMap_lipschitz hn hε X Y pv σ f hσ hsmall
  have hf : f ∈ closedBall f R := by simp [hR]
  intro q hq
  have h := (lipschitzOnWith_iff_norm_sub_le.mp hLip) hq hf
  have hqR : ‖q - f‖ ≤ R := by simpa only [mem_closedBall, dist_eq_norm] using hq
  have htri := norm_add_le (crossingMap ε X Y pv σ q - crossingMap ε X Y pv σ f)
    (crossingMap ε X Y pv σ f - f)
  rw [sub_add_sub_cancel] at htri
  rw [mem_closedBall, dist_eq_norm]
  norm_num at h
  linarith

theorem exists_unique_fixedPoint {n : ℕ} (hn : 0 < n) {ε R : ℝ} (hε : 0 < ε)
    (hR : 0 ≤ R) (X Y pv σ f : Fin n → ℝ) (hσ : ∀ j, σ j = 1 ∨ σ j = -1)
    (hsmall : ∀ j, |Y j| + ε * (|pv j| + 2 * (‖f‖ + R)) ≤ 1 / 4)
    (hsource : ‖crossingMap ε X Y pv σ f - f‖ ≤ R / 2) :
    ∃! q : Fin n → ℝ, ‖q - f‖ ≤ R ∧ crossingMap ε X Y pv σ q = q := by
  have hmap := crossingMap_maps_ball hn hε hR X Y pv σ f hσ hsmall hsource
  have hLip := crossingMap_lipschitz hn hε X Y pv σ f hσ hsmall
  have hcon : ContractingWith (1 / 2 : ℝ≥0)
      (hmap.restrict (crossingMap ε X Y pv σ) (closedBall f R) (closedBall f R)) := by
    refine ⟨by norm_num, ?_⟩
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact hLip.dist_le_mul x x.property y y.property
  have hf : f ∈ closedBall f R := by simp [hR]
  obtain ⟨q, hq, hfix, _⟩ := ContractingWith.exists_fixedPoint'
    isClosed_closedBall.isComplete hmap hcon hf (edist_ne_top _ _)
  refine ⟨q, ⟨by simpa only [mem_closedBall, dist_eq_norm] using hq, hfix⟩, ?_⟩
  intro r hr
  have hrmem : r ∈ closedBall f R := by simpa only [mem_closedBall, dist_eq_norm] using hr.1
  have h := (lipschitzOnWith_iff_norm_sub_le.mp hLip) hrmem hq
  rw [hr.2, hfix] at h
  norm_num at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (r - q)]))

theorem fixedPoint_error {n : ℕ} (hn : 0 < n) {ε R : ℝ} (hε : 0 < ε)
    (hR : 0 ≤ R) (X Y pv σ f : Fin n → ℝ) (hσ : ∀ j, σ j = 1 ∨ σ j = -1)
    (hsmall : ∀ j, |Y j| + ε * (|pv j| + 2 * (‖f‖ + R)) ≤ 1 / 4)
    {q : Fin n → ℝ} (hq : ‖q - f‖ ≤ R) (hfix : crossingMap ε X Y pv σ q = q) :
    ‖q - f‖ ≤ 2 * ‖crossingMap ε X Y pv σ f - f‖ := by
  have hLip := crossingMap_lipschitz hn hε X Y pv σ f hσ hsmall
  have hf : f ∈ closedBall f R := by simp [hR]
  have hqmem : q ∈ closedBall f R := by simpa only [mem_closedBall, dist_eq_norm] using hq
  have h := (lipschitzOnWith_iff_norm_sub_le.mp hLip) hqmem hf
  rw [hfix] at h
  have htri := norm_add_le (q - crossingMap ε X Y pv σ f) (crossingMap ε X Y pv σ f - f)
  rw [sub_add_sub_cancel] at htri
  norm_num at h
  linarith

theorem crossingMap_antiperiodic {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (X Y pv σ q : Fin (2 * m) → ℝ)
    (hX : ∀ j, X (halfTurn hm j) = X j) (hY : ∀ j, Y (halfTurn hm j) = Y j)
    (hp : FiniteBox.Antiperiodic hm pv) (hσ : FiniteBox.Antiperiodic hm σ) :
    FiniteBox.Antiperiodic hm (crossingMap ε X Y pv σ q) := by
  intro j
  simp only [crossingMap, rootValue, hX j, hY j, hσ j, hp j, J_antiperiodic hm q j]
  rw [show Y j + -σ j * ε * (-pv j + -J q j) = Y j + σ j * ε * (pv j + J q j) by ring]
  ring

theorem fixedPoint_antiperiodic {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (X Y pv σ q : Fin (2 * m) → ℝ)
    (hX : ∀ j, X (halfTurn hm j) = X j) (hY : ∀ j, Y (halfTurn hm j) = Y j)
    (hp : FiniteBox.Antiperiodic hm pv) (hσ : FiniteBox.Antiperiodic hm σ)
    (hfix : crossingMap ε X Y pv σ q = q) : FiniteBox.Antiperiodic hm q := by
  rw [← hfix]
  exact crossingMap_antiperiodic hm ε X Y pv σ q hX hY hp hσ

end
end StructuralNote.FixedSchurContraction
