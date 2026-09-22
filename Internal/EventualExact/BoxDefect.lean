import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

/-!
# Positive quadratic forms on finite boxes

The sign rounding estimate of manuscript Lemma 7.1 is proved for a concrete real
linear operator. At a zero of the potential the original sign is retained, so
rounding also preserves an antipodal sign relation.
-/

noncomputable section

open scoped BigOperators

namespace Erdos1045.EventualExact

variable {ι : Type*} [Fintype ι]

/-- The unnormalized real pairing on a finite vector space. -/
def finitePairing (f g : ι → ℝ) : ℝ := ∑ i, f i * g i

theorem finitePairing_comm (f g : ι → ℝ) :
    finitePairing f g = finitePairing g f := by
  simp only [finitePairing, mul_comm]

@[simp] theorem finitePairing_add_left (f h g : ι → ℝ) :
    finitePairing (f + h) g = finitePairing f g + finitePairing h g := by
  simp [finitePairing, add_mul, Finset.sum_add_distrib]

@[simp] theorem finitePairing_add_right (f g h : ι → ℝ) :
    finitePairing f (g + h) = finitePairing f g + finitePairing f h := by
  simp [finitePairing, mul_add, Finset.sum_add_distrib]

/-- A quadratic energy with the conventional factor one half. -/
def boxEnergy (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (f : ι → ℝ) : ℝ :=
  finitePairing f (T f) / 2

/-- The empirical-average normalization. -/
def normalizedBoxEnergy (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (f : ι → ℝ) : ℝ :=
  boxEnergy T f / Fintype.card ι

/-- Self-adjointness expressed in the explicitly defined finite pairing. -/
def FiniteSelfAdjoint (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) : Prop :=
  ∀ f g, finitePairing f (T g) = finitePairing g (T f)

/-- Positive semidefiniteness of the explicitly defined finite quadratic form. -/
def FinitePositiveSemidefinite (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) : Prop :=
  ∀ f, 0 ≤ finitePairing f (T f)

theorem boxEnergy_nonneg {T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
    (hT : FinitePositiveSemidefinite T) (f : ι → ℝ) : 0 ≤ boxEnergy T f :=
  div_nonneg (hT f) (by norm_num)

theorem boxEnergy_add {T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
    (hT : FiniteSelfAdjoint T) (f u : ι → ℝ) :
    boxEnergy T (f + u) =
      boxEnergy T f + finitePairing u (T f) + boxEnergy T u := by
  simp only [boxEnergy, map_add, finitePairing_add_left, finitePairing_add_right]
  rw [hT f u]
  ring

theorem boxEnergy_sub {T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
    (hT : FiniteSelfAdjoint T) (f h : ι → ℝ) :
    boxEnergy T h - boxEnergy T f =
      finitePairing (h - f) (T f) + boxEnergy T (h - f) := by
  have he := boxEnergy_add hT f (h - f)
  rw [add_sub_cancel] at he
  linarith

/-- A sign takes values in the two vertices of the unit interval. -/
def IsSignVector (σ : ι → ℝ) : Prop := ∀ i, σ i = 1 ∨ σ i = -1

/-- Reverse a sign precisely where its product with the potential is negative. -/
def roundedSign (s x : ℝ) : ℝ := if s * x < 0 then -s else s

/-- A weighted indicator of a disagreement with the potential. -/
def badSignWeight (s x : ℝ) : ℝ := if s * x < 0 then |x| else 0

theorem badSignWeight_nonneg (s x : ℝ) : 0 ≤ badSignWeight s x := by
  unfold badSignWeight
  split <;> positivity

theorem roundedSign_is_sign {s x : ℝ} (hs : s = 1 ∨ s = -1) :
    roundedSign s x = 1 ∨ roundedSign s x = -1 := by
  unfold roundedSign
  split <;> rcases hs with rfl | rfl <;> norm_num

theorem roundedSign_zero (s : ℝ) : roundedSign s 0 = s := by
  simp [roundedSign]

theorem roundedSign_neg (s x : ℝ) : roundedSign (-s) (-x) = -roundedSign s x := by
  simp only [roundedSign, neg_mul_neg]
  split <;> rfl

theorem sign_mul_abs {s x : ℝ} (hs : s = 1 ∨ s = -1) : |s * x| = |x| := by
  rcases hs with rfl | rfl <;> simp

theorem sign_abs_gap {s x : ℝ} (hs : s = 1 ∨ s = -1) :
    s * x - |x| = -2 * badSignWeight s x := by
  have ha := sign_mul_abs (x := x) hs
  unfold badSignWeight
  split
  next h => rw [abs_of_neg h] at ha; linarith
  next h => rw [abs_of_nonneg (le_of_not_gt h)] at ha; linarith

theorem roundedSign_gain {s x : ℝ} (hs : s = 1 ∨ s = -1) :
    (roundedSign s x - s) * x = 2 * badSignWeight s x := by
  have ha := sign_mul_abs (x := x) hs
  unfold roundedSign badSignWeight
  split
  next h => rw [abs_of_neg h] at ha; nlinarith
  next h => ring

theorem roundedSign_mul {s x : ℝ} (hs : s = 1 ∨ s = -1) :
    roundedSign s x * x = |x| := by
  have h₁ := roundedSign_gain (x := x) hs
  have h₂ := sign_abs_gap (x := x) hs
  nlinarith

theorem sign_abs_gap_sq_le {s x M : ℝ} (hs : s = 1 ∨ s = -1)
    (hM : |x| ≤ M) : (s * x - |x|) ^ 2 ≤ 4 * M * badSignWeight s x := by
  rw [sign_abs_gap hs]
  unfold badSignWeight
  split
  next h => nlinarith [mul_nonneg (abs_nonneg x) (sub_nonneg.mpr hM)]
  next h => simp

/-- The box vertex with amplitude `A` and prescribed signs. -/
def boxVertex (A : ℝ) (σ : ι → ℝ) : ι → ℝ := fun i => A * σ i

/-- Simultaneous sign rounding with zero-potential signs left unchanged. -/
def roundedBoxVertex (A : ℝ) (σ g : ι → ℝ) : ι → ℝ :=
  fun i => A * roundedSign (σ i) (g i)

/-- Total potential weight at signs that disagree with their potential. -/
def badSignMass (σ g : ι → ℝ) : ℝ := ∑ i, badSignWeight (σ i) (g i)

theorem badSignMass_eq_sum_filter (σ g : ι → ℝ) :
    badSignMass σ g = ∑ i ∈ Finset.univ.filter (fun i => σ i * g i < 0), |g i| := by
  classical
  simp [badSignMass, badSignWeight, Finset.sum_filter]

theorem badSignMass_nonneg (σ g : ι → ℝ) : 0 ≤ badSignMass σ g :=
  Finset.sum_nonneg fun i _ => badSignWeight_nonneg (σ i) (g i)

omit [Fintype ι] in
theorem roundedBoxVertex_mem_box {A : ℝ} (hA : 0 ≤ A)
    {σ : ι → ℝ} (hσ : IsSignVector σ) (g : ι → ℝ) (i : ι) :
    |roundedBoxVertex A σ g i| ≤ A := by
  rcases roundedSign_is_sign (x := g i) (hσ i) with hs | hs <;>
    simp [roundedBoxVertex, hs, abs_of_nonneg hA]

theorem roundedBoxVertex_pairing {A : ℝ} {σ : ι → ℝ}
    (hσ : IsSignVector σ) (g : ι → ℝ) :
    finitePairing (roundedBoxVertex A σ g - boxVertex A σ) g =
      2 * A * badSignMass σ g := by
  unfold finitePairing badSignMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi := roundedSign_gain (x := g i) (hσ i)
  change (A * roundedSign (σ i) (g i) - A * σ i) * g i =
    2 * A * badSignWeight (σ i) (g i)
  nlinarith [congrArg (fun t : ℝ => A * t) hi]

/-- The exact quadratic identity retains the nonnegative second-order term. -/
theorem roundedBoxVertex_energy_identity
    {T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} (hT : FiniteSelfAdjoint T)
    {A : ℝ} {σ : ι → ℝ} (hσ : IsSignVector σ) :
    let f := boxVertex A σ
    let g := T f
    let h := roundedBoxVertex A σ g
    boxEnergy T h - boxEnergy T f =
      2 * A * badSignMass σ g + boxEnergy T (h - f) := by
  dsimp
  rw [boxEnergy_sub hT, roundedBoxVertex_pairing hσ]

/-- Only the energy of the explicitly rounded competitor needs an upper bound. -/
theorem badSignMass_mul_le_defect
    {T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} (hTs : FiniteSelfAdjoint T)
    (hTp : FinitePositiveSemidefinite T) {A B : ℝ}
    {σ : ι → ℝ} (hσ : IsSignVector σ)
    (hB : boxEnergy T (roundedBoxVertex A σ (T (boxVertex A σ))) ≤ B) :
    2 * A * badSignMass σ (T (boxVertex A σ)) ≤ B - boxEnergy T (boxVertex A σ) := by
  have he := roundedBoxVertex_energy_identity hTs (A := A) hσ
  dsimp at he
  have hp := boxEnergy_nonneg hTp
    (roundedBoxVertex A σ (T (boxVertex A σ)) - boxVertex A σ)
  linarith

theorem badSignMass_le_defect
    {T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} (hTs : FiniteSelfAdjoint T)
    (hTp : FinitePositiveSemidefinite T) {A B : ℝ} (hA : 0 < A)
    {σ : ι → ℝ} (hσ : IsSignVector σ)
    (hB : boxEnergy T (roundedBoxVertex A σ (T (boxVertex A σ))) ≤ B) :
    badSignMass σ (T (boxVertex A σ)) ≤ (B - boxEnergy T (boxVertex A σ)) / (2 * A) := by
  apply (le_div_iff₀ (by positivity : 0 < 2 * A)).2
  simpa only [mul_comm] using badSignMass_mul_le_defect hTs hTp hσ hB

theorem signResidual_sq_sum_le {σ g : ι → ℝ} (hσ : IsSignVector σ)
    {M : ℝ} (hM : ∀ i, |g i| ≤ M) :
    (∑ i, (σ i * g i - |g i|) ^ 2) ≤ 4 * M * badSignMass σ g := by
  unfold badSignMass
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => sign_abs_gap_sq_le (hσ i) (hM i)

omit [Fintype ι] in
/-- An involutive or antipodal pairing is preserved even at zero potential. -/
theorem roundedBoxVertex_antiperiodic {A : ℝ} {σ g : ι → ℝ} (p : ι → ι)
    (hσ : ∀ i, σ (p i) = -σ i) (hg : ∀ i, g (p i) = -g i) (i : ι) :
    roundedBoxVertex A σ g (p i) = -roundedBoxVertex A σ g i := by
  simp [roundedBoxVertex, hσ i, hg i, roundedSign_neg]

section Normalized

variable [Nonempty ι]

theorem normalized_badSignMass_le_defect_of_nonneg
    {T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} (hTs : FiniteSelfAdjoint T)
    {A B : ℝ} (hA : 0 < A) {σ : ι → ℝ} (hσ : IsSignVector σ)
    (hp : 0 ≤ boxEnergy T
      (roundedBoxVertex A σ (T (boxVertex A σ)) - boxVertex A σ))
    (hB : normalizedBoxEnergy T (roundedBoxVertex A σ (T (boxVertex A σ))) ≤ B) :
    badSignMass σ (T (boxVertex A σ)) / Fintype.card ι ≤
      (B - normalizedBoxEnergy T (boxVertex A σ)) / (2 * A) := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hB' : boxEnergy T (roundedBoxVertex A σ (T (boxVertex A σ))) ≤
      B * Fintype.card ι := (div_le_iff₀ hn).1 hB
  have he := roundedBoxVertex_energy_identity hTs (A := A) hσ
  dsimp at he
  have hb : 2 * A * badSignMass σ (T (boxVertex A σ)) ≤
      B * Fintype.card ι - boxEnergy T (boxVertex A σ) := by linarith
  apply (le_div_iff₀ (by positivity : 0 < 2 * A)).2
  unfold normalizedBoxEnergy
  apply (le_of_mul_le_mul_right ?_ hn)
  have hn0 := ne_of_gt hn
  field_simp
  nlinarith

theorem normalized_badSignMass_le_defect
    {T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} (hTs : FiniteSelfAdjoint T)
    (hTp : FinitePositiveSemidefinite T) {A B : ℝ} (hA : 0 < A)
    {σ : ι → ℝ} (hσ : IsSignVector σ)
    (hB : normalizedBoxEnergy T (roundedBoxVertex A σ (T (boxVertex A σ))) ≤ B) :
    badSignMass σ (T (boxVertex A σ)) / Fintype.card ι ≤
      (B - normalizedBoxEnergy T (boxVertex A σ)) / (2 * A) :=
  normalized_badSignMass_le_defect_of_nonneg hTs hA hσ (boxEnergy_nonneg hTp _) hB

/-- The unnormalized bad mass has the factor `n` stated in Lemma 7.1. -/
theorem badSignMass_le_card_mul_normalized_defect
    {T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} (hTs : FiniteSelfAdjoint T)
    (hTp : FinitePositiveSemidefinite T) {A B : ℝ} (hA : 0 < A)
    {σ : ι → ℝ} (hσ : IsSignVector σ)
    (hB : normalizedBoxEnergy T (roundedBoxVertex A σ (T (boxVertex A σ))) ≤ B) :
    badSignMass σ (T (boxVertex A σ)) ≤
      Fintype.card ι * (B - normalizedBoxEnergy T (boxVertex A σ)) / (2 * A) := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hb := (div_le_iff₀ hn).1 (normalized_badSignMass_le_defect hTs hTp hA hσ hB)
  calc
    _ ≤ ((B - normalizedBoxEnergy T (boxVertex A σ)) / (2 * A)) * Fintype.card ι := hb
    _ = _ := by ring

theorem normalized_signResidual_sq_le_defect
    {T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} (hTs : FiniteSelfAdjoint T)
    (hTp : FinitePositiveSemidefinite T) {A B M : ℝ} (hA : 0 < A)
    {σ : ι → ℝ} (hσ : IsSignVector σ) (hM0 : 0 ≤ M)
    (hM : ∀ i, |T (boxVertex A σ) i| ≤ M)
    (hB : normalizedBoxEnergy T (roundedBoxVertex A σ (T (boxVertex A σ))) ≤ B) :
    (∑ i, (σ i * T (boxVertex A σ) i - |T (boxVertex A σ) i|) ^ 2) /
      Fintype.card ι ≤ (2 * M / A) * (B - normalizedBoxEnergy T (boxVertex A σ)) := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hb := normalized_badSignMass_le_defect hTs hTp hA hσ hB
  have hs := signResidual_sq_sum_le hσ hM
  calc
    _ ≤ (4 * M * badSignMass σ (T (boxVertex A σ))) / Fintype.card ι :=
      div_le_div_of_nonneg_right hs hn.le
    _ = 4 * M * (badSignMass σ (T (boxVertex A σ)) / Fintype.card ι) := by ring
    _ ≤ 4 * M * ((B - normalizedBoxEnergy T (boxVertex A σ)) / (2 * A)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by field_simp; ring

/-- The infinity norm form of the second inequality in manuscript Lemma 7.1. -/
theorem normalized_signResidual_sq_le_norm_defect
    {T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} (hTs : FiniteSelfAdjoint T)
    (hTp : FinitePositiveSemidefinite T) {A B : ℝ} (hA : 0 < A)
    {σ : ι → ℝ} (hσ : IsSignVector σ)
    (hB : normalizedBoxEnergy T (roundedBoxVertex A σ (T (boxVertex A σ))) ≤ B) :
    (∑ i, (σ i * T (boxVertex A σ) i - |T (boxVertex A σ) i|) ^ 2) /
      Fintype.card ι ≤ (2 * ‖T (boxVertex A σ)‖ / A) *
        (B - normalizedBoxEnergy T (boxVertex A σ)) := by
  apply normalized_signResidual_sq_le_defect hTs hTp hA hσ (norm_nonneg _) ?_ hB
  intro i
  simpa only [Real.norm_eq_abs] using norm_le_pi_norm (T (boxVertex A σ)) i

/-- A box upper bound supplies the rounded competitor's upper bound automatically. -/
theorem normalized_box_rounding_defect
    {T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} (hTs : FiniteSelfAdjoint T)
    (hTp : FinitePositiveSemidefinite T) {A B : ℝ} (hA : 0 < A)
    {σ : ι → ℝ} (hσ : IsSignVector σ)
    (hB : ∀ h : ι → ℝ, (∀ i, |h i| ≤ A) → normalizedBoxEnergy T h ≤ B) :
    let f := boxVertex A σ
    let g := T f
    badSignMass σ g / Fintype.card ι ≤
      (B - normalizedBoxEnergy T f) / (2 * A) ∧
    (∑ i, (σ i * g i - |g i|) ^ 2) / Fintype.card ι ≤
      (2 * ‖g‖ / A) * (B - normalizedBoxEnergy T f) := by
  have hh := hB (roundedBoxVertex A σ (T (boxVertex A σ)))
    (roundedBoxVertex_mem_box hA.le hσ _)
  exact ⟨normalized_badSignMass_le_defect hTs hTp hA hσ hh,
    normalized_signResidual_sq_le_norm_defect hTs hTp hA hσ hh⟩

/-- The same estimate uses an upper bound only on the antiperiodic box. -/
theorem antiperiodic_box_rounding_defect
    {T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} (hTs : FiniteSelfAdjoint T)
    (hTp : FinitePositiveSemidefinite T) {A B : ℝ} (hA : 0 < A)
    {σ : ι → ℝ} (hσ : IsSignVector σ) (p : ι → ι)
    (hσp : ∀ i, σ (p i) = -σ i)
    (hgp : ∀ i, T (boxVertex A σ) (p i) = -T (boxVertex A σ) i)
    (hB : ∀ h : ι → ℝ, (∀ i, |h i| ≤ A) →
      (∀ i, h (p i) = -h i) → normalizedBoxEnergy T h ≤ B) :
    let f := boxVertex A σ
    let g := T f
    badSignMass σ g / Fintype.card ι ≤
      (B - normalizedBoxEnergy T f) / (2 * A) ∧
    (∑ i, (σ i * g i - |g i|) ^ 2) / Fintype.card ι ≤
      (2 * ‖g‖ / A) * (B - normalizedBoxEnergy T f) := by
  have hh := hB (roundedBoxVertex A σ (T (boxVertex A σ)))
    (roundedBoxVertex_mem_box hA.le hσ _)
    (roundedBoxVertex_antiperiodic p hσp hgp)
  exact ⟨normalized_badSignMass_le_defect hTs hTp hA hσ hh,
    normalized_signResidual_sq_le_norm_defect hTs hTp hA hσ hh⟩

/-- Positivity is needed only on the antiperiodic subspace, not on all vectors. -/
theorem antiperiodic_box_rounding_defect_on_subspace
    {T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} (hTs : FiniteSelfAdjoint T)
    {A B : ℝ} (hA : 0 < A) {σ : ι → ℝ} (hσ : IsSignVector σ) (p : ι → ι)
    (hTp : ∀ v : ι → ℝ, (∀ i, v (p i) = -v i) → 0 ≤ finitePairing v (T v))
    (hσp : ∀ i, σ (p i) = -σ i)
    (hgp : ∀ i, T (boxVertex A σ) (p i) = -T (boxVertex A σ) i)
    (hB : ∀ h : ι → ℝ, (∀ i, |h i| ≤ A) →
      (∀ i, h (p i) = -h i) → normalizedBoxEnergy T h ≤ B) :
    let f := boxVertex A σ
    let g := T f
    badSignMass σ g / Fintype.card ι ≤
      (B - normalizedBoxEnergy T f) / (2 * A) ∧
    (∑ i, (σ i * g i - |g i|) ^ 2) / Fintype.card ι ≤
      (2 * ‖g‖ / A) * (B - normalizedBoxEnergy T f) := by
  have hr := roundedBoxVertex_antiperiodic (A := A) p hσp hgp
  have hf : ∀ i, boxVertex A σ (p i) = -boxVertex A σ i := by
    intro i
    simp [boxVertex, hσp i]
  have hd : ∀ i, (roundedBoxVertex A σ (T (boxVertex A σ)) - boxVertex A σ) (p i) =
      -(roundedBoxVertex A σ (T (boxVertex A σ)) - boxVertex A σ) i := by
    intro i
    simp only [Pi.sub_apply, hr i, hf i]
    ring
  have hp : 0 ≤ boxEnergy T
      (roundedBoxVertex A σ (T (boxVertex A σ)) - boxVertex A σ) :=
    div_nonneg (hTp _ hd) (by norm_num)
  have hh := hB (roundedBoxVertex A σ (T (boxVertex A σ)))
    (roundedBoxVertex_mem_box hA.le hσ _) hr
  have hb := normalized_badSignMass_le_defect_of_nonneg hTs hA hσ hp hh
  refine ⟨hb, ?_⟩
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hnorm : ∀ i, |T (boxVertex A σ) i| ≤ ‖T (boxVertex A σ)‖ := by
    intro i
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (T (boxVertex A σ)) i
  have hs := signResidual_sq_sum_le hσ hnorm
  calc
    _ ≤ (4 * ‖T (boxVertex A σ)‖ * badSignMass σ (T (boxVertex A σ))) / Fintype.card ι :=
      div_le_div_of_nonneg_right hs hn.le
    _ = 4 * ‖T (boxVertex A σ)‖ * (badSignMass σ (T (boxVertex A σ)) / Fintype.card ι) := by ring
    _ ≤ 4 * ‖T (boxVertex A σ)‖ * ((B - normalizedBoxEnergy T (boxVertex A σ)) / (2 * A)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by field_simp; ring

end Normalized

end Erdos1045.EventualExact
