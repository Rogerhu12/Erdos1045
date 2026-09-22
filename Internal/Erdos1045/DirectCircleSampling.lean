import Erdos1045.FourierDefinitions
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Disjoint-interval sampling from the fundamental theorem of calculus -/

namespace Erdos1045.FaberFourier

open MeasureTheory Set
open scoped BigOperators
noncomputable section

theorem integral_norm_sq_le_length_mul {g : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hg : IntegrableOn g (Ioc a b))
    (hg2 : IntegrableOn (fun x => ‖g x‖ ^ 2) (Ioc a b)) :
    (∫ x in Ioc a b, ‖g x‖) ^ 2 ≤
      (b - a) * ∫ x in Ioc a b, ‖g x‖ ^ 2 := by
  let L := b - a
  let N := ∫ x in Ioc a b, ‖g x‖
  have hL : 0 < L := sub_pos.mpr hab
  have hp : 0 ≤ ∫ x in Ioc a b,
      (L ^ 2 * ‖g x‖ ^ 2 - (2 * L * N) * ‖g x‖) + N ^ 2 := by
    apply integral_nonneg
    intro x
    change 0 ≤ L ^ 2 * ‖g x‖ ^ 2 - 2 * L * N * ‖g x‖ + N ^ 2
    nlinarith [sq_nonneg (L * ‖g x‖ - N)]
  have heq := integral_add ((hg2.const_mul (L ^ 2)).sub (hg.norm.const_mul (2 * L * N)))
    (integrable_const (N ^ 2))
  simp only [Pi.sub_apply] at heq
  rw [heq, integral_sub (hg2.const_mul (L ^ 2)) (hg.norm.const_mul (2 * L * N)), integral_const_mul,
    integral_const_mul, setIntegral_const, Real.volume_real_Ioc_of_le hab.le,
    smul_eq_mul] at hp
  have hh : 0 ≤ L * (L * (∫ x in Ioc a b, ‖g x‖ ^ 2) - N ^ 2) := by
    dsimp [L, N] at hp ⊢
    nlinarith [hp]
  have := nonneg_of_mul_nonneg_right hh hL
  dsimp [L, N] at this
  linarith

theorem CircleH1.local_difference_bound (f : CircleH1) {a b s t : ℝ}
    (hab : a < b) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hd2 : IntegrableOn (fun x => ‖f.weakDerivative x‖ ^ 2) (Ioc a b)) :
    ‖f.value t - f.value s‖ ^ 2 ≤
      (b - a) * ∫ x in Ioc a b, ‖f.weakDerivative x‖ ^ 2 := by
  have hd : IntegrableOn f.weakDerivative (Ioc a b) :=
    (f.derivative_locally_integrable.integrableOn_isCompact isCompact_Icc).mono_set
      Ioc_subset_Icc_self
  have hsub : uIoc s t ⊆ Ioc a b := by
    intro x hx
    exact ⟨lt_of_le_of_lt (le_min hs.1 ht.1) hx.1,
      le_trans hx.2 (max_le hs.2 ht.2)⟩
  have hb : ‖f.value t - f.value s‖ ≤ ∫ x in Ioc a b, ‖f.weakDerivative x‖ := by
    rw [f.fundamental_identity]
    exact intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
      (setIntegral_mono_set hd.norm (Filter.Eventually.of_forall fun x => norm_nonneg _)
        (Filter.Eventually.of_forall hsub))
  exact (sq_le_sq₀ (norm_nonneg _) (integral_nonneg fun x => norm_nonneg _)).mpr hb |>.trans
    (integral_norm_sq_le_length_mul hab hd hd2)

theorem CircleH1.local_sampling (f : CircleH1) {a b t : ℝ}
    (hab : a < b) (ht : t ∈ Icc a b)
    (hf2 : IntegrableOn (fun x => ‖f.value x‖ ^ 2) (Ioc a b))
    (hd2 : IntegrableOn (fun x => ‖f.weakDerivative x‖ ^ 2) (Ioc a b)) :
    ‖f.value t‖ ^ 2 ≤
      2 / (b - a) * (∫ x in Ioc a b, ‖f.value x‖ ^ 2) +
      2 * (b - a) * (∫ x in Ioc a b, ‖f.weakDerivative x‖ ^ 2) := by
  let D := ∫ x in Ioc a b, ‖f.weakDerivative x‖ ^ 2
  have hp (x : ℝ) (hx : x ∈ Ioc a b) :
      ‖f.value t‖ ^ 2 ≤ 2 * ‖f.value x‖ ^ 2 + 2 * (b - a) * D := by
    have hd := f.local_difference_bound hab ⟨hx.1.le, hx.2⟩ ht hd2
    have hn : ‖f.value t‖ ≤ ‖f.value x‖ + ‖f.value t - f.value x‖ := by
      calc
        ‖f.value t‖ = ‖f.value x + (f.value t - f.value x)‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    have hn2 := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hn
    dsimp [D]
    nlinarith [sq_nonneg (‖f.value x‖ - ‖f.value t - f.value x‖)]
  have hi := integral_mono_ae (μ := volume.restrict (Ioc a b))
    (integrable_const (‖f.value t‖ ^ 2)) ((hf2.const_mul 2).add (integrable_const (2 * (b - a) * D)))
    ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall hp))
  simp only [Pi.add_apply] at hi
  rw [setIntegral_const, Real.volume_real_Ioc_of_le hab.le, smul_eq_mul,
    integral_add (hf2.const_mul 2) (integrable_const (2 * (b - a) * D)), integral_const_mul,
    setIntegral_const, Real.volume_real_Ioc_of_le hab.le, smul_eq_mul] at hi
  calc
    ‖f.value t‖ ^ 2 ≤
        (2 * (∫ x in Ioc a b, ‖f.value x‖ ^ 2) +
          (b - a) * (2 * (b - a) * D)) / (b - a) :=
      (le_div_iff₀ (sub_pos.mpr hab)).mpr (by nlinarith [hi])
    _ = _ := by
      dsimp [D]
      field_simp

theorem CircleH1.sampling_of_intervals (f : CircleH1) {n : ℕ}
    (θ a b : Fin n → ℝ) {L : ℝ} (hL : 0 < L)
    (hlen : ∀ j, b j - a j = L) (hnode : ∀ j, θ j ∈ Icc (a j) (b j))
    (hsub : ∀ j, Ioc (a j) (b j) ⊆ Ioc 0 (2 * Real.pi))
    (hdis : Pairwise (fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j)))) :
    (∑ j, ‖f.value (θ j)‖ ^ 2) ≤
      (2 / L) * energy f.value + 2 * L * energy f.weakDerivative := by
  have hab (j : Fin n) : a j < b j := sub_pos.mp ((hlen j).symm ▸ hL)
  have hF : IntegrableOn (fun x => ‖f.value x‖ ^ 2) (Ioc 0 (2 * Real.pi)) :=
    f.square_integrable_value
  have hD : IntegrableOn (fun x => ‖f.weakDerivative x‖ ^ 2) (Ioc 0 (2 * Real.pi)) :=
    f.square_integrable_derivative
  have hf (j : Fin n) : IntegrableOn (fun x => ‖f.value x‖ ^ 2) (Ioc (a j) (b j)) :=
    hF.mono_set (hsub j)
  have hd (j : Fin n) : IntegrableOn (fun x => ‖f.weakDerivative x‖ ^ 2) (Ioc (a j) (b j)) :=
    hD.mono_set (hsub j)
  have hsum (g : ℝ → ℂ) (hg : Integrable (fun x => ‖g x‖ ^ 2) circleMeasure) :
      (∑ j, ∫ x in Ioc (a j) (b j), ‖g x‖ ^ 2) ≤ energy g := by
    change IntegrableOn (fun x => ‖g x‖ ^ 2) (Ioc 0 (2 * Real.pi)) at hg
    rw [← integral_iUnion_fintype (fun j => measurableSet_Ioc) hdis
      (fun j => hg.mono_set (hsub j))]
    apply setIntegral_mono_set hg (Filter.Eventually.of_forall fun x => sq_nonneg _)
    exact Filter.Eventually.of_forall (iUnion_subset hsub)
  calc
    (∑ j, ‖f.value (θ j)‖ ^ 2) ≤
        (∑ j, ((2 / L) * (∫ x in Ioc (a j) (b j), ‖f.value x‖ ^ 2) +
          2 * L * (∫ x in Ioc (a j) (b j), ‖f.weakDerivative x‖ ^ 2))) := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [hlen] using f.local_sampling (hab j) (hnode j) (hf j) (hd j)
    _ = (2 / L) * (∑ j, ∫ x in Ioc (a j) (b j), ‖f.value x‖ ^ 2) +
        2 * L * (∑ j, ∫ x in Ioc (a j) (b j), ‖f.weakDerivative x‖ ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (hsum _ f.square_integrable_value) (by positivity))
      (mul_le_mul_of_nonneg_left (hsum _ f.square_integrable_derivative) (by positivity))

theorem circle_sampling_proved :
    ∀ γ : ℝ, 0 < γ → ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ), 0 < n → ∀ θ : Fin n → ℝ, Separated θ γ → H1Sampling θ C := by
  intro γ hγ
  let δ := min γ Real.pi
  have hδ : 0 < δ := lt_min hγ Real.pi_pos
  refine ⟨8 / δ + δ, by positivity, ?_⟩
  intro n hn θ hsep f
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let L := δ / (4 * n)
  have hL : 0 < L := div_pos hδ (by positivity)
  have hLn : L * (4 * n) = δ := div_mul_cancel₀ δ (by positivity)
  have hδπ : δ ≤ Real.pi := min_le_right _ _
  have hδγ : δ ≤ γ := min_le_left _ _
  have hLπ : L ≤ Real.pi := by
    nlinarith [mul_nonneg hL.le (sub_nonneg.mpr hn1)]
  have hLγ : 4 * L ≤ γ / n := by
    apply (le_div_iff₀ hn0).mpr
    nlinarith [hLn]
  let a : Fin n → ℝ := fun j => if θ j ≤ Real.pi then θ j else θ j - L
  let b : Fin n → ℝ := fun j => a j + L
  have hlen (j : Fin n) : b j - a j = L := by dsimp [b]; ring
  have hnode (j : Fin n) : θ j ∈ Icc (a j) (b j) := by
    dsimp [a, b]
    split_ifs <;> constructor <;> linarith
  have hsub (j : Fin n) : Ioc (a j) (b j) ⊆ Ioc 0 (2 * Real.pi) := by
    have hrange := hsep.1 j
    intro x hx
    dsimp [a, b] at hx
    split_ifs at hx with hθ <;> constructor <;> linarith [hrange.1, hrange.2, hx.1, hx.2]
  have hdis : Pairwise (fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    have hxi' : |θ i - x| ≤ L := by
      apply abs_le.mpr
      constructor <;> linarith [(hnode i).1, (hnode i).2, hlen i, hxi.1, hxi.2]
    have hxj' : |x - θ j| ≤ L := by
      apply abs_le.mpr
      constructor <;> linarith [(hnode j).1, (hnode j).2, hlen j, hxj.1, hxj.2]
    have hfar : γ / n ≤ |θ i - θ j| := (hsep.2 i j hij).trans (min_le_left _ _)
    have htriangle := abs_sub_le (θ i) x (θ j)
    linarith
  have hb := f.sampling_of_intervals θ a b hL hlen hnode hsub hdis
  have hE : 0 ≤ energy f.value := integral_nonneg fun x => sq_nonneg _
  have hD : 0 ≤ energy f.weakDerivative := integral_nonneg fun x => sq_nonneg _
  have heq : (2 / L) * energy f.value + 2 * L * energy f.weakDerivative =
      (8 / δ) * ((n : ℝ) * energy f.value) + (δ / 2) * (energy f.weakDerivative / n) := by
    dsimp [L]
    field_simp
    ring
  rw [heq] at hb
  apply hb.trans
  have hC1 : 8 / δ ≤ 8 / δ + δ := le_add_of_nonneg_right hδ.le
  have hC2 : δ / 2 ≤ 8 / δ + δ := by
    have : 0 ≤ 8 / δ := by positivity
    linarith
  calc
    (8 / δ) * ((n : ℝ) * energy f.value) + (δ / 2) * (energy f.weakDerivative / n) ≤
        (8 / δ + δ) * ((n : ℝ) * energy f.value) +
          (8 / δ + δ) * (energy f.weakDerivative / n) :=
      add_le_add (mul_le_mul_of_nonneg_right hC1 (mul_nonneg hn0.le hE))
        (mul_le_mul_of_nonneg_right hC2 (div_nonneg hD hn0.le))
    _ = _ := by ring

end
end Erdos1045.FaberFourier
