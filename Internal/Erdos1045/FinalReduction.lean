import Erdos1045.AnalyticFamily
import Erdos1045.ExteriorLocalBridge
import Erdos1045.DiameterReduction

/-!
# From every extremal sequence to a uniform threshold and the diameter problem

The family-regularity premise below is an ordinary intermediate conclusion of
the analytic proof. It is never added to a classical theorem interface. The
remaining arguments are selection of a counterexample sequence, relabeling,
and exact homogeneity of the finite distance product.
-/

namespace Erdos1045.GlobalProof

open Configuration HullGeometry ExteriorClassical Filter
open scoped Topology
noncomputable section

theorem isRegular_of_perm {n : ℕ} (z : Points n) (σ : Equiv.Perm (Fin n))
    (hz : Configuration.IsRegular (z ∘ σ)) : Configuration.IsRegular z := by
  obtain ⟨a, b, hb, τ, hτ⟩ := hz
  refine ⟨a, b, hb, σ.symm.trans τ, ?_⟩
  intro j
  simpa only [Function.comp_apply, Equiv.apply_symm_apply, Equiv.trans_apply] using hτ (σ.symm j)

theorem eventual_regular_extremals (B : ClassicalAnalysis) (HE : ClassicalExteriorExistence)
    (hfamilies : ∀ s : ExtremalFamily,
      ∀ᶠ j in atTop, Configuration.IsRegular (s.points j)) :
    ∃ M : ℕ, 4 ≤ M ∧ ∀ n : ℕ, M ≤ n → Odd n →
      ∀ z : Points n, PerimeterExtremal n z → Configuration.IsRegular z := by
  classical
  by_contra! hbad
  have hchoose (j : ℕ) : ∃ n : ℕ, max 4 j ≤ n ∧ Odd n ∧
      ∃ z : Points n, PerimeterExtremal n z ∧ ¬ Configuration.IsRegular z :=
    hbad (max 4 j) (le_max_left _ _)
  choose N hN hodd z hz hnonreg using hchoose
  have hN4 (j : ℕ) : 4 ≤ N j := (le_max_left _ _).trans (hN j)
  have hNj (j : ℕ) : j ≤ N j := (le_max_right _ _).trans (hN j)
  have hNtop : Tendsto N atTop atTop := tendsto_atTop_mono hNj tendsto_id
  have hmodel (j : ℕ) : ∃ σ : Equiv.Perm (Fin (N j)), Nonempty
      {d : ExteriorData (z j ∘ σ) // FaberIdentities d} := by
    apply HE.model (N j) (by have := hN4 j; omega) (z j)
    · exact perimeterExtremal_injective B.geometry (by have := hN4 j; omega) (hz j)
    · exact perimeterExtremal_perimeter_eq B.geometry (by have := hN4 j; omega) (hz j)
    · exact ExteriorLocalBridge.perimeterExtremal_fekete B.geometry (hz j)
  choose σ hdata using hmodel
  let chosen (j : ℕ) := Classical.choice (hdata j)
  let s : ExtremalFamily :=
    { size := N
      size_ge := hN4
      size_odd := hodd
      size_tendsto := hNtop
      points := fun j => z j ∘ σ j
      maximal := fun j => perimeterExtremal_perm B.geometry (hz j) (σ j)
      data := fun j => (chosen j).val
      identities := fun j => (chosen j).property }
  obtain ⟨j, hj⟩ := (hfamilies s).exists
  exact hnonreg j (isRegular_of_perm (z j) (σ j) hj)

def diameterTwoMaximum (n : ℕ) : ℝ :=
  (n : ℝ) ^ n / Real.cos (Real.pi / (2 * n)) ^ exponent n

def diameterTwoRegular (n : ℕ) : Points n := fun i => (2 : ℂ) * unitRegular n i

theorem diameterTwoRegular_coordinates {n : ℕ} (j : Fin n) :
    diameterTwoRegular n j =
      (((1 / Real.cos (Real.pi / (2 * n))) : ℝ) : ℂ) * regular n j := by
  unfold diameterTwoRegular unitRegular
  push_cast
  field_simp

theorem half_scale_maximum (n : ℕ) :
    (1 / 2 : ℝ) ^ exponent n * diameterTwoMaximum n = diameterMaximum n := by
  unfold diameterTwoMaximum diameterMaximum
  rw [mul_pow, div_pow, one_pow]
  ring

theorem diameter_two_bound_of_regular_extremals (H : ClassicalHullGeometry)
    {n : ℕ} (hn : 3 ≤ n)
    (hregular : ∀ z : Points n, PerimeterExtremal n z → Configuration.IsRegular z)
    (z : Points n) (hz : DiameterAtMost 2 z) :
    discriminant z ≤ diameterTwoMaximum n := by
  let w : Points n := fun i => (1 / 2 : ℂ) * z i
  have hw : DiameterAtMost 1 w := by
    have h := diameter_affine hz 0 (1 / 2 : ℂ)
    norm_num at h
    exact h
  have hD : discriminant w = (1 / 2 : ℝ) ^ exponent n * discriminant z := by
    have h := discriminant_affine z 0 (1 / 2 : ℂ)
    norm_num only [zero_add, norm_div, norm_one, Complex.norm_ofNat] at h
    exact h
  have hb := diameter_bound_of_regular_extremals H hn hregular w hw
  rw [hD, ← half_scale_maximum n] at hb
  exact le_of_mul_le_mul_left hb (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) _)

theorem diameter_two_equality_isRegular (H : ClassicalHullGeometry)
    {n : ℕ} (hn : 3 ≤ n)
    (hregular : ∀ z : Points n, PerimeterExtremal n z → Configuration.IsRegular z)
    (z : Points n) (hz : DiameterAtMost 2 z) (hD : discriminant z = diameterTwoMaximum n) :
    Configuration.IsRegular z := by
  let w : Points n := fun i => (1 / 2 : ℂ) * z i
  have hw : DiameterAtMost 1 w := by
    have h := diameter_affine hz 0 (1 / 2 : ℂ)
    norm_num at h
    exact h
  have hwD : discriminant w = diameterMaximum n := by
    have h := discriminant_affine z 0 (1 / 2 : ℂ)
    norm_num only [zero_add, norm_div, norm_one, Complex.norm_ofNat] at h
    change discriminant w = _ at h
    rw [h, hD, half_scale_maximum]
  have hwreg := diameter_equality_isRegular H hn hregular w hw hwD
  apply isRegular_of_affine z 0 (1 / 2 : ℂ) (by norm_num)
  simpa only [zero_add] using hwreg

theorem diameterTwoRegular_diameter (H : ClassicalHullGeometry) {n : ℕ}
    (hn : 3 ≤ n) (hodd : Odd n) : DiameterAtMost 2 (diameterTwoRegular n) := by
  have h := diameter_affine (unitRegular_diameter H hn hodd) 0 (2 : ℂ)
  norm_num at h
  exact h

theorem diameterTwoRegular_discriminant (H : ClassicalHullGeometry) {n : ℕ}
    (hn : 3 ≤ n) : discriminant (diameterTwoRegular n) = diameterTwoMaximum n := by
  have h := discriminant_affine (unitRegular n) 0 (2 : ℂ)
  norm_num only [zero_add, Complex.norm_ofNat] at h
  change discriminant (diameterTwoRegular n) = _ at h
  rw [h, unitRegular_discriminant H hn]
  rw [← half_scale_maximum n, ← mul_assoc, ← mul_pow]
  norm_num

/-- The diameter-two statement in the normalization used by the manuscript.
Its sole nonclassical premise is the intermediate family rigidity result,
which the analytic main theorem supplies. -/
theorem eventual_diameter_two_maximum (B : ClassicalAnalysis) (HE : ClassicalExteriorExistence)
    (hfamilies : ∀ s : ExtremalFamily,
      ∀ᶠ j in atTop, Configuration.IsRegular (s.points j)) :
    ∃ M : ℕ, 4 ≤ M ∧ ∀ n : ℕ, M ≤ n → Odd n →
      (∀ z : Points n, DiameterAtMost 2 z → discriminant z ≤ diameterTwoMaximum n) ∧
      (DiameterAtMost 2 (diameterTwoRegular n) ∧
        discriminant (diameterTwoRegular n) = diameterTwoMaximum n) ∧
      (∀ z : Points n, DiameterAtMost 2 z → discriminant z = diameterTwoMaximum n →
        Configuration.IsRegular z) := by
  obtain ⟨M, hM, hregular⟩ := eventual_regular_extremals B HE hfamilies
  refine ⟨M, hM, ?_⟩
  intro n hn hodd
  have hn3 : 3 ≤ n := by omega
  exact ⟨fun z hz => diameter_two_bound_of_regular_extremals B.geometry hn3 (hregular n hn hodd) z hz,
    ⟨diameterTwoRegular_diameter B.geometry hn3 hodd,
      diameterTwoRegular_discriminant B.geometry hn3⟩,
    fun z hz hD => diameter_two_equality_isRegular B.geometry hn3 (hregular n hn hodd) z hz hD⟩

end
end Erdos1045.GlobalProof
