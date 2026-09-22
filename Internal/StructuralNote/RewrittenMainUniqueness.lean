import StructuralNote.FixedSchurActualRigidEquivalence
import StructuralNote.ReusedEvenLift

/-! Euclidean uniqueness of the literal maximizers in both problems. -/

namespace StructuralNote.RewrittenMainUniqueness

open Erdos1045 Erdos1045.Configuration Erdos1045.EventualExact Erdos1045.HullGeometry
open FixedSchurActualRigidEquivalence
noncomputable section

theorem regular_equal_discriminant_directRigid {n : ℕ} (hn : 3 ≤ n)
    (z w : Points n) (hz : Configuration.IsRegular z) (hw : Configuration.IsRegular w)
    (hd : discriminant z = discriminant w) : DirectRigidRelabeling z w := by
  obtain ⟨a, b, _, π, hz⟩ := hz
  obtain ⟨c, d, hd0, τ, hw⟩ := hw
  have hDz : discriminant z = ‖b‖ ^ exponent n * (n : ℝ)^n := by
    rw [show z = fun j => a + b * regular n (π j) from funext hz,
      discriminant_affine]
    rw [show discriminant (fun j => regular n (π j)) = discriminant (regular n) from
      HullGeometry.discriminant_perm (regular n) π,
      ClosedRegularGeometry.regular_discriminant n hn]
  have hDw : discriminant w = ‖d‖ ^ exponent n * (n : ℝ)^n := by
    rw [show w = fun j => c + d * regular n (τ j) from funext hw,
      discriminant_affine]
    rw [show discriminant (fun j => regular n (τ j)) = discriminant (regular n) from
      HullGeometry.discriminant_perm (regular n) τ,
      ClosedRegularGeometry.regular_discriminant n hn]
  have hscale : ‖b‖ = ‖d‖ := by
    have hn0 : (n : ℝ)^n ≠ 0 := pow_ne_zero _ (by positivity)
    have hpow : ‖b‖ ^ exponent n = ‖d‖ ^ exponent n :=
      mul_right_cancel₀ hn0 (hDz.symm.trans (hd.trans hDw))
    exact (pow_left_inj₀ (norm_nonneg b) (norm_nonneg d)
      (Nat.mul_ne_zero (by omega) (by omega) : exponent n ≠ 0)).mp hpow
  refine ⟨τ.trans π.symm, a - (b / d) * c, b / d, ?_, ?_⟩
  · rw [norm_div, hscale, div_self (norm_ne_zero_iff.mpr hd0)]
  · intro j
    change z (π.symm (τ j)) = _
    rw [hz, Equiv.apply_symm_apply, hw]
    field_simp
    ring

theorem eventual_diameter_extremizers_unique :
    ∃ n₀ : ℕ, 4 ≤ n₀ ∧ ∀ n ≥ n₀, ∀ z w : Points n,
      ExtremalNormalization.DiameterExtremal z →
      ExtremalNormalization.DiameterExtremal w → DirectRigidRelabeling z w := by
  obtain ⟨n₁, hn₁, hodd⟩ := eventual_odd_maximizer_regular
  obtain ⟨m₀, heven⟩ := eventual_actual_extremizers_directRigid
  refine ⟨max n₁ (2 * m₀), by omega, ?_⟩
  intro n hn z w hz hw
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨m, hm⟩ := he
    have hnEq : n = 2 * m := by omega
    clear hm
    subst n
    exact heven m (by omega) z w hz hw
  · have hMz : discriminant z = M n :=
      ((M_eq_verified_diameterMaximum n).trans
        (WholeBoxLowerBound.diameterMaximum_eq_of_extremal hz)).symm
    have hMw : discriminant w = M n :=
      ((M_eq_verified_diameterMaximum n).trans
        (WholeBoxLowerBound.diameterMaximum_eq_of_extremal hw)).symm
    exact regular_equal_discriminant_directRigid (by omega) z w
      (hodd n (by omega) ho z hz.1 hMz) (hodd n (by omega) ho w hw.1 hMw)
      (hMz.trans hMw.symm)

theorem eventual_perimeter_maximizers_unique :
    ∃ n₀ : ℕ, 4 ≤ n₀ ∧ ∀ n ≥ n₀, ∀ z w : Points n,
      hullPerimeter z ≤ 2 * Real.pi → discriminant z = W n →
      hullPerimeter w ≤ 2 * Real.pi → discriminant w = W n →
        DirectRigidRelabeling z w := by
  obtain ⟨n₀, hn₀, hreg⟩ := eventual_perimeter_maximizer_regular
  refine ⟨n₀, hn₀, ?_⟩
  intro n hn z w hz hDz hw hDw
  exact regular_equal_discriminant_directRigid (by omega) z w
    (hreg n hn z hz hDz) (hreg n hn w hw hDw) (hDz.trans hDw.symm)

end
end StructuralNote.RewrittenMainUniqueness
