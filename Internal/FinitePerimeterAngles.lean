import FinitePerimeterNormalCones

/-! Strict normal cones become disjoint open intervals of angles, on which
the actual finite support function equals one fixed vertex projection. -/

namespace ExteriorReduction.Reinhardt

open Complex Set Metric
open Erdos1045.Configuration Erdos1045.HullGeometry
open scoped ComplexConjugate

noncomputable section

def circleDirection (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

theorem circleDirection_continuous : Continuous circleDirection := by
  unfold circleDirection
  fun_prop

theorem arg_circleDirection {t : ℝ} (ht : t ∈ Ioo (-Real.pi) Real.pi) :
    Complex.arg (circleDirection t) = t := by
  rw [circleDirection, Complex.arg_exp_mul_I]
  apply (toIocMod_eq_self Real.two_pi_pos).mpr
  exact ⟨ht.1, by linarith [ht.2]⟩

theorem conj_circleDirection (t : ℝ) :
    conj (circleDirection t) = Complex.exp (-((t : ℂ) * Complex.I)) := by
  rw [circleDirection, ← Complex.exp_conj]
  simp

theorem circleDirection_arg_mem_strictNormalCone {n : ℕ} (z : Points n) (i : Fin n)
    {u : ℂ} (hu : u ∈ strictNormalCone z i) (hu0 : u ≠ 0) :
    circleDirection u.arg ∈ strictNormalCone z i := by
  apply (strictNormalCone_smul_iff z i (norm_pos_iff.mpr hu0) _).mp
  have he : ‖u‖ • circleDirection u.arg = u := by
    simpa only [circleDirection, Complex.real_smul] using Complex.norm_mul_exp_arg_mul_I u
  rwa [he]

theorem strictNormalAngles_eq {n : ℕ} (z : Points n) (i : Fin n)
    (hne : ∃ j, z j ≠ z i) (hcut : (-1 : ℂ) ∉ strictNormalCone z i) :
    strictNormalAngles z i = Ioo (-Real.pi) Real.pi ∩ circleDirection ⁻¹' strictNormalCone z i := by
  ext t
  constructor
  · intro ht
    obtain ⟨u, hu, rfl⟩ := ht
    refine ⟨strictNormalAngles_subset z i hne hcut ⟨u, hu, rfl⟩, ?_⟩
    exact circleDirection_arg_mem_strictNormalCone z i hu
      (fun he => zero_not_mem_strictNormalCone z i hne (he ▸ hu))
  · intro ht
    exact ⟨circleDirection t, ht.2, arg_circleDirection ht.1⟩

theorem strictNormalAngles_isOpen {n : ℕ} (z : Points n) (i : Fin n)
    (hne : ∃ j, z j ≠ z i) (hcut : (-1 : ℂ) ∉ strictNormalCone z i) :
    IsOpen (strictNormalAngles z i) := by
  rw [strictNormalAngles_eq z i hne hcut]
  exact isOpen_Ioo.inter ((strictNormalCone_isOpen z i).preimage circleDirection_continuous)

theorem strictNormalAngles_disjoint {n : ℕ} (z : Points n) {i j : Fin n}
    (hij : z i ≠ z j) : Disjoint (strictNormalAngles z i) (strictNormalAngles z j) := by
  rw [Set.disjoint_left]
  rintro t ⟨u, hu, htu⟩ ⟨v, hv, htv⟩
  have hu0 : u ≠ 0 := fun he => zero_not_mem_strictNormalCone z i ⟨j, hij.symm⟩ (he ▸ hu)
  have hv0 : v ≠ 0 := fun he => zero_not_mem_strictNormalCone z j ⟨i, hij⟩ (he ▸ hv)
  have hcu := circleDirection_arg_mem_strictNormalCone z i hu hu0
  have hcv := circleDirection_arg_mem_strictNormalCone z j hv hv0
  rw [htu] at hcu
  rw [htv] at hcv
  exact Set.disjoint_left.mp (strictNormalCone_disjoint z hij) hcu hcv

theorem support_eq_of_strictNormal {n : ℕ} (z : Points n) (i : Fin n) {t : ℝ}
    (ht : circleDirection t ∈ strictNormalCone z i) :
    support z t = (z i * Complex.exp (-((t : ℂ) * Complex.I))).re := by
  refine le_antisymm ?_ (projection_le_support z i t)
  apply csSup_le ⟨_, Set.mem_range_self i⟩
  rintro _ ⟨j, rfl⟩
  by_cases hji : z j = z i
  · simp [hji]
  · have hp := ht j hji
    rw [conj_circleDirection, sub_mul, Complex.sub_re] at hp
    linarith

theorem support_eq_on_strictNormalAngles {n : ℕ} (z : Points n) (i : Fin n)
    (hne : ∃ j, z j ≠ z i) (hcut : (-1 : ℂ) ∉ strictNormalCone z i) :
    EqOn (support z) (fun t => (z i * Complex.exp (-((t : ℂ) * Complex.I))).re)
      (strictNormalAngles z i) := by
  intro t ht
  rw [strictNormalAngles_eq z i hne hcut] at ht
  exact support_eq_of_strictNormal z i ht.2

#print axioms strictNormalAngles_isOpen
#print axioms support_eq_on_strictNormalAngles

end
end ExteriorReduction.Reinhardt
