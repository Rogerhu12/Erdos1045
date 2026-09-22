import Erdos1045.HullGeometry
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace Erdos1045.HullGeometry

open Configuration
noncomputable section

theorem hullPerimeter_perm_proved (n : ℕ) (z : Points n) (σ : Equiv.Perm (Fin n)) :
    hullPerimeter (z ∘ σ) = hullPerimeter z := by
  unfold hullPerimeter support
  congr 1
  funext t
  congr 1
  ext x
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨σ i, hi⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨j, rfl⟩ := σ.surjective i
    exact ⟨j, rfl⟩

theorem support_joint_continuous (n : ℕ) :
    Continuous (fun p : Points n × ℝ => support p.1 p.2) := by
  have hf : Continuous (fun p : (Points n × ℝ) × Fin n =>
      (p.1.1 p.2 * Complex.exp (-((p.1.2 : ℂ) * Complex.I))).re) := by
    apply continuous_prod_of_discrete_right.mpr
    intro i
    change Continuous (fun p : Points n × ℝ =>
      (p.1 i * Complex.exp (-((p.2 : ℂ) * Complex.I))).re)
    fun_prop
  have h := (isCompact_univ : IsCompact (Set.univ : Set (Fin n))).continuous_sSup
    (f := fun p : Points n × ℝ => fun i : Fin n =>
      (p.1 i * Complex.exp (-((p.2 : ℂ) * Complex.I))).re) hf
  simpa [support, Set.image_univ] using h

theorem hullPerimeter_continuous_proved (n : ℕ) : Continuous (@hullPerimeter n) := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (support_joint_continuous n) 0 (2 * Real.pi)

end
end Erdos1045.HullGeometry
