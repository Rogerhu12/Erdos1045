import StructuralNote.FixedDualRootSigns
import StructuralNote.FixedDualIntegral
import StructuralNote.FixedDualStationaryValues

/-! The two strict bounds for the actual integral dual norms, with the full
analytic zero count, root brackets, primitive formula, and rational certificates. -/

namespace StructuralNote.FixedDualNormBounds

open Real Set MeasureTheory FixedDualPrimitive FixedDualArithmetic FixedDualRootGeometry
open FixedDualRootSigns FixedDualIntegral FixedDualStationaryValues
noncomputable section

theorem half_integral_identity :
    dualNorm (1 / 2) = Real.pi / 2 + primitive (1 / 2) (root 1) - primitive (1 / 2) (root 0) +
      primitive (-(1 / 2)) (root 3) - primitive (-(1 / 2)) (root 2) - primitive (-(1 / 2)) (root 4) := by
  obtain ⟨p0, p1, p2, p3, p4⟩ := half_positions
  obtain ⟨s0, s1, s2, s3, s4, s5, s6⟩ := half_signs
  have hp := two_root_integral (1 / 2)
    (by linarith [p0.1] : 0 < root 0) (by linarith [p0.2, p1.1] : root 0 < root 1)
    (by linarith [p1.2, pi_gt_three] : root 1 < Real.pi / 2)
    (fun u hu => (s0 u hu).le) (fun u hu => (s1 u hu).le) (fun u hu => (s2 u hu).le)
  have hn := three_root_integral (-(1 / 2))
    (by linarith [p2.1] : 0 < root 2) (by linarith [p2.2, p3.1] : root 2 < root 3)
    (by linarith [p3.2, p4.1] : root 3 < root 4)
    (by linarith [p4.2, pi_gt_three] : root 4 < Real.pi / 2)
    (fun u hu => (s3 u hu).le) (fun u hu => (s4 u hu).le)
    (fun u hu => (s5 u hu).le) (fun u hu => (s6 u hu).le)
  rw [dualNorm_split (1 / 2) hp.1 hn.1, hp.2, hn.2,
    primitive_zero, primitive_zero, primitive_pi_div_two, primitive_pi_div_two]
  ring

theorem one_integral_identity :
    dualNorm 1 = Real.pi / 2 + primitive 1 (root 6) - primitive 1 (root 5) +
      primitive (-1) (root 8) - primitive (-1) (root 7) - primitive (-1) (root 9) := by
  obtain ⟨p0, p1, p2, p3, p4⟩ := one_positions
  obtain ⟨s0, s1, s2, s3, s4, s5, s6⟩ := one_signs
  have hp := two_root_integral 1
    (by linarith [p0.1] : 0 < root 5) (by linarith [p0.2, p1.1] : root 5 < root 6)
    (by linarith [p1.2, pi_gt_three] : root 6 < Real.pi / 2)
    (fun u hu => (s0 u hu).le) (fun u hu => (s1 u hu).le) (fun u hu => (s2 u hu).le)
  have hn := three_root_integral (-1)
    (by linarith [p2.1] : 0 < root 7) (by linarith [p2.2, p3.1] : root 7 < root 8)
    (by linarith [p3.2, p4.1] : root 8 < root 9)
    (by linarith [p4.2, pi_gt_three] : root 9 < Real.pi / 2)
    (fun u hu => (s3 u hu).le) (fun u hu => (s4 u hu).le)
    (fun u hu => (s5 u hu).le) (fun u hu => (s6 u hu).le)
  rw [dualNorm_split 1 hp.1 hn.1, hp.2, hn.2,
    primitive_zero, primitive_zero, primitive_pi_div_two, primitive_pi_div_two]
  ring

theorem root_primitive_enclosure (i : Fin 10) :
    ((rows i).primitiveThousandths : ℝ) / 1000 - 13 / 40000 <
      primitive (signedParameter (rows i)) (root i) ∧
    primitive (signedParameter (rows i)) (root i) <
      (((rows i).primitiveThousandths : ℝ) + 1) / 1000 + 13 / 40000 := by
  have h := table_root_primitive_enclosure i (Ioo_subset_Icc_self (root_position i)) (root_zero i)
  simpa only [primitiveLower, primitiveUpper, Rat.cast_div, Rat.cast_add, Rat.cast_intCast,
    Rat.cast_one, Rat.cast_ofNat] using h

/-- The first strict bound in (8.5), for the actual integral rather than a table surrogate. -/
theorem half_dualNorm_bound : dualNorm (1 / 2) < 49059 / 56000 ∧ dualNorm (1 / 2) < 9 / 10 := by
  let q : Fin 5 → ℝ := fun i => primitive (signedParameter (rows ⟨i, by omega⟩)) (root ⟨i, by omega⟩)
  apply half_budget_from_primitive_enclosures q
  · have h := half_integral_identity
    norm_num [q, rows, signedParameter] at h ⊢
    exact h
  · intro i
    exact root_primitive_enclosure ⟨i, by omega⟩

/-- The second strict bound in (8.5), with no numerical or root-count hypotheses. -/
theorem one_dualNorm_bound : dualNorm 1 < 67819 / 56000 ∧ dualNorm 1 < 97 / 80 := by
  let q : Fin 5 → ℝ := fun i => primitive (signedParameter (rows ⟨i + 5, by omega⟩)) (root ⟨i + 5, by omega⟩)
  apply one_budget_from_primitive_enclosures q
  · have h := one_integral_identity
    change dualNorm 1 = Real.pi / 2 +
      primitive (signedParameter (rows ⟨6, by omega⟩)) (root ⟨6, by omega⟩) -
      primitive (signedParameter (rows ⟨5, by omega⟩)) (root ⟨5, by omega⟩) +
      primitive (signedParameter (rows ⟨8, by omega⟩)) (root ⟨8, by omega⟩) -
      primitive (signedParameter (rows ⟨7, by omega⟩)) (root ⟨7, by omega⟩) -
      primitive (signedParameter (rows ⟨9, by omega⟩)) (root ⟨9, by omega⟩)
    norm_num [rows, signedParameter] at h ⊢
    exact h
  · intro i
    exact root_primitive_enclosure ⟨i + 5, by omega⟩

end
end StructuralNote.FixedDualNormBounds
