import StructuralNote.FixedDualTaylorRow9
import StructuralNote.FixedDualTaylorRow45
import StructuralNote.FixedDualTaylorRow137
import StructuralNote.FixedDualTaylorRow87
import StructuralNote.FixedDualTaylorRow12
import StructuralNote.FixedDualTaylorRow25
import StructuralNote.FixedDualTaylorRow126

/-! All thirty actual function assertions of Appendix A, tied to its original
finite table. Root existence follows, but exhaustion of the roots is separate. -/

namespace StructuralNote.FixedDualTable

open Real FixedDualPrimitive FixedDualArithmetic FixedDualIntervals
noncomputable section

def endpointSigns (r : Row) : Prop :=
  if r.rising then
    witness (signedParameter r) (left r) < 0 ∧ 0 < witness (signedParameter r) (right r)
  else
    0 < witness (signedParameter r) (left r) ∧ witness (signedParameter r) (right r) < 0

def midpointBounds (r : Row) : Prop :=
  (primitiveLower r : ℝ) < primitive (signedParameter r) (midpoint r) ∧
    primitive (signedParameter r) (midpoint r) < (primitiveUpper r : ℝ)

/-- All twenty endpoint signs and all ten primitive enclosures, without numerical premises. -/
theorem certified_table (i : Fin 10) : endpointSigns (rows i) ∧ midpointBounds (rows i) := by
  have h0 := first_and_sixth_rows
  have q0 := first_and_sixth_primitive_enclosures
  have h1 := FixedDualTaylorRow79.row79_complete
  have h2 := FixedDualTaylorRow9.row9_complete
  have h3 := FixedDualTaylorRow45.row45_complete
  have h4 := FixedDualTaylorRow137.row137_complete
  have h6 := FixedDualTaylorRow87.row87_complete
  have h7 := FixedDualTaylorRow12.row12_complete
  have h8 := FixedDualTaylorRow25.row25_complete
  have h9 := FixedDualTaylorRow126.row126_complete
  norm_num at h0 q0 h1 h2 h3 h4 h6 h7 h8 h9
  fin_cases i <;>
    norm_num [rows, endpointSigns, midpointBounds, signedParameter, left, right,
      FixedDualArithmetic.midpoint, primitiveLower, primitiveUpper]
  · exact ⟨⟨h0.1, h0.2.1⟩, q0.1, q0.2.1⟩
  · exact ⟨⟨h1.1, h1.2.1⟩, h1.2.2⟩
  · exact ⟨⟨h2.1, h2.2.1⟩, h2.2.2⟩
  · exact ⟨⟨h3.1, h3.2.1⟩, h3.2.2⟩
  · exact ⟨⟨h4.1, h4.2.1⟩, h4.2.2⟩
  · exact ⟨⟨h0.2.2.1, h0.2.2.2⟩, q0.2.2⟩
  · exact ⟨⟨h6.1, h6.2.1⟩, h6.2.2⟩
  · exact ⟨⟨h7.1, h7.2.1⟩, h7.2.2⟩
  · exact ⟨⟨h8.1, h8.2.1⟩, h8.2.2⟩
  · exact ⟨⟨h9.1, h9.2.1⟩, h9.2.2⟩

theorem row_real_domain (i : Fin 10) :
    0 < (left (rows i) : ℝ) ∧ (left (rows i) : ℝ) < (right (rows i) : ℝ) ∧
      (right (rows i) : ℝ) < Real.pi := by
  fin_cases i <;> norm_num [rows, left, right] <;> linarith [pi_gt_three]

/-- Every open interval in the table contains an actual zero. This does not assert uniqueness. -/
theorem table_root_exists (i : Fin 10) :
    ∃ u ∈ Set.Ioo (left (rows i) : ℝ) (right (rows i) : ℝ),
      witness (signedParameter (rows i)) u = 0 := by
  obtain ⟨hl, hlr, hr⟩ := row_real_domain i
  have hc : ContinuousOn (witness (signedParameter (rows i)))
      (Set.Icc (left (rows i) : ℝ) (right (rows i) : ℝ)) := by
    intro x hx
    have hx0 : 0 < x := hl.trans_le hx.1
    have hxp : x < Real.pi := hx.2.trans_lt hr
    exact (witness_hasDerivAt _ (sin_pos_of_pos_of_lt_pi hx0 hxp).ne').continuousAt.continuousWithinAt
  have hs := (certified_table i).1
  unfold endpointSigns at hs
  split_ifs at hs
  · exact intermediate_value_Ioo hlr.le hc ⟨hs.1, hs.2⟩
  · exact intermediate_value_Ioo' hlr.le hc ⟨hs.2, hs.1⟩

end
end StructuralNote.FixedDualTable
