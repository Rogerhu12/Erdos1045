import StructuralNote.LocalizedThreeArcDichotomy
import StructuralNote.ThreeArcSignAssembly
import StructuralNote.ThreeTransitionReconstruction
import StructuralNote.ThreeArcBlockLengths

/-! Three actual localized transitions determine a genuine canonical word,
with its block lengths in the fixed kernel interval. -/

namespace StructuralNote.ThreeArcCanonicalWord

open Real Set Erdos1045.EventualExact FiniteBox
open SignPatternSymmetry FixedDualClassificationExteriorGaps FixedDualClassificationArcGrid
open FiniteCompressionStandardArcs ThreeArcSignAssembly ThreeTransitionReconstruction
open ThreeArcBlockLengths LocalizedThreeArcDichotomy SolThreeBlockWord ThreeBlockKernelMargin
noncomputable section

theorem three_arcs_reconstruct {m : ℕ} (hm : 0 < m) (s : SignPattern hm) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβhi : β ≤ gridStep m) (hstep : gridStep m ≤ (Real.pi - 3) / 24)
    (hs : LocalizedSigns hm s β) (ht : ThreeTransitions hm s β) :
    ∃ k a b c : ℕ, ∃ hp : 0 < a ∧ 0 < b ∧ 0 < c, ∃ hsum : a + b + c = m,
      globalNegate (rotatePattern k s) = threeBlockPattern hm hp hsum ∧
      angle m a ∈ Icc (Real.pi / 4) (5 * Real.pi / 12) ∧
      angle m b ∈ Icc (Real.pi / 4) (5 * Real.pi / 12) ∧
      angle m c ∈ Icc (Real.pi / 4) (5 * Real.pi / 12) := by
  obtain ⟨⟨a, ha, hsa⟩, ⟨b, hb, hsb⟩, ⟨c, hc, hsc⟩⟩ := ht
  obtain ⟨h01, h12, h11, h23, h22, hlast, _⟩ := standard_arc_order hm hβ0 hβhi hstep
  have hex := standard_exteriorSigns hm s hβ0 hstep hs
  obtain ⟨hLa, hab, hbc, hcm, hpattern⟩ :=
    three_arc_sign_formula hm s h01 h12 h11 h23 h22 hlast hex ha hb hc hsa hsb hsc
  obtain ⟨hp, hsum, heq⟩ := three_transition_reconstruction hm s hLa hab hbc hcm hpattern
  have hangle := three_arc_block_angle_bounds hm hβ0 hβhi hstep ha hb hc
  exact ⟨a + 1, b - a, c - b, m + a - c, hp, hsum, heq, hangle⟩

end
end StructuralNote.ThreeArcCanonicalWord
