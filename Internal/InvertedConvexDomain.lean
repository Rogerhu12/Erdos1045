import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

/-!
# Inverting the complement of a compact convex set

The chosen point may lie on the boundary, so the inverted domain need not
be bounded. It is nevertheless open, proper, and star convex about zero.
This also covers a nondegenerate segment without a separate Joukowski case.
-/

namespace ExteriorReduction

open Complex Set Metric Filter
open scoped Topology

def invertedComplement (K : Set ℂ) (z : ℂ) : Set ℂ :=
  {w | w = 0 ∨ z + w⁻¹ ∉ K}

@[simp] theorem zero_mem_invertedComplement (K : Set ℂ) (z : ℂ) :
    (0 : ℂ) ∈ invertedComplement K z := Or.inl rfl

theorem invertedComplement_starConvex {K : Set ℂ} {z : ℂ}
    (hK : Convex ℝ K) (hz : z ∈ K) : StarConvex ℝ 0 (invertedComplement K z) := by
  intro w hw a b ha hb hab
  simp only [smul_zero, zero_add]
  by_cases hw0 : w = 0
  · simp [hw0]
  by_cases hb0 : b = 0
  · simp [hb0]
  have hwout : z + w⁻¹ ∉ K := hw.resolve_left hw0
  right
  intro hinside
  apply hwout
  have hp := hK hz hinside ha hb hab
  have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb0
  convert hp using 1
  simp only [Complex.real_smul]
  have habC : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
  field_simp
  linear_combination -(w * z) * habC

theorem invertedComplement_simplyConnected {K : Set ℂ} {z : ℂ}
    (hK : Convex ℝ K) (hz : z ∈ K) : IsSimplyConnected (invertedComplement K z) := by
  let := (invertedComplement_starConvex hK hz).contractibleSpace
    (show (invertedComplement K z).Nonempty from ⟨0, zero_mem_invertedComplement K z⟩)
  exact SimplyConnectedSpace.ofContractible _

theorem invertedComplement_ne_univ {K : Set ℂ} {z y : ℂ}
    (hy : y ∈ K) (hyz : y ≠ z) : invertedComplement K z ≠ univ := by
  intro heq
  have hmem : (y - z)⁻¹ ∈ invertedComplement K z := by rw [heq]; trivial
  rcases hmem with hzero | hout
  · exact hyz (sub_eq_zero.mp (inv_eq_zero.mp hzero))
  · apply hout
    simpa only [inv_inv, add_sub_cancel] using hy

theorem invertedComplement_isOpen {K : Set ℂ} (hK : IsCompact K) (z : ℂ) :
    IsOpen (invertedComplement K z) := by
  rw [isOpen_iff_mem_nhds]
  intro w hw
  by_cases hw0 : w = 0
  · subst w
    obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
    let S := |R| + ‖z‖ + 1
    have hS : 0 < S := by dsimp [S]; positivity
    apply mem_of_superset (ball_mem_nhds (0 : ℂ) (show 0 < 1 / S by positivity))
    intro w hw
    by_cases hw0 : w = 0
    · exact Or.inl hw0
    right
    intro hinside
    have hlarge : ‖w⁻¹‖ ≤ R + ‖z‖ := by
      calc
        ‖w⁻¹‖ = ‖(z + w⁻¹) - z‖ := by congr 1; ring
        _ ≤ ‖z + w⁻¹‖ + ‖z‖ := norm_sub_le _ _
        _ ≤ R + ‖z‖ := add_le_add (hR _ hinside) le_rfl
    have hsmall : ‖w‖ * S < 1 :=
      (lt_div_iff₀ hS).mp (mem_ball_zero_iff.mp hw)
    have hid : ‖w‖ * ‖w⁻¹‖ = 1 := by rw [← norm_mul, mul_inv_cancel₀ hw0, norm_one]
    have hmul := mul_le_mul_of_nonneg_left hlarge (norm_nonneg w)
    have hRabs : R ≤ |R| := le_abs_self R
    have hpositive : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    dsimp [S] at hsmall
    nlinarith
  · have hout : z + w⁻¹ ∉ K := hw.resolve_left hw0
    have hcont : ContinuousAt (fun u : ℂ => z + u⁻¹) w :=
      continuousAt_const.add (continuousAt_id.inv₀ hw0)
    have hevent : ∀ᶠ u in 𝓝 w, z + u⁻¹ ∉ K :=
      hcont.preimage_mem_nhds (hK.isClosed.isOpen_compl.mem_nhds hout)
    exact mem_of_superset hevent (fun u hu => Or.inr hu)

#print axioms invertedComplement_starConvex
#print axioms invertedComplement_simplyConnected
#print axioms invertedComplement_isOpen

end ExteriorReduction
