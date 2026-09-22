import ExteriorExistence

/-!
# Positive derivative normalization of the inverted exterior model

The rotation is constructed explicitly from the inverse map's nonzero derivative.
No boundary regularity or further existence theorem is assumed.
-/

namespace ExteriorReduction

open Complex ComplexConjugate Set Metric Function

noncomputable section

def positivePhase (d : ℂ) : ℂ := conj d / (‖d‖ : ℂ)

theorem positivePhase_norm {d : ℂ} (hd : d ≠ 0) : ‖positivePhase d‖ = 1 := by
  simp [positivePhase, hd]

theorem mul_positivePhase {d : ℂ} (hd : d ≠ 0) :
    d * positivePhase d = (‖d‖ : ℂ) := by
  have hnorm : (‖d‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hd
  rw [positivePhase, ← mul_div_assoc, Complex.mul_conj']
  field_simp

theorem unit_rotation_mem_ball {α v : ℂ} (hα : ‖α‖ = 1) :
    α * v ∈ ball (0 : ℂ) 1 ↔ v ∈ ball (0 : ℂ) 1 := by
  simp only [mem_ball_zero_iff, norm_mul, hα, one_mul]

/-- Rotate a biholomorphic disk model so that the derivative of its inverse is
positive real. The first map rotates in the opposite direction. -/
theorem normalize_biholomorphic_disk {U : Set ℂ} (hU : IsOpen U)
    {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hg : DifferentiableOn ℂ g (ball 0 1)) (hbij : BijOn f U (ball 0 1))
    (hgmap : MapsTo g (ball 0 1) U) (hinv : InvOn g f U (ball 0 1))
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) :
    ∃ fN gN : ℂ → ℂ, DifferentiableOn ℂ fN U ∧
      DifferentiableOn ℂ gN (ball 0 1) ∧ BijOn fN U (ball 0 1) ∧
      MapsTo gN (ball 0 1) U ∧ InvOn gN fN U (ball 0 1) ∧
      fN 0 = 0 ∧ gN 0 = 0 ∧
      deriv gN 0 = (‖deriv g 0‖ : ℂ) ∧ 0 < ‖deriv g 0‖ := by
  have hd : deriv g 0 ≠ 0 :=
    RiemannBiholomorphic.deriv_ne_zero_of_biholomorphic isOpen_ball hU
      hg hf hgmap hinv.2 (by simp)
  let α := positivePhase (deriv g 0)
  have hα : ‖α‖ = 1 := positivePhase_norm hd
  have hαne : α ≠ 0 := by
    intro hz
    simp [hz] at hα
  have hαinv : ‖α⁻¹‖ = 1 := by rw [norm_inv, hα, inv_one]
  let fN : ℂ → ℂ := fun w => α⁻¹ * f w
  let gN : ℂ → ℂ := fun v => g (α * v)
  have hfN : DifferentiableOn ℂ fN U := hf.const_mul α⁻¹
  have hgN : DifferentiableOn ℂ gN (ball 0 1) := by
    intro v hv
    exact ((hg.differentiableAt (isOpen_ball.mem_nhds
      ((unit_rotation_mem_ball hα).mpr hv))).comp v
      (differentiableAt_id.const_mul α)).differentiableWithinAt
  have hfNmap : MapsTo fN U (ball 0 1) := by
    intro w hw
    exact (unit_rotation_mem_ball hαinv).mpr (hbij.mapsTo hw)
  have hgNmap : MapsTo gN (ball 0 1) U := by
    intro v hv
    exact hgmap ((unit_rotation_mem_ball hα).mpr hv)
  have hleft : LeftInvOn gN fN U := by
    intro w hw
    dsimp [fN, gN]
    rw [← mul_assoc, mul_inv_cancel₀ hαne, one_mul, hinv.1 hw]
  have hright : RightInvOn gN fN (ball 0 1) := by
    intro v hv
    dsimp [fN, gN]
    rw [hinv.2 ((unit_rotation_mem_ball hα).mpr hv), ← mul_assoc,
      inv_mul_cancel₀ hαne, one_mul]
  refine ⟨fN, gN, hfN, hgN, ⟨hfNmap, hleft.injOn,
    fun v hv => ⟨gN v, hgNmap hv, hright hv⟩⟩, hgNmap, ⟨hleft, hright⟩,
    ?_, ?_, ?_, norm_pos_iff.mpr hd⟩
  · simp [fN, hf0]
  · simp [gN, hg0]
  · have hgd := hg.differentiableAt (isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1))
    have houter : HasDerivAt g (deriv g 0) (α * 0) := by simpa using hgd.hasDerivAt
    have hcomp := houter.comp 0 ((hasDerivAt_id (0 : ℂ)).const_mul α)
    have hderiv : deriv gN 0 = deriv g 0 * α := by
      simpa only [gN, Function.comp_def, id_eq, mul_one] using hcomp.deriv
    exact hderiv.trans (mul_positivePhase hd)

/-- A compact convex nontrivial set has an inverted disk model with positive
real inverse derivative. Its reciprocal `c` is the exterior leading coefficient. -/
theorem exists_positive_inverted_biholomorphic {K : Set ℂ} (hK : IsCompact K)
    (hconv : Convex ℝ K) {z y : ℂ} (hz : z ∈ K) (hy : y ∈ K) (hyz : y ≠ z) :
    ∃ (f g : ℂ → ℂ) (c : ℝ), 0 < c ∧
      DifferentiableOn ℂ f (invertedComplement K z) ∧
      DifferentiableOn ℂ g (ball 0 1) ∧
      BijOn f (invertedComplement K z) (ball 0 1) ∧
      MapsTo g (ball 0 1) (invertedComplement K z) ∧
      InvOn g f (invertedComplement K z) (ball 0 1) ∧
      f 0 = 0 ∧ g 0 = 0 ∧ deriv g 0 = ((c⁻¹ : ℝ) : ℂ) := by
  obtain ⟨f, g, hf, hg, hbij, hgmap, hinv, hf0, hg0⟩ :=
    exists_inverted_biholomorphic hK hconv hz hy hyz
  obtain ⟨fN, gN, hfN, hgN, hbijN, hgmapN, hinvN, hfN0, hgN0, hdN, hdpos⟩ :=
    normalize_biholomorphic_disk (invertedComplement_isOpen hK z)
      hf hg hbij hgmap hinv hf0 hg0
  refine ⟨fN, gN, ‖deriv g 0‖⁻¹, inv_pos.mpr hdpos, hfN, hgN,
    hbijN, hgmapN, hinvN, hfN0, hgN0, ?_⟩
  simpa only [inv_inv] using hdN

#print axioms normalize_biholomorphic_disk
#print axioms exists_positive_inverted_biholomorphic

end

end ExteriorReduction
