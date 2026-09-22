import PositiveNormalization
import AnalyticLaurentModel
import StarLikePositiveReal

/-!
# A positively normalized exterior map from one fixed disk model

The inversion and the analytic model at infinity use the same functions
throughout. All assertions below are constructed from the disk biholomorphism;
no second Riemann map or boundary regularity assertion is introduced.
-/

namespace ExteriorReduction

open Complex Set Metric Filter
open scoped Topology

noncomputable section

def exteriorFromModel (q : ℂ → ℂ) (A w : ℂ) : ℂ := A + w * q w⁻¹

def exteriorInverseFromDisk (f : ℂ → ℂ) (A p : ℂ) : ℂ := (f (p - A)⁻¹)⁻¹

theorem exteriorFromModel_hasDerivAt {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (A : ℂ) {w : ℂ} (hw : w ∈ exteriorDisk) :
    HasDerivAt (exteriorFromModel q A) (derivativeNumerator q w⁻¹) w := by
  have hwne : w ≠ 0 := by
    intro heq
    have hh : (1 : ℝ) < 0 := by simpa [heq, exteriorDisk] using hw
    norm_num at hh
  have hh := ((hasDerivAt_id w).mul
    ((hq w⁻¹ (inv_mem_disk_of_exterior hw)).differentiableAt.hasDerivAt.comp w
      (hasDerivAt_inv hwne))).const_add A
  convert hh using 1 <;> try rfl
  simp only [derivativeNumerator, id_eq, one_mul, Function.comp_apply]
  field_simp
  ring

theorem exteriorFromModel_normalized_deriv {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (hq0 : q 0 ≠ 0)
    (A : ℂ) {w : ℂ} (hw : w ∈ exteriorDisk) :
    deriv (exteriorFromModel q A) w = q 0 * modelDerivative q w⁻¹ := by
  rw [(exteriorFromModel_hasDerivAt hq A hw).deriv, modelDerivative]
  field_simp

/-- Inversion produces the exterior biholomorphism associated with the given
disk maps, and with exactly their removable Laurent model. -/
theorem laurentModel_exterior_biholomorphic {K : Set ℂ} (hK : IsCompact K)
    {A : ℂ} (hA : A ∈ K) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (invertedComplement K A))
    (hg : DifferentiableOn ℂ g (ball 0 1))
    (hbij : BijOn f (invertedComplement K A) (ball 0 1))
    (hgmap : MapsTo g (ball 0 1) (invertedComplement K A))
    (hinv : InvOn g f (invertedComplement K A) (ball 0 1))
    (_hf0 : f 0 = 0) (hg0 : g 0 = 0) :
    DifferentiableOn ℂ (exteriorFromModel (laurentModel g) A) exteriorDisk ∧
      DifferentiableOn ℂ (exteriorInverseFromDisk f A) Kᶜ ∧
      BijOn (exteriorFromModel (laurentModel g) A) exteriorDisk Kᶜ ∧
      MapsTo (exteriorInverseFromDisk f A) Kᶜ exteriorDisk ∧
      InvOn (exteriorInverseFromDisk f A) (exteriorFromModel (laurentModel g) A)
        exteriorDisk Kᶜ ∧
      (∀ w ∈ exteriorDisk, deriv (exteriorFromModel (laurentModel g) A) w ≠ 0) := by
  have hgne {v : ℂ} (hv : v ∈ ball 0 1) (hvne : v ≠ 0) : g v ≠ 0 :=
    StarLike.value_ne_zero hinv.2 hg0 hv hvne
  have hfne {v : ℂ} (hv : v ∈ invertedComplement K A) (hvne : v ≠ 0) : f v ≠ 0 := by
    intro hzero
    have hh := hinv.1 hv
    rw [hzero, hg0] at hh
    exact hvne hh.symm
  have hwne {w : ℂ} (hw : w ∈ exteriorDisk) : w ≠ 0 := by
    intro heq
    have hh : (1 : ℝ) < 0 := by simpa [heq, exteriorDisk] using hw
    norm_num at hh
  have hpne {p : ℂ} (hp : p ∈ Kᶜ) : p - A ≠ 0 := by
    intro heq
    exact hp (sub_eq_zero.mp heq ▸ hA)
  have hpinv {p : ℂ} (hp : p ∈ Kᶜ) : (p - A)⁻¹ ∈ invertedComplement K A := by
    right
    change p ∉ K at hp
    simpa only [inv_inv, add_sub_cancel] using hp
  let Ψ := exteriorFromModel (laurentModel g) A
  let Φ := exteriorInverseFromDisk f A
  have hΨeq {w : ℂ} (hw : w ∈ exteriorDisk) : Ψ w = A + (g w⁻¹)⁻¹ :=
    (exterior_eq_laurentModel hg0 A (hwne hw)).symm
  have hΨmap : MapsTo Ψ exteriorDisk Kᶜ := by
    intro w hw
    rw [hΨeq hw]
    exact (hgmap (inv_mem_disk_of_exterior hw)).resolve_left
      (hgne (inv_mem_disk_of_exterior hw) (inv_ne_zero (hwne hw)))
  have hΦmap : MapsTo Φ Kᶜ exteriorDisk := by
    intro p hp
    exact inv_mem_exterior_of_disk (hbij.mapsTo (hpinv hp))
      (hfne (hpinv hp) (inv_ne_zero (hpne hp)))
  have hleft : LeftInvOn Φ Ψ exteriorDisk := by
    intro w hw
    rw [hΨeq hw]
    dsimp [Φ, exteriorInverseFromDisk]
    rw [add_sub_cancel_left, inv_inv, hinv.2 (inv_mem_disk_of_exterior hw), inv_inv]
  have hright : RightInvOn Φ Ψ Kᶜ := by
    intro p hp
    rw [hΨeq (hΦmap hp)]
    dsimp [Φ, exteriorInverseFromDisk]
    rw [inv_inv, hinv.1 (hpinv hp), inv_inv, add_sub_cancel]
  have hΨbij : BijOn Ψ exteriorDisk Kᶜ :=
    ⟨hΨmap, hleft.injOn, fun p hp => ⟨Φ p, hΦmap hp, hright hp⟩⟩
  have hd0 : deriv g 0 ≠ 0 :=
    RiemannBiholomorphic.deriv_ne_zero_of_biholomorphic
      isOpen_ball (invertedComplement_isOpen hK A) hg hf hgmap hinv.2 (by simp)
  have hq : AnalyticOnNhd ℂ (laurentModel g) (ball 0 1) :=
    laurentModel_analytic hg hg0 hd0 (fun _ hv hvne => hgne hv hvne)
  have hΨdiff : DifferentiableOn ℂ Ψ exteriorDisk := by
    intro w hw
    exact ((differentiableAt_id.mul
      ((hq w⁻¹ (inv_mem_disk_of_exterior hw)).differentiableAt.comp w
        (differentiableAt_id.inv (hwne hw)))).const_add A).differentiableWithinAt
  have hΦdiff : DifferentiableOn ℂ Φ Kᶜ :=
    RiemannBiholomorphic.differentiableOn_inverse exteriorDisk_isOpen hK.isClosed.isOpen_compl
      hΨdiff hΨbij hΦmap ⟨hleft, hright⟩
  refine ⟨hΨdiff, hΦdiff, hΨbij, hΦmap, ⟨hleft, hright⟩, ?_⟩
  intro w hw
  exact RiemannBiholomorphic.deriv_ne_zero_of_biholomorphic
    exteriorDisk_isOpen hK.isClosed.isOpen_compl hΨdiff hΦdiff hΨmap hleft hw

/-- A nontrivial compact convex set admits one positive disk normalization,
its analytic model at infinity, and the associated exterior inverse maps.
All normalization and nonvanishing facts refer to this same `g`. -/
theorem exists_positive_exterior_model {K : Set ℂ} (hK : IsCompact K)
    (hconv : Convex ℝ K) {A y : ℂ} (hA : A ∈ K) (hy : y ∈ K) (hyA : y ≠ A) :
    ∃ (f g : ℂ → ℂ) (c : ℝ), 0 < c ∧
      DifferentiableOn ℂ f (invertedComplement K A) ∧
      DifferentiableOn ℂ g (ball 0 1) ∧
      BijOn f (invertedComplement K A) (ball 0 1) ∧
      MapsTo g (ball 0 1) (invertedComplement K A) ∧
      InvOn g f (invertedComplement K A) (ball 0 1) ∧ f 0 = 0 ∧ g 0 = 0 ∧
      deriv g 0 = ((c⁻¹ : ℝ) : ℂ) ∧
      laurentModel g 0 = (c : ℂ) ∧
      AnalyticOnNhd ℂ (laurentModel g) (ball 0 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, laurentModel g z ≠ 0) ∧
      AnalyticOnNhd ℂ (modelDerivative (laurentModel g)) (ball 0 1) ∧
      modelDerivative (laurentModel g) 0 = 1 ∧
      deriv (modelDerivative (laurentModel g)) 0 = 0 ∧
      (∀ z ∈ ball (0 : ℂ) 1, modelDerivative (laurentModel g) z ≠ 0) ∧
      DifferentiableOn ℂ (exteriorFromModel (laurentModel g) A) exteriorDisk ∧
      DifferentiableOn ℂ (exteriorInverseFromDisk f A) Kᶜ ∧
      BijOn (exteriorFromModel (laurentModel g) A) exteriorDisk Kᶜ ∧
      MapsTo (exteriorInverseFromDisk f A) Kᶜ exteriorDisk ∧
      InvOn (exteriorInverseFromDisk f A) (exteriorFromModel (laurentModel g) A)
        exteriorDisk Kᶜ ∧
      (∀ w ∈ exteriorDisk, deriv (exteriorFromModel (laurentModel g) A) w ≠ 0) := by
  obtain ⟨f, g, c, hc, hf, hg, hbij, hgmap, hinv, hf0, hg0, hdg⟩ :=
    exists_positive_inverted_biholomorphic hK hconv hA hy hyA
  have hderiv : ∀ z ∈ ball (0 : ℂ) 1, deriv g z ≠ 0 := fun _ hz =>
    RiemannBiholomorphic.deriv_ne_zero_of_biholomorphic
      isOpen_ball (invertedComplement_isOpen hK A) hg hf hgmap hinv.2 hz
  have hd0 := hderiv 0 (by simp)
  have hgne : ∀ z ∈ ball (0 : ℂ) 1, z ≠ 0 → g z ≠ 0 :=
    fun _ hz hz0 => StarLike.value_ne_zero hinv.2 hg0 hz hz0
  have hq := laurentModel_analytic hg hg0 hd0 hgne
  have hqne := fun z hz => laurentModel_ne_zero hg0 hd0 hgne (z := z) hz
  have hq0 := hqne 0 (by simp)
  have hqvalue : laurentModel g 0 = (c : ℂ) := by
    rw [laurentModel_zero, hdg, ← Complex.ofReal_inv, inv_inv]
  refine ⟨f, g, c, hc, hf, hg, hbij, hgmap, hinv, hf0, hg0, hdg, hqvalue,
    hq, hqne, modelDerivative_analytic hq hq0, modelDerivative_zero hq0,
    (modelDerivative_hasDerivAt_zero (hq 0 (by simp))).deriv,
    fun _ hz => modelDerivative_ne_zero hg hg0 hgne hderiv hz, ?_⟩
  exact laurentModel_exterior_biholomorphic hK hA hf hg hbij hgmap hinv hf0 hg0

#print axioms laurentModel_exterior_biholomorphic
#print axioms exists_positive_exterior_model
#print axioms exteriorFromModel_normalized_deriv

end
end ExteriorReduction
