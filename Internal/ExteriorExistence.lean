import InvertedConvexDomain
import RiemannBiholomorphic

/-!
# Actual exterior maps for nontrivial compact convex sets

Inversion reduces the problem to a proper simply connected plane domain.
The maps below are genuine holomorphic inverse bijections. Normalization
of the coefficient at infinity and the Laurent expansion are separate
remaining steps, not hidden fields in this existence statement.
-/

namespace ExteriorReduction

open Complex Set Metric Function

def exteriorDisk : Set ℂ := {w | 1 < ‖w‖}

theorem exteriorDisk_isOpen : IsOpen exteriorDisk :=
  isOpen_lt continuous_const continuous_norm

theorem inv_mem_disk_of_exterior {w : ℂ} (hw : w ∈ exteriorDisk) :
    w⁻¹ ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, norm_inv, inv_eq_one_div]
  exact (div_lt_one (lt_trans zero_lt_one hw)).mpr hw

theorem inv_mem_exterior_of_disk {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) (hne : w ≠ 0) :
    w⁻¹ ∈ exteriorDisk := by
  change 1 < ‖w⁻¹‖
  rw [norm_inv, inv_eq_one_div]
  exact (one_lt_div (norm_pos_iff.mpr hne)).mpr (mem_ball_zero_iff.mp hw)

theorem exists_inverted_biholomorphic {K : Set ℂ} (hK : IsCompact K)
    (hconv : Convex ℝ K) {z y : ℂ} (hz : z ∈ K) (hy : y ∈ K) (hyz : y ≠ z) :
    ∃ f g : ℂ → ℂ, DifferentiableOn ℂ f (invertedComplement K z) ∧
      DifferentiableOn ℂ g (ball 0 1) ∧
      BijOn f (invertedComplement K z) (ball 0 1) ∧
      MapsTo g (ball 0 1) (invertedComplement K z) ∧
      InvOn g f (invertedComplement K z) (ball 0 1) ∧ f 0 = 0 ∧ g 0 = 0 :=
  RiemannBiholomorphic.exists_biholomorphic_unitBall
    (invertedComplement_isOpen hK z) (invertedComplement_simplyConnected hconv hz)
    (invertedComplement_ne_univ hy hyz) (zero_mem_invertedComplement K z)

theorem exists_exterior_biholomorphic {K : Set ℂ} (hK : IsCompact K)
    (hconv : Convex ℝ K) {z y : ℂ} (hz : z ∈ K) (hy : y ∈ K) (hyz : y ≠ z) :
    ∃ Ψ Φ g : ℂ → ℂ, DifferentiableOn ℂ Ψ exteriorDisk ∧
      DifferentiableOn ℂ Φ Kᶜ ∧ BijOn Ψ exteriorDisk Kᶜ ∧
      MapsTo Φ Kᶜ exteriorDisk ∧ InvOn Φ Ψ exteriorDisk Kᶜ ∧
      (∀ w ∈ exteriorDisk, deriv Ψ w ≠ 0) ∧
      DifferentiableOn ℂ g (ball 0 1) ∧ g 0 = 0 ∧ deriv g 0 ≠ 0 ∧
      (∀ w, Ψ w = z + (g w⁻¹)⁻¹) := by
  obtain ⟨f, g, hf, hg, hbij, hgmap, hinv, hf0, hg0⟩ :=
    exists_inverted_biholomorphic hK hconv hz hy hyz
  have hgne {v : ℂ} (hv : v ∈ ball 0 1) (hvne : v ≠ 0) : g v ≠ 0 := by
    intro hzero
    have hh := hinv.2 hv
    rw [hzero, hf0] at hh
    exact hvne hh.symm
  have hfne {v : ℂ} (hv : v ∈ invertedComplement K z) (hvne : v ≠ 0) : f v ≠ 0 := by
    intro hzero
    have hh := hinv.1 hv
    rw [hzero, hg0] at hh
    exact hvne hh.symm
  have hwne {w : ℂ} (hw : w ∈ exteriorDisk) : w ≠ 0 := by
    intro heq
    have hh : (1 : ℝ) < 0 := by simpa [heq, exteriorDisk] using hw
    norm_num at hh
  have hpne {p : ℂ} (hp : p ∈ Kᶜ) : p - z ≠ 0 := by
    intro heq
    exact hp (sub_eq_zero.mp heq ▸ hz)
  have hpinv {p : ℂ} (hp : p ∈ Kᶜ) : (p - z)⁻¹ ∈ invertedComplement K z := by
    right
    change p ∉ K at hp
    simpa only [inv_inv, add_sub_cancel] using hp
  let Ψ : ℂ → ℂ := fun w => z + (g w⁻¹)⁻¹
  let Φ : ℂ → ℂ := fun p => (f (p - z)⁻¹)⁻¹
  have hΨmap : MapsTo Ψ exteriorDisk Kᶜ := by
    intro w hw
    exact (hgmap (inv_mem_disk_of_exterior hw)).resolve_left
      (hgne (inv_mem_disk_of_exterior hw) (inv_ne_zero (hwne hw)))
  have hΦmap : MapsTo Φ Kᶜ exteriorDisk := by
    intro p hp
    exact inv_mem_exterior_of_disk (hbij.mapsTo (hpinv hp))
      (hfne (hpinv hp) (inv_ne_zero (hpne hp)))
  have hleft : LeftInvOn Φ Ψ exteriorDisk := by
    intro w hw
    dsimp [Φ, Ψ]
    rw [add_sub_cancel_left, inv_inv, hinv.2 (inv_mem_disk_of_exterior hw), inv_inv]
  have hright : RightInvOn Φ Ψ Kᶜ := by
    intro p hp
    dsimp [Φ, Ψ]
    rw [inv_inv, hinv.1 (hpinv hp), inv_inv, add_sub_cancel]
  have hΨbij : BijOn Ψ exteriorDisk Kᶜ :=
    ⟨hΨmap, hleft.injOn, fun p hp => ⟨Φ p, hΦmap hp, hright hp⟩⟩
  have hΨdiff : DifferentiableOn ℂ Ψ exteriorDisk := by
    intro w hw
    have hgi := (hg.differentiableAt (isOpen_ball.mem_nhds (inv_mem_disk_of_exterior hw))).comp w
      (differentiableAt_id.inv (hwne hw))
    exact ((hgi.inv (hgne (inv_mem_disk_of_exterior hw)
      (inv_ne_zero (hwne hw)))).const_add z).differentiableWithinAt
  have hΦdiff : DifferentiableOn ℂ Φ Kᶜ :=
    RiemannBiholomorphic.differentiableOn_inverse exteriorDisk_isOpen hK.isClosed.isOpen_compl
      hΨdiff hΨbij hΦmap ⟨hleft, hright⟩
  refine ⟨Ψ, Φ, g, hΨdiff, hΦdiff, hΨbij, hΦmap, ⟨hleft, hright⟩, ?_, hg, hg0, ?_, fun _ => rfl⟩
  · intro w hw
    exact RiemannBiholomorphic.deriv_ne_zero_of_biholomorphic
      exteriorDisk_isOpen hK.isClosed.isOpen_compl hΨdiff hΦdiff hΨmap hleft hw
  · exact RiemannBiholomorphic.deriv_ne_zero_of_biholomorphic
      isOpen_ball (invertedComplement_isOpen hK z) hg hf hgmap hinv.2 (by simp)

#print axioms exists_inverted_biholomorphic
#print axioms exists_exterior_biholomorphic

end ExteriorReduction
