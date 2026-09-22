import StructuralNote.MatchingActivityKKTAnalytic
import StructuralNote.MatchingActivityKKTActual
import Erdos1045.HullGeometry

/-! Transport of the ambient KKT identity from a normalized representative to
an original configuration through a unit rigid motion and a relabeling.  The
multiplier coefficients are unchanged; only the endpoints of every active edge
are relabeled. -/

namespace StructuralNote.MatchingActivityKKTRigidTransport

open Erdos1045 Erdos1045.Configuration Erdos1045.EventualExact Complex
open MatchingActivityActiveConstraintDifferentials
open MatchingActivityKKTAnalytic
open MatchingActivityKKTActual
open CommonLocalization NormalizedPolarRepresentation ActualCrossingGeometry
open PolarCenterEnergy MatchingActivityActualChartSelection
open MatchingActivityRadialActual StrongPointwiseCoordinates
open scoped BigOperators Topology ContDiff
noncomputable section

/-- Pull an ambient velocity at the original configuration back through the
unit complex multiplier and the vertex relabeling. -/
def pullbackVelocity {n : ℕ} (b : ℂ) (π : Equiv.Perm (Fin n))
    (U : Points n) : Points n :=
  fun j => (starRingEnd ℂ) b * U (π j)

theorem mul_conj_eq_one_of_norm_eq_one {b : ℂ} (hb : ‖b‖ = 1) :
    b * (starRingEnd ℂ) b = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hb, one_pow]
  norm_num

/-- A unit affine image of an injective configuration remains injective after
any relabeling. -/
theorem rigid_relabel_injective {n : ℕ} {x z : Points n}
    (π : Equiv.Perm (Fin n)) (a b : ℂ) (hb : ‖b‖ = 1)
    (hx : Function.Injective x)
    (hrep : ∀ j, z (π j) = a + b * x j) :
    Function.Injective z := by
  have hb0 : b ≠ 0 := norm_ne_zero_iff.mp (by rw [hb]; norm_num)
  intro i j hij
  have hscaled : b * x (π.symm i) = b * x (π.symm j) := by
    apply add_left_cancel (a := a)
    calc
      a + b * x (π.symm i) = z (π (π.symm i)) := (hrep (π.symm i)).symm
      _ = z i := by rw [π.apply_symm_apply]
      _ = z j := hij
      _ = z (π (π.symm j)) := by rw [π.apply_symm_apply]
      _ = a + b * x (π.symm j) := hrep (π.symm j)
  have hxeq : x (π.symm i) = x (π.symm j) := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp ?_).resolve_left hb0
    calc
      b * (x (π.symm i) - x (π.symm j)) =
          b * x (π.symm i) - b * x (π.symm j) := by ring
      _ = 0 := sub_eq_zero.mpr hscaled
  exact π.symm.injective (hx hxeq)

private theorem rigid_path_relation {n : ℕ} {x z U : Points n}
    (π : Equiv.Perm (Fin n)) (a b : ℂ) (hb : ‖b‖ = 1)
    (hrep : ∀ j, z (π j) = a + b * x j) (t : ℝ) (j : Fin n) :
    (z + t • U) (π j) =
      a + b * (x + t • pullbackVelocity b π U) j := by
  have hunit := mul_conj_eq_one_of_norm_eq_one hb
  have hvelocity : b * ((t : ℂ) * ((starRingEnd ℂ) b * U (π j))) =
      (t : ℂ) * U (π j) := by
    calc
      b * ((t : ℂ) * ((starRingEnd ℂ) b * U (π j))) =
          (t : ℂ) * (b * (starRingEnd ℂ) b) * U (π j) := by ring
      _ = (t : ℂ) * U (π j) := by rw [hunit]; ring
  simp only [Pi.add_apply, Pi.smul_apply, pullbackVelocity]
  change z (π j) + (t : ℂ) * U (π j) =
    a + b * (x j + (t : ℂ) * ((starRingEnd ℂ) b * U (π j)))
  rw [hrep, mul_add, hvelocity]
  ring

/-- Every active squared-edge first differential is unchanged by a unit rigid
motion when both endpoints and the velocity are transported together. -/
theorem edgeDifferential_rigid_relabel {n : ℕ} {x z : Points n}
    (π : Equiv.Perm (Fin n)) (a b : ℂ) (hb : ‖b‖ = 1)
    (hrep : ∀ j, z (π j) = a + b * x j)
    (U : Points n) (p q : Fin n) :
    edgeDifferential x (pullbackVelocity b π U) p q =
      edgeDifferential z U (π p) (π q) := by
  let V := pullbackVelocity b π U
  let xp : ℝ → Points n := fun t => x + t • V
  let zp : ℝ → Points n := fun t => z + t • U
  have hxp (j : Fin n) : HasDerivAt (fun t => xp t j) (V j) 0 := by
    simpa only [xp, Pi.add_apply, Pi.smul_apply, zero_smul, add_zero, one_smul]
      using ((hasDerivAt_id' (0 : ℝ)).smul_const (V j)).const_add (x j)
  have hzp (j : Fin n) : HasDerivAt (fun t => zp t j) (U j) 0 := by
    simpa only [zp, Pi.add_apply, Pi.smul_apply, zero_smul, add_zero, one_smul]
      using ((hasDerivAt_id' (0 : ℝ)).smul_const (U j)).const_add (z j)
  have hedge : (fun t => edgeConstraint (xp t) p q) =
      fun t => edgeConstraint (zp t) (π p) (π q) := by
    funext t
    have hp := rigid_path_relation (U := U) π a b hb hrep t p
    have hq := rigid_path_relation (U := U) π a b hb hrep t q
    unfold edgeConstraint
    rw [show zp t (π p) - zp t (π q) = b * (xp t p - xp t q) by
      dsimp only [xp, zp, V] at hp hq ⊢
      rw [hp, hq]
      ring,
      norm_mul, hb, one_mul]
  calc
    edgeDifferential x V p q =
        deriv (fun t => edgeConstraint (xp t) p q) 0 :=
      by simpa only [xp, zero_smul, add_zero] using
        (edgeConstraint_hasDerivAt p q hxp).deriv.symm
    _ = deriv (fun t => edgeConstraint (zp t) (π p) (π q)) 0 := by rw [hedge]
    _ = edgeDifferential z U (π p) (π q) :=
      by simpa only [zp, zero_smul, add_zero] using
        (edgeConstraint_hasDerivAt (π p) (π q) hzp).deriv

/-- The ambient first derivative of the logarithmic discriminant is invariant
under the same unit rigid motion and relabeling. -/
theorem fderiv_logDiscriminant_rigid_relabel {n : ℕ} {x z : Points n}
    (π : Equiv.Perm (Fin n)) (a b : ℂ) (hb : ‖b‖ = 1)
    (hx : Function.Injective x)
    (hrep : ∀ j, z (π j) = a + b * x j)
    (U : Points n) :
    fderiv ℝ logDiscriminant x (pullbackVelocity b π U) =
      fderiv ℝ logDiscriminant z U := by
  let V := pullbackVelocity b π U
  let xp : ℝ → Points n := fun t => x + t • V
  let zp : ℝ → Points n := fun t => z + t • U
  have hzinj : Function.Injective z := rigid_relabel_injective π a b hb hx hrep
  have hxPath : HasDerivAt xp V 0 := by
    simpa only [xp, one_smul] using
      ((hasDerivAt_id' (0 : ℝ)).smul_const V).const_add x
  have hzPath : HasDerivAt zp U 0 := by
    simpa only [zp, one_smul] using
      ((hasDerivAt_id' (0 : ℝ)).smul_const U).const_add z
  have hdisc (t : ℝ) : discriminant (zp t) = discriminant (xp t) := by
    have hfun : zp t ∘ π = fun j => a + b * xp t j := by
      funext j
      exact rigid_path_relation π a b hb hrep t j
    calc
      discriminant (zp t) = discriminant (zp t ∘ π) :=
        (HullGeometry.discriminant_perm (zp t) π).symm
      _ = discriminant (fun j => a + b * xp t j) := by rw [hfun]
      _ = ‖b‖ ^ exponent n * discriminant (xp t) := discriminant_affine (xp t) a b
      _ = discriminant (xp t) := by rw [hb]; simp
  have hlog : (fun t => logDiscriminant (xp t)) =
      fun t => logDiscriminant (zp t) := by
    funext t
    unfold logDiscriminant
    rw [hdisc]
  have hxOuter : HasFDerivAt logDiscriminant
      (fderiv ℝ logDiscriminant x) x :=
    (logDiscriminant_contDiffAt hx).differentiableAt
      (by norm_num : (∞ : WithTop ℕ∞) ≠ 0) |>.hasFDerivAt
  have hzOuter : HasFDerivAt logDiscriminant
      (fderiv ℝ logDiscriminant z) z :=
    (logDiscriminant_contDiffAt hzinj).differentiableAt
      (by norm_num : (∞ : WithTop ℕ∞) ≠ 0) |>.hasFDerivAt
  have hxDerivative : HasDerivAt (fun t => logDiscriminant (xp t))
      (fderiv ℝ logDiscriminant x V) 0 := by
    have hxOuter0 : HasFDerivAt logDiscriminant
        (fderiv ℝ logDiscriminant x) (xp 0) := by
      simpa only [xp, zero_smul, add_zero] using hxOuter
    simpa only [xp, zero_smul, add_zero, Function.comp_def] using
      hxOuter0.comp_hasDerivAt 0 hxPath
  have hzDerivative : HasDerivAt (fun t => logDiscriminant (zp t))
      (fderiv ℝ logDiscriminant z U) 0 := by
    have hzOuter0 : HasFDerivAt logDiscriminant
        (fderiv ℝ logDiscriminant z) (zp 0) := by
      simpa only [zp, zero_smul, add_zero] using hzOuter
    simpa only [zp, zero_smul, add_zero, Function.comp_def] using
      hzOuter0.comp_hasDerivAt 0 hzPath
  calc
    fderiv ℝ logDiscriminant x V =
        deriv (fun t => logDiscriminant (xp t)) 0 := hxDerivative.deriv.symm
    _ = deriv (fun t => logDiscriminant (zp t)) 0 := by rw [hlog]
    _ = fderiv ℝ logDiscriminant z U := hzDerivative.deriv

/-- Multipliers on the original labeling.  The coefficient arrays are indexed
by the normalized word; `π` transports the corresponding matching and crossing
edge endpoints to the original configuration. -/
structure RelabeledMultipliers {m : ℕ} (hm : 0 < m) (s : Fin m → ℝ)
    (π : Equiv.Perm (Fin (2 * m))) (z : Points (2 * m)) where
  matching : Fin m → ℝ
  crossing : Fin m → ℝ
  stationarity : ∀ U : Points (2 * m),
    fderiv ℝ logDiscriminant z U =
      (∑ i, matching i * edgeDifferential z U
        (π (matchingFirst i)) (π (matchingSecond hm i))) +
      ∑ i, crossing i * edgeDifferential z U
        (π (selectedFirst hm s i)) (π (selectedSecond hm s i))

/-- Transport a genuine normalized multiplier certificate to the original
configuration without changing any multiplier coefficient. -/
def transportMultipliers {m : ℕ} (hm : 0 < m) (s : Fin m → ℝ)
    (x z : Points (2 * m)) (π : Equiv.Perm (Fin (2 * m))) (a b : ℂ)
    (hb : ‖b‖ = 1) (hx : Function.Injective x)
    (hrep : ∀ j, z (π j) = a + b * x j)
    (K : Multipliers hm s x) : RelabeledMultipliers hm s π z where
  matching := K.matching
  crossing := K.crossing
  stationarity U := by
    rw [← fderiv_logDiscriminant_rigid_relabel π a b hb hx hrep U,
      K.stationarity]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      rw [edgeDifferential_rigid_relabel π a b hb hrep U]
    · apply Finset.sum_congr rfl
      intro i _
      rw [edgeDifferential_rigid_relabel π a b hb hrep U]

@[simp] theorem transportMultipliers_matching {m : ℕ} (hm : 0 < m)
    (s : Fin m → ℝ) (x z : Points (2 * m))
    (π : Equiv.Perm (Fin (2 * m))) (a b : ℂ) (hb : ‖b‖ = 1)
    (hx : Function.Injective x) (hrep : ∀ j, z (π j) = a + b * x j)
    (K : Multipliers hm s x) :
    (transportMultipliers hm s x z π a b hb hx hrep K).matching = K.matching := rfl

@[simp] theorem transportMultipliers_crossing {m : ℕ} (hm : 0 < m)
    (s : Fin m → ℝ) (x z : Points (2 * m))
    (π : Equiv.Perm (Fin (2 * m))) (a b : ℂ) (hb : ‖b‖ = 1)
    (hx : Function.Injective x) (hrep : ∀ j, z (π j) = a + b * x j)
    (K : Multipliers hm s x) :
    (transportMultipliers hm s x z π a b hb hx hrep K).crossing = K.crossing := rfl

/-- The localization model itself gives a direct rigid presentation of the
original points by the normalized physical points. -/
theorem model_directRigid_normalizedPoint {m : ℕ} {z : Points (2 * m)}
    {π : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (hmodel : NormalizedRelativeEdgeModel z π α β u η) :
    ∃ A R : ℂ, ‖R‖ = 1 ∧
      ∀ j, z (π j) = A + R * normalizedPoint m β u j := by
  let A : ℂ := α + (β / (‖β‖ : ℂ)) * physicalTranslation m ‖β‖ u
  let R : ℂ := (β / (‖β‖ : ℂ)) * PolarCenterEnergy.phase (-meanAngle m u)
  refine ⟨A, R, normalizedRotation_norm hmodel.scale_ne_zero u, ?_⟩
  intro j
  have h := model_normalized_coordinates hmodel j
  rw [← ActualPressureGap.polarCenter_eq_normalizedCenter m β u] at h
  simpa only [A, R, normalizedPoint, phase, neg_neg,
    SignedPressureAngular.root, PolarRepresentation.reference, mul_assoc] using h

/-- A model multiplier certificate transports directly to the original
configuration.  The injectivity assumption is on the original points; the
rigid presentation then recovers injectivity of the normalized points. -/
theorem exists_relabeledMultipliers_of_model {m : ℕ} (hm : 0 < m)
    {z : Points (2 * m)} {π : Equiv.Perm (Fin (2 * m))} {α β : ℂ}
    {u : ℕ → ℂ} {η : ℝ}
    (hmodel : NormalizedRelativeEdgeModel z π α β u η)
    (hzinj : Function.Injective z)
    (K : ActualMultipliers hm β u) :
    ∃ L : RelabeledMultipliers hm
        (fun i => activeHalfSign hm (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i) π z,
      L.matching = K.matching ∧ L.crossing = K.crossing := by
  obtain ⟨A, R, hR, hrep⟩ := model_directRigid_normalizedPoint hmodel
  have hxinj : Function.Injective (normalizedPoint m β u) := by
    intro i j hij
    apply π.injective
    apply hzinj
    rw [hrep i, hrep j, hij]
  let L := transportMultipliers hm
    (fun i => activeHalfSign hm (normalizedAngle m u) (modelRadii m β u)
      (actualCenter m β u) i)
    (normalizedPoint m β u) z π A R hR hxinj hrep K
  exact ⟨L, rfl, rfl⟩

private theorem injective_of_discriminant_pos {n : ℕ} {z : Points n}
    (hdisc : 0 < discriminant z) : Function.Injective z := by
  intro i j hij
  by_contra hne
  have hinner : (∏ k ∈ Finset.univ.erase i, ‖z i - z k‖) = 0 := by
    apply Finset.prod_eq_zero (i := j)
    · simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact Ne.symm hne
    · rw [hij, sub_self, norm_zero]
  have hzero : discriminant z = 0 := by
    unfold discriminant
    apply Finset.prod_eq_zero (i := i)
    · simp
    · exact hinner
  linarith

/-- Every sufficiently large actual diameter maximizer therefore carries the
normalized unique multiplier family and its coefficient-identical ambient KKT
certificate on the original labeling. -/
theorem eventual_actual_maximizer_relabeled_multipliers :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z : Points (2 * m),
      ExtremalNormalization.DiameterExtremal z →
      ∃ (hm : 0 < m) (π : Equiv.Perm (Fin (2 * m))) (α β : ℂ)
        (u : ℕ → ℂ) (η : ℝ) (K : ActualMultipliers hm β u)
        (L : RelabeledMultipliers hm
          (fun i => activeHalfSign hm (normalizedAngle m u) (modelRadii m β u)
            (actualCenter m β u) i) π z),
        NormalizedRelativeEdgeModel z π α β u η ∧
        ActualKKTConditions hm β u ∧
        (∀ K' : ActualMultipliers hm β u, K' = K) ∧
        L.matching = K.matching ∧ L.crossing = K.crossing := by
  obtain ⟨m₀, hKKT⟩ := eventual_actual_maximizer_unique_multipliers
  refine ⟨m₀, ?_⟩
  intro m hm z hz
  obtain ⟨hmp, π, α, β, u, η, hmodel, _, hconditions, K, hKunique⟩ :=
    hKKT m hm z hz
  have hdisc : 0 < discriminant z := by
    rw [← WholeBoxLowerBound.diameterMaximum_eq_of_extremal hz]
    exact WholeBoxLowerBound.diameterMaximum_pos (by have := hconditions.large; omega)
  have hzinj : Function.Injective z := injective_of_discriminant_pos hdisc
  obtain ⟨L, hmatching, hcrossing⟩ :=
    exists_relabeledMultipliers_of_model hmp hmodel hzinj K
  exact ⟨hmp, π, α, β, u, η, K, L, hmodel, hconditions,
    hKunique, hmatching, hcrossing⟩

end
end StructuralNote.MatchingActivityKKTRigidTransport
