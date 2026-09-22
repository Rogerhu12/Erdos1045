import StructuralNote.FixedSchurActualDiameterGraph

/-! Reflection and one-third-turn symmetry of the original extremizer, after
conjugating the canonical label symmetries through its genuine rigid model. -/

namespace StructuralNote.FixedSchurActualEuclideanSymmetry

open Complex Filter
open Erdos1045 Erdos1045.Configuration Erdos1045.EventualExact
open Erdos1045.EventualExact.FiniteBox
open FixedSchurChart FixedSchurEquationSmooth FixedSchurChartSmooth
open FixedSchurCyclicEquivariance FixedSchurReflectionEquivariance
open FixedSchurCanonicalWordSymmetry FixedSchurActualCanonicalEntry
open FixedSchurActualRigidEquivalence
open scoped Topology

noncomputable section

local notation "conj" => (starRingEnd ℂ)

/-- Conjugation in the oriented Euclidean coordinate with origin `a` and
unit direction `b`. -/
def planeReflection (a b z : ℂ) : ℂ :=
  a + b * conj ((z - a) / b)

/-- Rotation by `ρ` about `a`. -/
def rotationAbout (a ρ z : ℂ) : ℂ :=
  a + ρ * (z - a)

theorem planeReflection_dist (a b x y : ℂ) (hb : ‖b‖ = 1) :
    ‖planeReflection a b x - planeReflection a b y‖ = ‖x - y‖ := by
  have hsub : (x - a) / b - (y - a) / b = (x - y) / b := by ring
  have he : planeReflection a b x - planeReflection a b y =
      b * conj ((x - y) / b) := by
    unfold planeReflection
    calc
      a + b * conj ((x - a) / b) - (a + b * conj ((y - a) / b)) =
          b * (conj ((x - a) / b) - conj ((y - a) / b)) := by ring
      _ = b * conj ((x - a) / b - (y - a) / b) := by rw [map_sub]
      _ = b * conj ((x - y) / b) := by rw [hsub]
  rw [he, norm_mul, hb, one_mul, norm_conj, norm_div, hb, div_one]

theorem rotationAbout_dist (a ρ x y : ℂ) (hρ : ‖ρ‖ = 1) :
    ‖rotationAbout a ρ x - rotationAbout a ρ y‖ = ‖x - y‖ := by
  have he : rotationAbout a ρ x - rotationAbout a ρ y = ρ * (x - y) := by
    unfold rotationAbout
    ring
  rw [he, norm_mul, hρ, one_mul]

theorem planeReflection_fixedLine (a b : ℂ) (hb : b ≠ 0) (t : ℝ) :
    planeReflection a b (a + b * (t : ℂ)) = a + b * (t : ℂ) := by
  have hdiv : (a + b * (t : ℂ) - a) / b = (t : ℂ) := by
    field_simp
    ring
  have ht : conj (t : ℂ) = (t : ℂ) := by
    apply Complex.ext <;> simp
  rw [planeReflection, hdiv, ht]

theorem planeReflection_involutive (a b z : ℂ) (hb : b ≠ 0) :
    planeReflection a b (planeReflection a b z) = z := by
  have hcoord : (planeReflection a b z - a) / b = conj ((z - a) / b) := by
    unfold planeReflection
    field_simp
    ring
  unfold planeReflection at hcoord ⊢
  rw [hcoord]
  rw [conj_conj]
  field_simp
  ring

theorem directRigid_reflection {n : ℕ} {z w : Points n}
    (π : Equiv.Perm (Fin n)) (a b : ℂ) (hb : ‖b‖ = 1)
    (hzw : ∀ j, z (π j) = a + b * w j)
    (hreflect : w = reflectCenter w) :
    ∀ j, z (π j) = planeReflection a b (z (π (vertexReflection n j))) := by
  intro j
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, norm_zero] at hb
    norm_num at hb
  have href := congrFun hreflect j
  change w j = conj (w (vertexReflection n j)) at href
  rw [hzw j, hzw (vertexReflection n j)]
  unfold planeReflection
  have hdiv : (a + b * w (vertexReflection n j) - a) / b =
      w (vertexReflection n j) := by
    field_simp
    ring
  rw [hdiv, href]

theorem directRigid_thirdTurn {n k : ℕ} {z w : Points n}
    (π : Equiv.Perm (Fin n)) (a b : ℂ)
    (hzw : ∀ j, z (π j) = a + b * w j)
    (hturn : w = cyclicCenter k w) :
    ∀ j, z (π j) = rotationAbout a
      (conj (LocalPhase.regularRoot n ^ k)) (z (π (cyclicIndex n k j))) := by
  intro j
  have ht := congrFun hturn j
  change w j = conj (LocalPhase.regularRoot n ^ k) * w (cyclicIndex n k j) at ht
  rw [hzw j, hzw (cyclicIndex n k j)]
  unfold rotationAbout
  rw [ht]
  ring

theorem thirdTurnMultiplier_norm {m : ℕ} :
    ‖conj (LocalPhase.regularRoot (2 * m) ^ (2 * (m / 3)))‖ = 1 := by
  rw [norm_conj, norm_pow, ClosedFourier.root_norm, one_pow]

theorem thirdTurnMultiplier_cube {m : ℕ} (hm : 3 ≤ m) (hdiv : 3 ∣ m) :
    (conj (LocalPhase.regularRoot (2 * m) ^ (2 * (m / 3)))) ^ 3 = 1 := by
  obtain ⟨d, rfl⟩ := hdiv
  have hd : 3 * d / 3 = d := by omega
  rw [hd, ← map_pow, ← pow_mul]
  have he : 2 * d * 3 = 2 * (3 * d) := by omega
  rw [he, LocalDFT.regularRoot_pow (by omega)]
  norm_num

theorem thirdTurnMultiplier_ne_one {m : ℕ} (hm : 3 ≤ m) (hdiv : 3 ∣ m) :
    conj (LocalPhase.regularRoot (2 * m) ^ (2 * (m / 3))) ≠ 1 := by
  obtain ⟨d, rfl⟩ := hdiv
  have hd : 3 * d / 3 = d := by omega
  rw [hd]
  have hne := LocalDFT.regularRoot_power_ne_one
    (n := 2 * (3 * d)) (h := 2 * d) (by omega) (by omega) (by omega)
  intro h
  apply hne
  have hc := congrArg conj h
  simpa using hc

/-- Every sufficiently large actual even extremizer has a genuine Euclidean
reflection symmetry.  If `3 ∣ m` (equivalently `6 ∣ 2m`), it also has the
displayed one-third-turn rotation symmetry about the same physical center. -/
theorem eventual_actual_extremizer_euclidean_symmetries :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z : Points (2 * m),
      ExtremalNormalization.DiameterExtremal z →
      ∃ (hm : 3 ≤ m) (x : SchurParameters m) (π : Equiv.Perm (Fin (2 * m)))
        (a b : ℂ),
        CanonicalRepresentative hm z x ∧ ‖b‖ = 1 ∧
        (∀ j, z (π j) = a + b *
          configuration (by omega) (canonicalPattern hm) x.1 x.2 j) ∧
        (∀ j, z (π j) =
          planeReflection a b (z (π (vertexReflection (2 * m) j)))) ∧
        (3 ∣ m →
          let ρ := conj (LocalPhase.regularRoot (2 * m) ^ (2 * (m / 3)))
          ‖ρ‖ = 1 ∧ ρ ^ 3 = 1 ∧ ρ ≠ 1 ∧ ∀ j, z (π j) =
            rotationAbout a ρ (z (π (cyclicIndex (2 * m) (2 * (m / 3)) j)))) := by
  obtain ⟨m₀, hentry⟩ := eventual_actual_extremizer_canonical_directRigid
  obtain ⟨m₁, hreflect⟩ := eventually_atTop.1 eventual_canonical_reflection_symmetry
  obtain ⟨m₂, hturn⟩ := eventually_atTop.1 eventual_canonical_third_turn_symmetry
  refine ⟨max (max m₀ m₁) m₂, ?_⟩
  intro m hm z hz
  obtain ⟨hm3, x, hx, henergy, π, a, b, hb, hzw⟩ := hentry m (by omega) z hz
  let w : Points (2 * m) :=
    configuration (by omega) (canonicalPattern hm3) x.1 x.2
  have href : w = reflectCenter w :=
    hreflect m (by omega) hm3 x hx.1 hx.2.1
  have hzref : ∀ j, z (π j) =
      planeReflection a b (z (π (vertexReflection (2 * m) j))) :=
    directRigid_reflection π a b hb hzw href
  refine ⟨hm3, x, π, a, b, hx, hb, hzw, hzref, ?_⟩
  intro hdiv
  have ht : w = cyclicCenter (2 * (m / 3)) w :=
    hturn m (by omega) hm3 hdiv x hx.1 hx.2.1
  exact ⟨thirdTurnMultiplier_norm, thirdTurnMultiplier_cube hm3 hdiv,
    thirdTurnMultiplier_ne_one hm3 hdiv,
    directRigid_thirdTurn π a b hzw ht⟩

end
end StructuralNote.FixedSchurActualEuclideanSymmetry
