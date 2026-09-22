import Mathlib

/-!
# Extremal discriminants of finite planar configurations

Concrete definitions and final propositions for Erdos 1045.
This file depends only on Mathlib. `Erdos1045.main` proves the combined
proposition `Erdos1045.Statement.Claims` in `Erdos1045.Proof`.
Each unordered distance occurs twice in the discriminant.
-/

namespace Erdos1045.Statement

/-- A concrete sufficient order for the even geometry and algebraic certificate. -/
def evenThreshold : ℕ := 2 ^ (10 ^ 120)

/-- A common concrete sufficient order for odd diameter and perimeter rigidity. -/
def regularThreshold : ℕ := 2 ^ 100000000

/-- The sufficient diameter order, selected by parity. -/
def diameterThreshold (n : ℕ) : ℕ :=
  if Odd n then regularThreshold else evenThreshold

open scoped BigOperators Topology
noncomputable section

abbrev Points (n : ℕ) := Fin n → ℂ

def discriminant {n : ℕ} (z : Points n) : ℝ :=
  ∏ i, ∏ j ∈ Finset.univ.erase i, ‖z i - z j‖

def DiameterAtMost {n : ℕ} (d : ℝ) (z : Points n) : Prop :=
  ∀ i j, ‖z i - z j‖ ≤ d

def regular (n : ℕ) : Points n :=
  fun j => Complex.exp (((2 * Real.pi * (j : ℝ) / n : ℝ) : ℂ) * Complex.I)

def IsRegular {n : ℕ} (z : Points n) : Prop :=
  ∃ a b : ℂ, b ≠ 0 ∧ ∃ σ : Equiv.Perm (Fin n),
    ∀ j, z j = a + b * regular n (σ j)

def support {n : ℕ} (z : Points n) (t : ℝ) : ℝ :=
  sSup (Set.range (fun i : Fin n => (z i * Complex.exp (-((t : ℂ) * Complex.I))).re))

/-- The support-integral perimeter of the convex hull; a segment has twice its length. -/
def hullPerimeter {n : ℕ} (z : Points n) : ℝ :=
  ∫ t in (0 : ℝ)..(2 * Real.pi), support z t

def diameterValues (n : ℕ) : Set ℝ :=
  {x | ∃ z : Points n, DiameterAtMost 2 z ∧ discriminant z = x}

def perimeterValues (n : ℕ) : Set ℝ :=
  {x | ∃ z : Points n, hullPerimeter z ≤ 2 * Real.pi ∧ discriminant z = x}

def M (n : ℕ) : ℝ := sSup (diameterValues n)

def W (n : ℕ) : ℝ := sSup (perimeterValues n)

def DiameterExtremal {n : ℕ} (z : Points n) : Prop :=
  DiameterAtMost 2 z ∧
    ∀ w : Points n, DiameterAtMost 2 w → discriminant w ≤ discriminant z

/-! Geometric characterization of diameter maximizers. -/

open scoped BigOperators

/-- Two labelled configurations agree after a relabelling and a
direct Euclidean rigid motion of the complex plane. -/
def DirectRigidRelabeling {n : ℕ} (z w : Points n) : Prop :=
  ∃ π : Equiv.Perm (Fin n), ∃ a b : ℂ, ‖b‖ = 1 ∧
    ∀ j, z (π j) = a + b * w j

/-- The centroid of a finite labelled configuration. -/
noncomputable def centroid {n : ℕ} (z : Points n) : ℂ :=
  (∑ j, z j) / (n : ℂ)

/-- Reflection in the line through `a` with unit direction `b`. -/
noncomputable def planeReflection (a b z : ℂ) : ℂ :=
  a + b * (starRingEnd ℂ) ((z - a) / b)

/-- Rotation by the unit complex number `ρ` about `a`. -/
def rotationAbout (a ρ z : ℂ) : ℂ :=
  a + ρ * (z - a)

/-- The standard positively oriented `n`-th root used to specify the exact
one-third-turn multiplier. -/
noncomputable def regularRoot (n : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi / (n : ℝ) : ℝ) : ℂ) * Complex.I)

/-- Add `k` to a cyclic label.  A function is enough for the public
geometric statement; the implementation may use an equivalent permutation. -/
def cyclicShiftIndex {n : ℕ} (hn : 0 < n) (k : ℕ) (j : Fin n) : Fin n :=
  ⟨(j.val + k) % n, Nat.mod_lt _ hn⟩

/-- Negate a cyclic label. -/
def reflectionIndex {n : ℕ} (hn : 0 < n) (j : Fin n) : Fin n :=
  ⟨(n - j.val) % n, Nat.mod_lt _ hn⟩

/-- The repeated outer block length in the balanced three-block word. -/
def canonicalOuter (m : ℕ) : ℕ :=
  if m % 3 = 2 then m / 3 + 1 else m / 3

/-- The middle block length in the balanced three-block word. -/
def canonicalMiddle (m : ℕ) : ℕ :=
  if m % 3 = 1 then m / 3 + 1 else m / 3

/-- The negative positions of the canonical antiperiodic three-block word,
written directly as interval membership rather than through proof-internal
word encodings. -/
def canonicalNegative (m : ℕ) (j : Fin (2 * m)) : Prop :=
  let x := j.val % m
  if j.val < m then
    canonicalOuter m ≤ x ∧ x < canonicalOuter m + canonicalMiddle m
  else
    x < canonicalOuter m ∨ canonicalOuter m + canonicalMiddle m ≤ x

/-- The complete canonical even-order diameter graph, as an adjacency
predicate on its explicit cyclic labelling.  It consists of every half-turn
edge and precisely the selected two orientations of the `(m+1)` offset. -/
def CanonicalEvenDiameterAdj {m : ℕ} (hm : 3 ≤ m)
    (i j : Fin (2 * m)) : Prop :=
  let shift := cyclicShiftIndex (n := 2 * m) (by omega : 0 < 2 * m)
  j = shift m i ∨
    (j = shift (m + 1) i ∧ canonicalNegative m i) ∨
    (i = shift (m + 1) j ∧ canonicalNegative m j)

/-- All public even-order geometry attached to an actual extremizer. -/
structure EvenGeometry (m : ℕ) (z : Points (2 * m)) where
  large : 3 ≤ m
  graphRelabeling : Equiv.Perm (Fin (2 * m))
  graph_eq : ∀ i j,
    (‖z (graphRelabeling i) - z (graphRelabeling j)‖ = 2 ↔
      CanonicalEvenDiameterAdj large i j)
  symmetryRelabeling : Equiv.Perm (Fin (2 * m))
  reflectionCenter : ℂ
  reflectionDirection : ℂ
  reflectionDirection_unit : ‖reflectionDirection‖ = 1
  reflection : ∀ j,
    z (symmetryRelabeling j) =
      planeReflection reflectionCenter reflectionDirection
        (z (symmetryRelabeling
          (reflectionIndex (n := 2 * m) (by omega : 0 < 2 * m) j)))
  thirdTurn : 3 ∣ m →
    let ρ := (starRingEnd ℂ)
      (regularRoot (2 * m) ^ (2 * (m / 3)))
    ‖ρ‖ = 1 ∧ ρ ^ 3 = 1 ∧ ρ ≠ 1 ∧
      ∀ j, z (symmetryRelabeling j) =
        rotationAbout (centroid z) ρ
          (z (symmetryRelabeling
            (cyclicShiftIndex (n := 2 * m) (by omega : 0 < 2 * m)
              (2 * (m / 3)) j)))

/-- The geometric characterization, phrased in terms of
the literal supremum `M` and actual point configurations. -/
def DiameterCharacterization : Prop :=
  ∀ n : ℕ, diameterThreshold n ≤ n →
    (∃ z : Points n, DiameterAtMost 2 z ∧ discriminant z = M n) ∧
    (∀ z w : Points n,
      DiameterAtMost 2 z → discriminant z = M n →
      DiameterAtMost 2 w → discriminant w = M n →
      DirectRigidRelabeling z w) ∧
    (Odd n →
      M n = (n : ℝ) ^ n /
        Real.cos (Real.pi / (2 * n)) ^ (n * (n - 1)) ∧
      ∀ z : Points n,
        DiameterAtMost 2 z → discriminant z = M n → IsRegular z) ∧
    (∀ m : ℕ, n = 2 * m → ∀ z : Points (2 * m),
      DiameterExtremal z → Nonempty (EvenGeometry m z))

/-- The exact perimeter maximum, attainment, regularity and rigid uniqueness
above the concrete regular-polygon threshold. -/
def PerimeterCharacterization : Prop :=
  ∀ n : ℕ, regularThreshold ≤ n →
    W n = (n : ℝ)^n * (Real.pi / (n * Real.sin (Real.pi / n)))^(n * (n - 1)) ∧
    (∃ z : Points n, hullPerimeter z ≤ 2 * Real.pi ∧ discriminant z = W n) ∧
    (∀ z : Points n, hullPerimeter z ≤ 2 * Real.pi → discriminant z = W n →
      IsRegular z) ∧
    (∀ z w : Points n, hullPerimeter z ≤ 2 * Real.pi → discriminant z = W n →
      hullPerimeter w ≤ 2 * Real.pi → discriminant w = W n → DirectRigidRelabeling z w)

/-- The even and odd normalized discriminant limits. -/
def NormalizedLimits : Prop :=
  Filter.Tendsto (fun m : ℕ => M (2 * m) / (2 * m : ℝ)^(2 * m)) Filter.atTop
    (𝓝 ((3 : ℝ)^(9 / 4 : ℝ) / 8 *
      Real.exp ((Real.pi^2 - 2 * Real.sqrt 3 * Real.pi) / 8))) ∧
  Filter.Tendsto (fun m : ℕ => M (2 * m + 1) / (2 * m + 1 : ℝ)^(2 * m + 1)) Filter.atTop
    (𝓝 (Real.exp (Real.pi^2 / 8)))

namespace KKT

open scoped BigOperators

noncomputable section

/-- The public indexing set for the two families of active edges.  The index
has no geometric meaning; the endpoints below live in the original labeling. -/
abbrev ActiveIndex (m : ℕ) := Sum (Fin m) (Fin m)

/-- Squared length of an edge in the original point configuration. -/
def edgeSquaredDistance {n : ℕ} (z : Points n) (p q : Fin n) : ℝ :=
  ‖z p - z q‖ ^ 2

/-- First variation of the squared length of an edge. -/
def edgeDifferential {n : ℕ} (z U : Points n) (p q : Fin n) : ℝ :=
  2 * inner ℝ (z p - z q) (U p - U q)

/-- The ambient gradient of the squared length of an edge. -/
def edgeGradient {n : ℕ} (z : Points n) (p q : Fin n) : Points n :=
  Pi.single p (2 * (z p - z q)) + Pi.single q (-2 * (z p - z q))

/-- The logarithmic discriminant whose KKT equation is asserted below. -/
def logDiscriminant {n : ℕ} (z : Points n) : ℝ :=
  Real.log (discriminant z)

/-- A public KKT certificate stated entirely on the original point set.

`active_exact` says that the displayed pairs are exactly all diameter edges,
with endpoint order ignored.  `licq` is linear independence of their squared-
distance differentials.  The remaining fields give the unique strictly
positive multiplier family and complementary slackness. -/
structure PositiveKKT {m : ℕ} (z : Points (2 * m)) : Type where
  first : ActiveIndex m → Fin (2 * m)
  second : ActiveIndex m → Fin (2 * m)
  active_exact : ∀ p q,
    ‖z p - z q‖ = 2 ↔
      ∃ k, (p = first k ∧ q = second k) ∨
        (q = first k ∧ p = second k)
  licq : ∀ c : ActiveIndex m → ℝ,
    (∀ U : Points (2 * m),
      ∑ k, c k * edgeDifferential z U (first k) (second k) = 0) →
    c = 0
  multiplier : ActiveIndex m → ℝ
  positive : ∀ k, 0 < multiplier k
  stationarity : ∀ U : Points (2 * m),
    fderiv ℝ logDiscriminant z U =
      ∑ k, multiplier k * edgeDifferential z U (first k) (second k)
  unique : ∀ μ : ActiveIndex m → ℝ,
    (∀ U : Points (2 * m),
      fderiv ℝ logDiscriminant z U =
        ∑ k, μ k * edgeDifferential z U (first k) (second k)) →
    μ = multiplier
  complementary_slackness : ∀ k,
    multiplier k *
      (edgeSquaredDistance z (first k) (second k) - 4) = 0

/-- Unique strictly positive KKT data at the concrete even-order cutoff. -/
def UniquePositiveKKT : Prop :=
  ∀ m : ℕ, evenThreshold ≤ 2 * m → ∀ z : Points (2 * m),
    DiameterExtremal z → Nonempty (PositiveKKT z)

end

end KKT

namespace Algebraic

/-- Finite Fourier character and midpoint frame used to define the reference. -/
def character (n p j : ℕ) : ℂ := regularRoot n ^ (j * p)

def frame (n : ℕ) (j : Fin n) : ℂ :=
  Complex.exp ((((1 : ℝ) * Real.pi / (n : ℝ) : ℝ) : ℂ) * Complex.I) *
    character n 1 j

def firstCoefficient {n : ℕ} (q : Fin n → ℝ) : ℂ :=
  (∑ j, (q j : ℂ) * (starRingEnd ℂ) (frame n j)) / n

def fourierCoefficient {n : ℕ} (f : Fin n → ℂ) (p : Fin n) : ℂ :=
  (∑ j, f j * (starRingEnd ℂ) (character n p j)) / n

def liftIncrement {n : ℕ} (q : Fin n → ℝ) (j : Fin n) : ℂ :=
  frame n j * ((2 * Real.sin (Real.pi / n) / n : ℝ) * (q j : ℂ) +
    Complex.I * (4 * Real.sin (Real.pi / n) / n : ℝ) *
      ((firstCoefficient q * frame n j).im : ℂ))

/-- The mean-zero discrete integral of the prescribed increments. -/
def canonicalLift {n : ℕ} (q : Fin n → ℝ) (j : Fin n) : ℂ :=
  ∑ p : Fin n,
    (if p.val = 0 then 0 else
      fourierCoefficient (liftIncrement q) p / (regularRoot n ^ p.val - 1)) *
        character n p j

def logOrder (n : ℕ) : ℕ := ⌈Real.log n / Real.log 2⌉₊

def referenceRadius (n : ℕ) : ℝ := 4096 * (logOrder n : ℝ) / (n : ℝ)

def baseWord {n : ℕ} (σ : Fin n → ℝ) (j : Fin n) : ℝ :=
  (n * Real.tan (Real.pi / (2 * n))) * σ j

def referenceChord {n : ℕ} (hn : 0 < n) (j : Fin n) : ℂ :=
  (starRingEnd ℂ) (frame n j) *
    (character n 1 j + character n 1 (cyclicShiftIndex hn 1 j))

/-- The positive square-root crossing equation at zero free parameters. -/
def referenceEquation {m : ℕ} (hm : 0 < m)
    (σ q : Fin (2 * m) → ℝ) (j : Fin (2 * m)) : ℝ :=
  let ε := 2 * Real.sin (Real.pi / (2 * m)) / (2 * m)
  let c := referenceChord (by omega : 0 < 2 * m) j
  let p := 2 * (firstCoefficient q * frame (2 * m) j).im
  σ j / ε * (Real.sqrt (4 - (c.im + σ j * ε * p) ^ 2) - c.re)

/-- Choose the fixed point in the specified ball, with the same total fallback
used to specify the reference center. Existence and uniqueness for
large orders are consequences of the construction. -/
def referenceCoordinate {m : ℕ} (hm : 0 < m)
    (σ : Fin (2 * m) → ℝ) : Fin (2 * m) → ℝ := by
  classical
  exact if h : ∃ q : Fin (2 * m) → ℝ,
      ‖q - baseWord σ‖ ≤ referenceRadius (2 * m) ∧
      referenceEquation hm σ q = q then h.choose else baseWord σ

def referenceCenter {m : ℕ} (hm : 0 < m)
    (σ : Fin (2 * m) → ℝ) : Fin (2 * m) → ℂ :=
  canonicalLift (referenceCoordinate hm σ)

/-- The exact quadratic pair energy, as a finite sum of chord ratios. -/
def pairEnergy {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) : ℝ :=
  (∑ h ∈ (Finset.range n).erase 0, ∑ j ∈ Finset.range n,
    Complex.normSq ((c ⟨(j + h) % n, Nat.mod_lt _ hn⟩ -
        c ⟨j % n, Nat.mod_lt _ hn⟩) /
      (regularRoot n ^ (j + h) - regularRoot n ^ j))) / 2

end Algebraic

/-! Algebraic characterization by an explicit stationary system and a polynomial window. -/

namespace Algebraic

open scoped BigOperators Topology
open MvPolynomial

/-! The canonical balanced word. -/

def canonicalSign (m : ℕ) (j : Fin (2 * m)) : ℝ := by
  classical
  exact if canonicalNegative m j then -1 else 1

def canonicalHalfWord (m : ℕ) (j : Fin m) : Bool := by
  classical
  exact decide (canonicalSign m ⟨j.val, by omega⟩ = 1)

def canonicalHalfSign (m : ℕ) (j : Fin m) : ℝ :=
  if canonicalHalfWord m j then 1 else -1

/-! The rational base-edge configuration. -/

abbrev ConfigVariables (m : ℕ) := Fin (m - 1) ⊕ Fin m

def angleParameter {m : ℕ} (X : ConfigVariables m → ℝ) (j : Fin m) : ℝ :=
  if hj : j.val = 0 then 0 else X (.inl ⟨j.val - 1, by omega⟩)

def crossingParameter {m : ℕ} (X : ConfigVariables m → ℝ) (j : Fin m) : ℝ :=
  X (.inr j)

def rationalRotation (t : ℝ) : ℂ :=
  ⟨(1 - t ^ 2) / (1 + t ^ 2), 2 * t / (1 + t ^ 2)⟩

def circleUnit (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

def midpoint (m : ℕ) (j : Fin m) : ℝ :=
  Real.pi / m * ((j : ℝ) + 1 / 2)

def diameter {m : ℕ} (hm : 0 < m) (X : ConfigVariables m → ℝ) (j : ℕ) : ℂ :=
  circleUnit (Real.pi / m * j) *
    rationalRotation (angleParameter X ⟨j % m, Nat.mod_lt _ hm⟩)

def crossingUnit {m : ℕ} (X : ConfigVariables m → ℝ) (j : Fin m) : ℂ :=
  circleUnit (midpoint m j) * rationalRotation (crossingParameter X j)

def crossingIncrement (σ : ℝ) (d e U : ℂ) : ℂ :=
  (σ : ℂ) * (2 * U - d - e)

def increment {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ)
    (X : ConfigVariables m → ℝ) (j : Fin m) : ℂ :=
  crossingIncrement (σ j) (diameter hm X j)
    (diameter hm X (j.val + 1)) (crossingUnit X j)

def centerPrefix {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ)
    (X : ConfigVariables m → ℝ) (r : ℕ) : ℂ :=
  ∑ j ∈ Finset.range r, if hj : j < m then increment hm σ X ⟨j, hj⟩ else 0

def closure {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ)
    (X : ConfigVariables m → ℝ) : ℂ :=
  ∑ j, increment hm σ X j

def point {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ)
    (X : ConfigVariables m → ℝ) (j : ℕ) : ℂ :=
  centerPrefix hm σ X (j % m) + diameter hm X j

def configuration {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ)
    (X : ConfigVariables m → ℝ) : Points (2 * m) :=
  fun j => point hm σ X j

def extendedAngleParameter {m : ℕ} (hm : 0 < m)
    (X : ConfigVariables m → ℝ) (j : Fin (2 * m)) : ℝ :=
  angleParameter X ⟨j.val % m, Nat.mod_lt _ hm⟩

def rationalCenter {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ)
    (X : ConfigVariables m → ℝ) (j : Fin (2 * m)) : ℂ :=
  centerPrefix hm σ X (j.val % m)

def selectedWindowEnergy {m : ℕ} (hm : 3 ≤ m)
    (X : ConfigVariables m → ℝ) : ℝ :=
  pairEnergy (by omega : 0 < 2 * m)
      (fun j => (extendedAngleParameter (by omega) X j : ℂ)) +
  pairEnergy (by omega : 0 < 2 * m)
      (rationalCenter (by omega) (canonicalHalfSign m) X -
        referenceCenter (by omega) (canonicalSign m))

/-! Rational expressions and their cleared polynomial system. -/

abbrev Coeff := algebraicClosure ℚ ℝ

structure Expression (ι : Type*) where
  numerator : MvPolynomial ι Coeff
  denominator : MvPolynomial ι Coeff

namespace Expression

variable {ι : Type*}

def eval (f : Expression ι) (x : ι → ℝ) : ℝ :=
  aeval x f.numerator / aeval x f.denominator

def polynomial (p : MvPolynomial ι Coeff) : Expression ι := ⟨p, 1⟩
def constant (c : Coeff) : Expression ι := polynomial (C c)
def var (i : ι) : Expression ι := polynomial (X i)

instance : Zero (Expression ι) := ⟨constant 0⟩
instance : One (Expression ι) := ⟨constant 1⟩
instance : Add (Expression ι) := ⟨fun f g =>
  ⟨f.numerator * g.denominator + g.numerator * f.denominator,
    f.denominator * g.denominator⟩⟩
instance : Neg (Expression ι) := ⟨fun f => ⟨-f.numerator, f.denominator⟩⟩
instance : Sub (Expression ι) := ⟨fun f g => f + -g⟩
instance : Mul (Expression ι) := ⟨fun f g =>
  ⟨f.numerator * g.numerator, f.denominator * g.denominator⟩⟩
instance : Inv (Expression ι) := ⟨fun f => ⟨f.denominator, f.numerator⟩⟩
instance : Div (Expression ι) := ⟨fun f g => f * g⁻¹⟩

def sumList : List (Expression ι) → Expression ι
  | [] => 0
  | f :: fs => f + sumList fs

def sum {α : Type*} (s : Finset α) (f : α → Expression ι) : Expression ι :=
  sumList (s.toList.map f)

def coordinateDerivative [DecidableEq ι] (i : ι) (f : Expression ι) : Expression ι :=
  ⟨pderiv i f.numerator * f.denominator - f.numerator * pderiv i f.denominator,
    f.denominator * f.denominator⟩

def rename {κ : Type*} (f : Expression ι) (r : ι → κ) : Expression κ :=
  ⟨MvPolynomial.rename r f.numerator, MvPolynomial.rename r f.denominator⟩

end Expression

structure ComplexExpression (ι : Type*) where
  re : Expression ι
  im : Expression ι

namespace ComplexExpression

variable {ι : Type*}

def ofReal (f : Expression ι) : ComplexExpression ι := ⟨f, 0⟩

instance : Zero (ComplexExpression ι) := ⟨ofReal 0⟩
instance : Add (ComplexExpression ι) := ⟨fun f g => ⟨f.re + g.re, f.im + g.im⟩⟩
instance : Neg (ComplexExpression ι) := ⟨fun f => ⟨-f.re, -f.im⟩⟩
instance : Sub (ComplexExpression ι) := ⟨fun f g => f + -g⟩
instance : Mul (ComplexExpression ι) := ⟨fun f g =>
  ⟨f.re * g.re - f.im * g.im, f.re * g.im + f.im * g.re⟩⟩

def sum {α : Type*} (s : Finset α) (f : α → ComplexExpression ι) : ComplexExpression ι :=
  ⟨Expression.sum s (fun a => (f a).re), Expression.sum s (fun a => (f a).im)⟩

def squareNorm (f : ComplexExpression ι) : Expression ι := f.re * f.re + f.im * f.im

def rotation (t : Expression ι) : ComplexExpression ι :=
  ⟨(1 - t * t) / (1 + t * t),
    (Expression.constant 2 * t) / (1 + t * t)⟩

theorem trig_algebraic (q : ℚ) :
    IsAlgebraic ℚ (Real.cos ((q : ℝ) * Real.pi)) ∧
      IsAlgebraic ℚ (Real.sin ((q : ℝ) * Real.pi)) := by
  have hi : Function.Injective (algebraMap ℤ ℚ) := by
    intro a b h
    exact_mod_cast h
  exact ⟨(Real.isAlgebraic_cos_rat_mul_pi q).extendScalars hi,
    (Real.isAlgebraic_sin_rat_mul_pi q).extendScalars hi⟩

def cosine (q : ℚ) : Coeff :=
  ⟨Real.cos ((q : ℝ) * Real.pi), mem_algebraicClosure_iff.mpr (trig_algebraic q).1⟩

def sine (q : ℚ) : Coeff :=
  ⟨Real.sin ((q : ℝ) * Real.pi), mem_algebraicClosure_iff.mpr (trig_algebraic q).2⟩

def unit (q : ℚ) : ComplexExpression ι :=
  ⟨Expression.constant (cosine q), Expression.constant (sine q)⟩

end ComplexExpression

abbrev RExpr (m : ℕ) := Expression (ConfigVariables m)
abbrev CExpr (m : ℕ) := ComplexExpression (ConfigVariables m)

def boolSign {m : ℕ} (σ : Fin m → Bool) (j : Fin m) : ℝ :=
  if σ j then 1 else -1

def signExpr {m : ℕ} (σ : Fin m → Bool) (j : Fin m) : RExpr m :=
  Expression.constant (if σ j then 1 else -1)

def angleExpr {m : ℕ} (j : Fin m) : RExpr m :=
  if hj : j.val = 0 then 0 else Expression.var (.inl ⟨j.val - 1, by omega⟩)

def crossingAngleExpr {m : ℕ} (j : Fin m) : RExpr m := Expression.var (.inr j)

def diameterExpr {m : ℕ} (hm : 0 < m) (j : ℕ) : CExpr m :=
  ComplexExpression.unit ((j : ℚ) / m) *
    ComplexExpression.rotation (angleExpr ⟨j % m, Nat.mod_lt _ hm⟩)

def crossingUnitExpr {m : ℕ} (j : Fin m) : CExpr m :=
  ComplexExpression.unit (((j.val : ℚ) + 1 / 2) / m) *
    ComplexExpression.rotation (crossingAngleExpr j)

def incrementExpr {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (j : Fin m) : CExpr m :=
  ComplexExpression.ofReal (signExpr σ j) *
    (ComplexExpression.ofReal (Expression.constant 2) * crossingUnitExpr j -
      diameterExpr hm j - diameterExpr hm (j.val + 1))

def centerPrefixExpr {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (r : ℕ) : CExpr m :=
  ComplexExpression.sum (Finset.range r)
    (fun j => if hj : j < m then incrementExpr hm σ ⟨j, hj⟩ else 0)

def closureExpr {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) : CExpr m :=
  ComplexExpression.sum Finset.univ (incrementExpr hm σ)

def pointExpr {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (j : ℕ) : CExpr m :=
  centerPrefixExpr hm σ (j % m) + diameterExpr hm j

def configurationExpr {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool)
    (j : Fin (2 * m)) : CExpr m :=
  pointExpr hm σ j

def squaredDistanceExpr {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool)
    (i j : Fin (2 * m)) : RExpr m :=
  (configurationExpr hm σ i - configurationExpr hm σ j).squareNorm

abbrev Variables (m : ℕ) := ConfigVariables m ⊕ Fin 2

def coordinates {m : ℕ} (Y : Variables m → ℝ) : ConfigVariables m → ℝ :=
  Y ∘ Sum.inl

def multiplier {m : ℕ} (Y : Variables m → ℝ) (k : Fin 2) : ℝ := Y (.inr k)

def pairs (m : ℕ) : Finset (Fin (2 * m) × Fin (2 * m)) :=
  Finset.univ.filter (fun p => p.1 ≠ p.2)

def closureCoordinate {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool)
    (k : Fin 2) : RExpr m :=
  if k.val = 0 then (closureExpr hm σ).re else (closureExpr hm σ).im

def objective {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool)
    (X : ConfigVariables m → ℝ) : ℝ :=
  (∑ p ∈ pairs m,
    Real.log (Complex.normSq
      (configuration hm (boolSign σ) X p.1 - configuration hm (boolSign σ) X p.2))) / 2

def gradient {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool)
    (i : ConfigVariables m) : RExpr m :=
  Expression.sum (pairs m) (fun p =>
    Expression.coordinateDerivative i (squaredDistanceExpr hm σ p.1 p.2) /
      squaredDistanceExpr hm σ p.1 p.2) / Expression.constant 2

def residual {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool)
    (i : ConfigVariables m) : Expression (Variables m) :=
  (gradient hm σ i).rename Sum.inl -
    Expression.sum Finset.univ (fun k : Fin 2 =>
      Expression.var (.inr k) *
        (Expression.coordinateDerivative i (closureCoordinate hm σ k)).rename Sum.inl)

def systemExpression {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) :
    Variables m → Expression (Variables m)
  | .inl i => residual hm σ i
  | .inr k => (closureCoordinate hm σ k).rename Sum.inl

def polynomials {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) :
    Variables m → MvPolynomial (Variables m) Coeff :=
  fun i => (systemExpression hm σ i).numerator

def Stationary {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool)
    (Y : Variables m → ℝ) : Prop :=
  closure hm (boolSign σ) (coordinates Y) = 0 ∧
    ∀ i, deriv (fun t => objective hm σ (Function.update (coordinates Y) i t))
        (coordinates Y i) =
      ∑ k : Fin 2, multiplier Y k * deriv (fun t =>
        (closureCoordinate hm σ k).eval (Function.update (coordinates Y) i t))
          (coordinates Y i)

def rationalJacobian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Expression ι) (x : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => deriv (fun t => (f i).eval (Function.update x j t)) (x j)

def polynomialJacobian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → MvPolynomial ι Coeff) (x : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => aeval x (pderiv j (p i))

structure Certificate (m : ℕ) where
  large : 3 ≤ m
  root : Variables m → ℝ
  window : MvPolynomial (ConfigVariables m) Coeff
  dimension : Fintype.card (Variables m) = 2 * m + 1
  window_spec : ∀ X : ConfigVariables m → ℝ,
    (selectedWindowEnergy large X <
      (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) ↔
        0 < aeval X window)
  in_window : 0 < aeval (coordinates root) window
  stationary : Stationary (by omega) (canonicalHalfWord m) root
  polynomial_root : ∀ q,
    aeval root (polynomials (by omega) (canonicalHalfWord m) q) = 0
  system_iff : ∀ Y : Variables m → ℝ,
    0 < aeval (coordinates Y) window →
    ((∀ q, aeval Y (polynomials (by omega) (canonicalHalfWord m) q) = 0) ↔
      Stationary (by omega) (canonicalHalfWord m) Y)
  unique_root : ∀ Y : Variables m → ℝ,
    0 < aeval (coordinates Y) window →
    (∀ q, aeval Y (polynomials (by omega) (canonicalHalfWord m) q) = 0) →
    Y = root
  rational_nonsingular :
    (rationalJacobian
      (systemExpression (by omega) (canonicalHalfWord m)) root).det ≠ 0
  polynomial_nonsingular :
    (polynomialJacobian
      (polynomials (by omega) (canonicalHalfWord m)) root).det ≠ 0
  algebraic : ∀ q, IsAlgebraic ℚ (root q)
  geometric_algebraic : ∀ j,
    IsAlgebraic ℚ
      (configuration (by omega) (canonicalHalfSign m) (coordinates root) j).re ∧
    IsAlgebraic ℚ
      (configuration (by omega) (canonicalHalfSign m) (coordinates root) j).im
  distances_algebraic : ∀ i j, IsAlgebraic ℚ
    ‖configuration (by omega) (canonicalHalfSign m) (coordinates root) i -
      configuration (by omega) (canonicalHalfSign m) (coordinates root) j‖
  extremal : DiameterExtremal
    (configuration (by omega) (canonicalHalfSign m) (coordinates root))
  maximum : M (2 * m) = discriminant
    (configuration (by omega) (canonicalHalfSign m) (coordinates root))
  maximum_algebraic : IsAlgebraic ℚ (M (2 * m))

/-- The selected algebraic certificate above the concrete even-order threshold. -/
def CertificateAboveThreshold : Prop :=
  ∀ m : ℕ, evenThreshold ≤ 2 * m → Nonempty (Certificate m)

end Algebraic

/-- All public conclusions; proved together in `Erdos1045.Proof`. -/
def Claims : Prop :=
  DiameterCharacterization ∧ PerimeterCharacterization ∧ NormalizedLimits ∧
    Algebraic.CertificateAboveThreshold ∧ KKT.UniquePositiveKKT

end
end Erdos1045.Statement

namespace Erdos1045

/-- Diameter and perimeter characterizations with their concrete thresholds,
the parity limits, the thresholded algebraic certificate, and eventual positive KKT. -/
theorem main : Statement.Claims := by
  sorry

end Erdos1045
