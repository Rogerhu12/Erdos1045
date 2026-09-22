# Explicit thresholds

The diameter characterization, algebraic certificate and positive KKT
certificate in `Erdos1045.main`
directly use the concrete even-order cutoff

$$
N = 2^{10^{120}}.
$$

For every even order `n = 2m ≥ N`, it gives attainment, uniqueness up to
relabelling and direct Euclidean rigid motions, the canonical diameter graph,
reflection symmetry, third-turn symmetry when `3 ∣ m`, and the unique
nonsingular algebraic stationary certificate in one polynomial window.
The certificate also proves that its selected configuration is a global
diameter maximizer, and that its coordinates, distances and maximum value
are algebraic over `ℚ`.

## Statement and proof

- `Erdos1045/Statement.lean` defines the five public conclusions and their
  thresholds; its sole import is Mathlib. `Challenge.lean` mirrors this
  statement and adds one deliberate theorem hole.
- `diameterThreshold n` chooses `regularThreshold` at odd orders and
  `evenThreshold` at even orders. `DiameterCharacterization` and
  `PerimeterCharacterization` state their conclusions at these cutoffs.
  `Algebraic.CertificateAboveThreshold` and `KKT.UniquePositiveKKT`
  use `evenThreshold` directly.
- `Erdos1045/ExplicitStatement.lean` contains implementation-only parity
  packages. They help assemble the public diameter theorem and are not
  additional submitted claims.
- `Erdos1045/ExplicitProof.lean` proves the even package;
  `Internal/StructuralNote/ExplicitEvenThreshold.lean` assembles its finite
  analytic, geometric and algebraic arguments, and `ExplicitEvenNumerical.lean`
  proves the displayed integer dominates their component thresholds.
- `scripts/AuditExplicitFinal.lean` checks the transitive axioms of these
  endpoints. `scripts/Audit.lean` checks the combined five-part theorem.

`evenThreshold` is an ordinary computable `Nat` expression. The proof compares
exponents and rational bounds; it never constructs the decimal or binary
expansion of `N`. Its decimal expansion would have approximately
`3.0103 × 10^119` digits.

## Quantitative proof components

The finite Fourier comparison uses order `2^200`. The physical localization
estimate is bounded by `2^100000000` at the required edge tolerance. The local
coordinate, pressure, balancing, strict-concavity and rational-window modules
prove their own finite thresholds; the final numerical module combines them.
The pressure-margin estimate is the source of the much larger overall bound.

## Odd diameter and perimeter

The same global localization applies to every perimeter extremizer, without
a parity restriction. At relative edge error below `1/4000`, the proved
uniform local rigidity theorem forces the extremizer to be regular. The
explicit localization threshold at this tolerance is at most

$$
n_{\mathrm{reg}} = 2^{100\,000\,000}.
$$

`Internal/EventualExact/ExplicitPerimeter.lean` proves this pointwise
regularity, the sharp homogeneous perimeter bound and the odd diameter-two
formula. The odd result follows by the proved perimeter-diameter inequality
and the regular polygon's equality case.

`Erdos1045/ExplicitRegularProof.lean` connects these results to the literal
suprema `M` and `W`, including attainment, regularity and uniqueness up to
direct rigid motion and relabelling. `Erdos1045/Proof.lean` combines the two
parities into `DiameterCharacterization`. Thus each result appears once in
the five-part public `Claims`, with its quantitative threshold built in.

Both threshold constants are computable natural-number expressions. The
proofs compare their sizes without expanding the enormous integers.

## Positive KKT certificate

Every even-order diameter maximizer with `2m ≥ 2^(10^120)` has the complete
active edge family, independent squared-distance constraint differentials,
and a unique multiplier family that is strictly positive on every active
edge and satisfies stationarity and complementary slackness.

`Internal/StructuralNote/ExplicitKKTThreshold.lean` proves this at the same
even cutoff. Its construction supplies the following quantitative inputs:

- Saturated matching coordinates and exactly one active crossing per pair.
- Small geometric coefficients, positive radial gain and derivative bounds.
- The strict pressure margin controlling crossing variations.
- Projection into the fixed-Schur domain, the selected chart representation,
  and the chart's geometric properties.

The resulting `ActualKKTConditions` feed the existing pointwise multiplier
positivity theorem. Transport back to the original labelled configuration
preserves the coefficients, and linear independence gives uniqueness.
`Erdos1045/Internal/KKT.lean` packages the result as `KKT.UniquePositiveKKT`,
the fifth conjunct of the public theorem. No existence-only order threshold
is used as an input to this construction.

## Checking

After building the project, run:

```sh
lake env lean scripts/AuditExplicitFinal.lean
```

The audit permits only `propext`, `Classical.choice` and `Quot.sound`.
The Comparator configuration compares `Erdos1045.main`, so the explicit result
is part of that comparison surface. The threshold constants, parity selector and quantitative characterizations
are listed among the compared definitions. The independent
Comparator/NanoDa run can be invoked with `scripts/verify-comparator.sh`.
