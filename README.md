# Eventual maximizers of the planar distance product

Lean 4 formalization, licensed under Apache-2.0.

Author and maintainer: **Boyang Hu**.
This repository contains the paper and its Lean 4 formalization, determining
the maximizing configurations in Erdős problem 1045 for all sufficiently
large orders.

## Paper

The accompanying manuscript is available as [PDF](paper/Erdos1045.pdf) and
[LaTeX source](paper/Erdos1045.tex), revised September 22, 2026.
The accompanying proof snapshot is identified in
[docs/SOURCE.md](docs/SOURCE.md) by the SHA-256 digest of
[PROOF_SHA256SUMS](PROOF_SHA256SUMS).
See [paper/README.md](paper/README.md) for compilation instructions.
Appendix A's table and integral bounds are proved in the Lean development;
Appendix B describes all five formal conclusions, including explicit
even-order, odd-order, perimeter and positive KKT thresholds, and records the differences in proof route. See
[the explicit threshold proof](docs/EXPLICIT_THRESHOLD.md) for quantitative details.

## Mathematical results

For labelled points `z : Fin n → ℂ`, the discriminant is

```math
\Delta(z)=\prod_{i}\prod_{j\ne i}\lvert z_i-z_j\rvert
         =\prod_{i\lt j}\lvert z_i-z_j\rvert^2.
```

`M n` is the supremum for diameter at most 2. `W n` is the supremum
for convex-hull perimeter at most `2π`. Perimeter is defined by the integral
of the support function; a segment has twice its length as perimeter.

The main theorem is `Erdos1045.main : Erdos1045.Statement.Claims`.
Its five conjuncts assert:

1. **Diameter characterization.** For odd `n ≥ 2^100000000` and even
   `n ≥ 2^(10^120)`, `M n` is attained and maximizers are unique up to
   relabelling and a direct Euclidean rigid motion. For odd `n`, every
   maximizer is regular and `M n = n^n / cos(π/(2n))^(n(n-1))`.
   For even `n = 2m`, `CanonicalEvenDiameterAdj` describes every diameter
   edge after relabelling; reflection symmetry is forced, and a nontrivial
   third-turn symmetry is forced when `3 ∣ m`.
2. **Perimeter characterization.** For every `n ≥ 2^100000000`, the maximum
   is attained and equals `n^n * (π/(n*sin(π/n)))^(n(n-1))`. All maximizers
   are regular and are unique up to direct rigid motion and relabelling.
3. **Normalized parity limits.** `M(2m)/(2m)^(2m)` tends to
   `3^(9/4)/8 * exp((π² - 2√3π)/8)` and
   `M(2m+1)/(2m+1)^(2m+1)` tends to `exp(π²/8)`.
4. **Algebraic certificate.** For every even `n = 2m ≥ 2^(10^120)`, the
   specified stationary polynomial system has a unique root in its selected
   window, with nonsingular rational and polynomial Jacobians. It describes
   a global maximizing configuration; root coordinates, geometric coordinates,
   distances and the maximum value are algebraic over `ℚ`.
5. **Positive KKT certificate.** For every even order `n = 2m ≥ 2^(10^120)`,
   every diameter maximizer has an exactly specified active set, linearly independent
   squared-distance differentials, and unique strictly positive multipliers
   satisfying stationarity and complementary slackness.

The finite thresholds are part of the diameter, perimeter, algebraic and
positive KKT statements themselves. The even-order conclusions share the
same cutoff `2^(10^120)`. See [the threshold proof](docs/EXPLICIT_THRESHOLD.md) for the
component bounds and verification entry point.

## Statement and proof

- `Erdos1045/Statement.lean` defines the five claims using only Mathlib.
  `regularThreshold = 2^100000000`, `evenThreshold = 2^(10^120)`, and
  `diameterThreshold n` selects the appropriate bound by parity.
- `Challenge.lean` mirrors that statement and adds one deliberate main
  theorem hole. `scripts/check_submission.py` checks their agreement.
- `Erdos1045/Proof.lean` proves `Erdos1045.main`. The parity-specific
  proof packages in `ExplicitStatement.lean` are implementation helpers
  for these five public conclusions. `Erdos1045/Internal/` connects
  the public definitions to the development in `Internal/`.
- `Solution.lean` imports the completed proof.
- `comparator.json` selects `Erdos1045.main` and explicitly lists the
  threshold constants and thresholded characterizations. It permits only
  `propext`, `Classical.choice` and `Quot.sound` and retains a configuration for
  optional independent NanoDa checking.

## Reproducible build

Install [elan](https://github.com/leanprover/elan), Git and Python 3.11 or later.
The repository pins Lean 4.33.0 and Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`; all transitive dependencies are pinned
in `lake-manifest.json`.

```sh
lake exe cache get
python build.py
python verify.py --no-build
```

`python verify.py` performs the layout check, a Lake build, and the transitive
axiom audit. `python verify.py --fresh` first removes this project's generated
Lake build outputs. Mathlib's pinned cache can still be reused.
The Challenge's one warning about its deliberate `sorry` is expected; it is
excluded from the solution audit.

For an additional local comparison of the compiled statement definitions in
separate environments, run `lake env lean --run scripts/CompareSurface.lean`.

The sandboxed Comparator check needs Linux, Go 1.24 or later, elan, and a
working unprivileged systemd user scope:

```sh
bash scripts/verify-comparator.sh --lean-only
```

CI runs this pipeline: it compares Challenge and Solution, enforces the three
permitted axioms, and rechecks the exported proof with Lean's kernel. A full
9,609-job build and Lean kernel replay have passed for this proof snapshot.
The pinned NanoDa checker overflows while evaluating a large natural-number
power, so CI omits that additional checker. To run it manually, install
Rust/Cargo and omit `--lean-only`. All checker dependencies are pinned.
See [docs/VALIDATION.md](docs/VALIDATION.md) for the verification record.

To verify the exact source and release files before building, run from
the repository root:

```sh
sha256sum -c PROOF_SHA256SUMS
sha256sum -c SHA256SUMS
```

## Sources and proof adaptations

The source manuscript, *Eventual maximizers of the planar distance
product*, is included in `paper/`. `docs/SOURCE.md` identifies the source
and accompanying proof snapshot.
`formalization.yaml` records provenance and mathematical classification.

The implementation retains an exterior-map/Faber route for global analytic
localization, establishes saturation by feasible lens-coordinate variations
before introducing KKT, and proves finite-kernel monotonicity from difference
identities and value convergence. The diameter graph is expressed by the
explicit cyclic adjacency predicate `CanonicalEvenDiameterAdj`.

## Contributions

The initial mathematical draft was generated using GPT-6 Pro. The Lean
formalization was developed using OpenAI Codex agents (Astra, Sol and Luna),
with human direction of scope and proof-route choices. The resulting formal
proofs were checked by Lean 4. The author is responsible for the manuscript
and for the correspondence between its mathematical statements and the
formal statements. `formalization.yaml` records the contributors, tools
and development process.
