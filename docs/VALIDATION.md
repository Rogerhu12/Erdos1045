# Verification record

## Proof snapshot

The proof snapshot is `11dea5d09e39e784`; its full SHA-256 identifier and
920-file manifest are described in [SOURCE.md](SOURCE.md). All 916 Lean source
and audit files, the toolchain, dependency manifest and Comparator configuration
are unchanged by the repository cleanup.

The development pins Lean 4.33.0 and Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`.

| Check | Result |
| --- | --- |
| Full CI build | Passed: 9,609 jobs, including `Solution`. |
| Lean kernel replay | Passed: Comparator replayed the exported Solution in Lean's default kernel. |
| Transitive axiom audit | Local audit passed for `Erdos1045.main` and all 21 explicit-threshold audit declarations; only `propext`, `Classical.choice` and `Quot.sound` occur. |
| Statement comparison | Local comparison matched seven selected definitions, the main theorem type and 35,450 transitive statement-dependency constants in separately loaded environments. |
| NanoDa replay | Did not complete: the pinned checker panicked with `memory overflow` in `num-bigint` exponentiation. |

The full build and Lean replay are recorded in the
[archived CI run](https://github.com/Rogerhu12/Erdos1045-history-20260922/actions/runs/35684837915)
of September 22, 2026. That run checked the same proof manifest. Its overall
status is failure because of the NanoDa panic; it is not a successful NanoDa
or complete Comparator run. The axiom and statement-comparison results above
come from the local validation of this proof snapshot.

## Continuous integration

CI uses `scripts/verify-comparator.sh --lean-only`. This mode derives a temporary
configuration from `comparator.json`, changing only `enable_nanoda` to `false`.
It retains the same theorem, definitions and permitted axioms, the sandboxed
Challenge/Solution builds, statement comparison, and Lean kernel replay.
Failures still fail the job. The explicit-threshold axiom audit follows it.

The committed `comparator.json` retains NanoDa for manual replay and the
submission configuration. The default script invocation still runs NanoDa;
it is never silently retried or counted as passed. The pinned checker has no
size limit on natural-number exponentiation, so the concrete cutoff
`2^(10^120)` cannot safely be expanded to a numeral by that implementation.

CI runs once per main-branch push or pull request, with superseded runs
cancelled. Publishing a tag does not launch a duplicate build.

## Reproduce the checks

```sh
lake exe cache get
python verify.py --fresh
lake env lean --run scripts/CompareSurface.lean
```

The fresh build removes this project's generated Lake outputs and rebuilds
from source; the pinned Mathlib cache can still be reused. For sandboxed
Comparator verification on Linux:

```sh
bash scripts/verify-comparator.sh --lean-only
```

Omit `--lean-only` to request NanoDa as well; Rust/Cargo is then required.
The checked-in script pins Comparator, lean4export, NanoDa and Landrun.

## Release integrity

The source-layout check covers 903 Solution-side files, a 669-line Challenge
with only a Mathlib import, and nine pinned dependencies. The Challenge's
single deliberate theorem hole is excluded from the Solution axiom audit.
The accompanying 41-page PDF and mathematical sources are unchanged in this
cleanup. Its full-file manifest can be checked alongside the proof manifest:

```sh
sha256sum -c PROOF_SHA256SUMS
sha256sum -c SHA256SUMS
```
