# Manuscript

Boyang Hu, *Eventual maximizers of the planar distance product*,
revised September 22, 2026.

- `Erdos1045.pdf`: the paper, including both appendices and the AI disclosure.
- `Erdos1045.tex`: the complete LaTeX source, including tables and references.

Compile from this directory with a TeX distribution that includes XeLaTeX
and the standard packages listed in the source. Run until cross-references
stabilize; three passes suffice from a clean directory for this version:

```sh
xelatex -no-shell-escape -interaction=nonstopmode -halt-on-error Erdos1045.tex
xelatex -no-shell-escape -interaction=nonstopmode -halt-on-error Erdos1045.tex
xelatex -no-shell-escape -interaction=nonstopmode -halt-on-error Erdos1045.tex
```

Repeat the command if the final log still requests a rerun. The source
snapshot accompanying this paper is identified in
[docs/SOURCE.md](../docs/SOURCE.md).

The Lean project is in the parent directory. Its public entry is
`Solution.lean`, exporting `Erdos1045.main`. Build and verification instructions
are in the project's `README.md`.

The five public statements use the proved cutoffs directly:

- Diameter: `2^100000000` for odd orders, `2^(10^120)` for even orders.
- Perimeter: `2^100000000`, with no parity restriction.
- Selected algebraic certificate: even orders at least `2^(10^120)`.
- Positive KKT certificate: even orders at least `2^(10^120)`.
- The two normalized parity limits form the remaining statement.

The paper's main, perimeter, positive-multiplier and algebraic theorems
state these thresholds directly.
Section 5 explains the quantitative localization-and-rigidity step, and
Appendix B describes the corresponding Lean statements and proof route.

Appendix A's twenty endpoint signs and ten primitive enclosures are proved by
`StructuralNote.FixedDualTable.certified_table`. Its two integral bounds are
proved by `half_dualNorm_bound` and `one_dualNorm_bound` in
`StructuralNote.FixedDualNormBounds`.
