# Mathematical source

## Manuscript and formalization

Boyang Hu, *Eventual maximizers of the planar distance product*, revised
September 22, 2026. The manuscript is included as
[LaTeX source](../paper/Erdos1045.tex) and [PDF](../paper/Erdos1045.pdf).

The proof snapshot accompanying this manuscript is identified by

```text
sha256:11dea5d09e39e784f4b84145b80264db577aae4fdabcaf0f7bacdb38fd6ba335
```

This is the SHA-256 digest of [PROOF_SHA256SUMS](../PROOF_SHA256SUMS).
That manifest lists the normalized bytes of all 916 Lean source and audit
files, together with `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`
and `comparator.json` (920 files in total). The manuscript uses the prefix
`11dea5d09e39e784`. This content identifier is independent of Git history.

All manifest paths are relative to the repository root. Text files use LF
line endings. [SHA256SUMS](../SHA256SUMS) covers the complete release,
including the manuscript, documentation and proof manifest; it excludes only
itself. Recompute the manifests when preparing a changed release.

The initial mathematical draft was generated using GPT-6 Pro. The Lean
formalization was developed using OpenAI Codex agents under human direction;
the resulting formal proofs were checked by Lean 4. The proof adaptations
are described in Appendix B, `README.md` and `formalization.yaml`. The
verification record is in [VALIDATION.md](VALIDATION.md).

The formal diameter and algebraic statements use the concrete even-order
cutoff `2^(10^120)`. The odd diameter and perimeter statements use the common
cutoff `2^100000000`. The positive KKT statement also uses `2^(10^120)`.
Together with the normalized parity limits, these are the five conclusions
of `Erdos1045.main`.
