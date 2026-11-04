# Thermal finite collision core

Lean checks the finite rational collision core and the positive local weights and coded entry programs for the three specified models, relative to the Z^2 full-shift specialization of Kari and Taati's Corollary 21 (arXiv:1311.2319v3; Corollary 4 in the journal version). It does not certify the paper's thermal or undecidability conclusions.

## Exact scope

This package checks the finite rational collision reduction for cellular automata on the two-dimensional infinite full shift: finite-law normalization and restriction, exact integer numerators and denominator bounds, coefficient nonnegativity and detection, disjoint-support factorization, connected positive witnesses, W as the positive-coefficient expansion, and the rational positive local weights and complete finite table coverage for the three specified models. Uniform primitive-recursive programs evaluate every coded table entry and exhaustively test finite candidates, returning only nonempty positive witnesses with no smaller nonempty positive subset; every returned witness is connected, and every nonsurjective coded CA has a successful stage. The programs' equality, soundness, and this existence-completeness property are proved. The onto-to-uniform direction is relative to the explicitly supplied, model-independent hypothesis PublishedCA.KariTaati_Corollary21, whose measure is the actual uniform Bernoulli product measure. The published theorem is not proved here. This package proves no finite-volume stochastic comparison, infinite-volume thermal theorem, pressure differentiability result, Gibbs uniqueness theorem, or undecidability theorem; it does not certify the paper's selected main results.

## Pins

- Lean `leanprover/lean4:v4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
- Unmodified Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- All transitive revisions are frozen in `lake-manifest.json`.
- `Thermal/Audit.lean` prints the axioms of all 177 thin-core theorem declarations, including `witness_search` and `weight_table_computable`.

## Build and verify

Install the pinned Lean toolchain and the pinned dependency sources and Mathlib cache. In a normal connected checkout, the preparation commands are:

```sh
lake update
lake exe cache get
```

Then one command compiles the thin core, checks the complete axiom audit, exports both comparator environments, and replays the solution in Lean's kernel:

```sh
python -B verify.py
```

The verifier performs no downloads and runs one compiler at a time with `LEAN_NUM_THREADS=1`, `-j1 -M6144`. On Windows it enforces a 10,000,000,000-byte process-tree commit cap; on Unix it applies a 10,000,000,000-byte address-space limit. Its logs, exports, timings and peak memory are written to `work/`. An existing offline cache can be selected explicitly:

```powershell
python -B verify.py --dependency-dir "PATH/TO/cached/packages" --lean-bin "PATH/TO/lean-4.35.0/bin"
```

The dependency directory must contain Mathlib and its sibling packages, each with its cached `.lake/build/lib/lean` directory. Missing external artifacts are compiled serially. Mathlib source compilation uses its pinned `maxSynthPendingDepth=3` setting.

## Comparator challenge

`Challenge.lean`, `Solution.lean` and `comparator.json` use the [leanprover/comparator configuration format](https://github.com/leanprover/comparator). They cover every one of the 177 audited finite theorems. Each challenge statement is the fully explicit type of the corresponding theorem; the solution supplies that theorem's checked proof. Only `propext`, `Quot.sound` and `Classical.choice` are permitted. The challenge intentionally contains placeholder proofs, as required by this challenge format; the solution and the thin-core proof modules contain no admissions.

Lean 4.35.0 includes the comparator. On a supported Linux installation with bubblewrap, the native source-build command is:

```sh
lake comparator --config comparator.json
```

`verify.py` compares newly generated exports with the pinned toolchain. On Windows it uses `--inadvisably-no-sandbox`; the package and exporter must be trusted. Use the sandboxed Linux command for an untrusted solution. Git for Windows supplies required `which`/`env` lookup helpers; no git process runs when both exports are supplied. See the [pinned comparator implementation](https://raw.githubusercontent.com/leanprover/lean4/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/lake/Lake/CLI/Check.lean). Exports include the comparator's required primitive constants and quotient declarations. Keep the challenge and its trusted imports fixed when reviewing another solution.

## Published input and source cleanliness

The sole published hypothesis used by this finite reduction is the explicit `PublishedCA.KariTaati_Corollary21` parameter. See [Kari and Taati, arXiv:1311.2319v3, Corollary 21, printed page 20](https://arxiv.org/pdf/1311.2319v3#page=20), which is Corollary 4 in Section 3.1 of the [journal version](https://doi.org/10.1007/s10955-015-1281-2) and `Thermal/BalanceSource.lean`. This parameter does not appear as a new axiom in `#print axioms`.

The proof sources use unmodified pinned Mathlib, including its `maxSynthPendingDepth=3` compiler setting.

## License

Copyright 2026 Seth Douglas and Nidhal Mghirbi. Under the scheme in [RIGHTS.md](../RIGHTS.md), documentation and recorded outputs are CC BY 4.0; the Lean proof sources and scripts are dual licensed under MIT or Apache 2.0, at the user's option. See the three license files and NOTICE in the parent directory. These grants do not alter rights in Mathlib, Lean, or other third-party material.
