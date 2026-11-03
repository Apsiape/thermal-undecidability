# Spontaneous magnetization and thermal decay are undecidable at positive temperature

Seth Douglas and Nidhal Mghirbi. Version 1.1.0, 3 November 2026. Concept DOI (all versions): [10.5281/zenodo.23924357](https://doi.org/10.5281/zenodo.23924357). Version 1.0.0: [10.5281/zenodo.23924358](https://doi.org/10.5281/zenodo.23924358). Version 1.1.0: [10.5281/zenodo.23933148](https://doi.org/10.5281/zenodo.23933148).

**This is a preprint. It has not been peer reviewed.**

## Abstract

Spontaneous magnetization is undecidable at a fixed positive temperature for translation-invariant finite-range classical lattice models with strictly positive rational Boltzmann weights. A computable family on 2304 local states has maximal visible nine-colour Potts magnetization exactly zero or a fixed positive constant, attained in a translation-invariant Gibbs state. Its pressure in a uniform field is uniformly computable, but differentiability at zero field is undecidable with a fixed derivative-jump gap. Rational weights are asserted at zero field.

We also prove undecidability of exponential decay of one specified thermal spin correlation, in every Gibbs state, on 512 local states. Both constructions couple critical visible spins to cellular-automaton replicas. Surjectivity cancels the collision corrections; nonsurjectivity gives strict subcritical bond domination and exponential decay of the specified correlation uniformly over states. The interaction range depends on the input, and the branches are fine-tuned at their critical or coexistence points. The results transfer to diagonal quantum interactions and survive a prescribed output-reset noise family, the same construction with reduced retention. A larger Potts family on 16,908,544 local states makes Gibbs uniqueness undecidable: nonsurjective inputs have a unique state with uniform exponential clustering of all local observables; surjective inputs have at least 66,050 states, including a disordered state with the same bound. Uniqueness for the 512- and 2304-state families remains open.

## Changes in version 1.1.0

Adds Gibbs uniqueness and full clustering at a larger first-order Potts point, with a complete selector/swap proof and exact constants. The original nine-colour and Ising theorems are unchanged. Version 1.0.0 remains available at https://doi.org/10.5281/zenodo.23924358.

## Contents and reproduction

- `paper/main.pdf`: manuscript.
- `paper/`: LaTeX source, bibliography, plain-text abstract, source manifest, source archive and strict build driver. Run `python -B build.py` there with pdflatex and BibTeX installed.
- `verification/`: exact and numerical finite checks, recorded outputs and reproduction commands. Start with `verification/README.txt`. Run `python -B exact_checks.py` for the independent exact check and `python -B run_all.py` for the full 20-job replay; each replay uses a fresh output directory.
- `SHA256SUMS`: SHA-256 hashes for every public file except itself.
- `verification/SHA256SUMS`: SHA-256 hashes for public files except the two checksum files. Run `python -B check_hashes.py` from `verification/`.

Finite computations support the written proofs. They do not establish infinite-volume transitions, the all-state result, a variational principle or undecidability.

## Citation and rights

See `CITATION.cff` for citation metadata.
Paper and documentation: CC BY 4.0. Scripts: MIT or Apache 2.0, at your option. See `RIGHTS.md`, the license files and `NOTICE`.
