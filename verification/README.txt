Finite verification for
Spontaneous magnetization and thermal decay are undecidable at positive temperature
Seth Douglas and Nidhal Mghirbi, Version 1.1.0, November 2026

Run every command below from this verification/ directory.

Quick independent exact check (Python standard library only):
  python exact_checks.py

Full replay, including every standalone script in both review suites:
  python run_all.py

The full replay runs two processes at a time. Symbolic enumeration, 16/17-edge
network-flow/LP comparisons and 18-edge torus screening can take substantially
longer than the quick check. Results are written to a fresh runs/run-* directory. To choose it explicitly:
  python run_all.py --output PATH-THAT-DOES-NOT-EXIST
Its logs/, versions.json and run-results.json do not replace the shipped records. The runner checks exit codes; printed diagnostics also need
interpretation as described below.

Environment used for this release:
  Python 3.13.12
  NumPy 2.4.3
  SciPy 1.17.1
  SymPy 1.14.0
  NetworkX 3.6.1
  mpmath 1.3.0
Install matching versions:
  python -m pip install numpy==2.4.3 scipy==1.17.1 sympy==1.14.0 networkx==3.6.1 mpmath==1.3.0

Provenance
----------
fk_route/ contains all six scripts from the earlier FK-route review. magnetic/
contains the later magnetic review's common module, seven standalone check
scripts and its original text outputs. The two reviews were separate checks of
the derivations. Their mathematical code and terminology are retained; this README
clarifies their numerical scope. originals.zip preserves the received check
files with LF text and neutral descriptions in process comments. Only sec3_checks.py has a replay-selection adaptation: its
mathematical functions are unchanged; the original large LP grid is optional
because sec3_run2.py covers larger cases with the independent flow engine.

exact_checks.py is a further implementation using fractions.Fraction and exact
integer counts. It imports neither review suite. It checks collision positivity,
the W expansion, an XOR control, disjoint-support factorization, 16 witness-
completion cases, the comparator lattice condition, two stochastic dominations
and the covariance inequality for all 20 up-sets of a three-edge cube, an exact
negative control, output-reset scaling, both rational counterexample certificates,
a real exact single-site Dobrushin matrix row-sum calculation (all hidden
boundary assignments, all retained touching factors, and visible conditionings),
a 2x2 cycle-graph version of both dominations and the covariance inequality on
all 168 up-sets, the -t^2/16 non-attractiveness certificate, a finite exhaustive
sliding-decoder/residue identity, and a finite Gibbs trace algebra sanity check.
The trace check does not test the infinite-volume KMS correspondence.

Standalone commands and scope
-----------------------------
python fk_route/claim2_identities.py
  Collision and reset identities. Its bounded Garden-of-Eden search is only a
  preliminary screen: five MISMATCH lines are expected because absence of a short
  forbidden word does not decide surjectivity.

python fk_route/surj_decide_1d.py
  Resolves those same examples with an exact finite de Bruijn construction.
  All 28 examples agree with the collision test. The decision logic is exact;
  some displayed collision expectations use floating point.

python fk_route/counterexample27.py
  Exact symbolic selector identities and failure of log-supermodularity.

python fk_route/fkg_tests.py
  Finite FK weights, association diagnostics, stochastic comparison and the
  comparator lattice condition. Negative target covariances are intentional.

python fk_route/extra_checks.py
  Additional association counterexamples, factorization and comparison.

python fk_route/dobrushin_check.py
  Sampled finite single-site influence checks.

python magnetic/sec2_checks.py
  Collision/witness/comparator checks with two finite optimization engines.

python magnetic/sec3_checks.py
  Covariance and integrated domination on tori and wired boxes. NetworkX uses
  floating capacities; HiGHS uses floating-point linear programming.
  The default replays 3x2 cases; run_all.py separately runs sec3_run2.py for larger
  cases, matching the supplied review's completed logs. To additionally run the
  original redundant large LP grid:
    python magnetic/sec3_checks.py --full-lp
  That extended replay was stopped after 1,304 seconds without a mathematical
  failure. Its completed independent flow counterpart passed.

python magnetic/sec3_run2.py
  Alternative 16/17-edge runs; flow-screening used for bisections and box sweep.

python magnetic/sec3_torus33.py
  18-edge torus screening with integer capacities scaled from floating weights.
  The printed rounding bound limits the certificate: a small displayed value is
  not a proof of exact zero for every increasing event.

python magnetic/sec4_checks.py
  Hidden insertion locality, conditional contraction and exact-form bond odds.

python magnetic/sec4_boundary_layer.py
  Demonstrates the fixed-hidden-boundary insertion-ratio qualification.

python magnetic/sec44_criticality.py
  Algebraic critical-point checks and numerical cylinder spectra.

common.py is import-only; it has no standalone test entry point.

Interpretation
--------------
"Exact domination" in older script comments means exhaustive finite state-space
optimization, not exact real arithmetic. The new checker supplies literal
rational checks on smaller examples. No finite computation here proves an
infinite-volume statement, a critical exponent or undecidability. Those
conclusions depend on the written proofs and cited external theorems.

Hash verification
-----------------
SHA256SUMS identifies every public file apart from the two checksum files
and generated build/, runs/ and __pycache__ content; paths are relative to this
verification/ directory. The root ../SHA256SUMS also covers this checksum file
and omits only itself from the public files; its paths are relative to the root.
  python check_hashes.py
Rerunning run_all.py leaves shipped records and hashes unchanged. New outputs
are under runs/ by default; these local replay directories are not release files.
Original recorded outputs are in magnetic/; release replay records are under logs/.

Potts extension (17-job replay)
------------------------------
python potts/collision_checks.py
  Byte-identical independent review checker; exact collision identities, witness
  bounds and the necessary multiplier |A|. Its printed final verdict is checked
  in the release audit, since the original script does not raise on a false flag.
python potts/fk_q9_checks.py
  Byte-identical independent review checker; finite nine-colour FK expansion,
  boundary magnetization, sampled increasing-event anchor covariance and both
  endpoint dominations, including real CA weights in BOTH orientations.
  It uses floating-point arithmetic. Tiny positive roundoff values are recorded;
  the intentional kappa=1 stress violation is a negative control, not a failure.
  Printed numerical inequalities are checked in the release audit as well as
  process exit status; the original checker mainly prints diagnostics.
python potts/exact_q9_checks.py
  New exact checker with assertions. Direct spin sums and bond sums give the
  wired-boundary magnetization identity exactly. A real two-site MAJ3 witness
  is rewarded in BOTH orientation layers on a seven-edge graph. Integer-flow
  certificates give monotone couplings for target <= rewarded comparator <=
  displaced FK, certifying every increasing event, free and wired.
  A slightly smaller admissible reward is chosen so the endpoint odds and
  rational interpolation points can be represented by fractions exactly;
  the manuscript's analytic proof uses its full normalized reward.
  The script also checks exact conditional closure bounds and enumerates actual
  oriented edges and retained translates in a 9x9 vertex box, verifying that all
  36 H edges and all 36 V edges in its 6x6 interior core are retained anchors. It requires NetworkX, already listed above.

The independent Potts report supplied six repairs (two orientation layers,
alphabet-sized collision multiplier, separated transition/pressure citations,
1/k reward normalization, variational derivative proof with rationality at zero
field only, and the CA-only alphabet bound). All are incorporated. These checks
validate finite algebra and comparisons; the infinite-volume transition,
all-state result, variational principle and undecidability rest on the proofs.

Release 1.0.0 full replay: replays/release-final/ (logs, run-results.json, versions.json).
Earlier 17-job replay: replays/potts-pass/. Its exact-q9 interior-coverage
message referred only to index bounds; the release checker now enumerates actual
oriented edges and retained translates as described above.
Earlier shipped numerical records are preserved unchanged.


Version 1.1.0 uniqueness extension (20-job replay)
------------------------------------------------
python uniqueness/check_constants.py
  Port of the first review script. Adds exact rational intervals for the mass,
  exact exploration constants, assertions for printed inequalities and stable
  log1p arithmetic for the diagnostic grid. The correlation-length resummations
  and direct conditionally convergent sums are numerical diagnostics only.
python uniqueness/check_lw.py
  Port of the second review script. Adds an independent exact rational mass
  enclosure, exact exploration constants and a 36,000-case rational grid.
  Retains the original 80-digit grid and smaller-Q numerical diagnostics.
  Both scripts also justify the universal inequalities algebraically; a finite
  grid alone is not a proof for all neighbourhoods.
python uniqueness/check_q1681.py
  Standalone standard-library exact rational certificate: mass 0.023,
  kappa < 0.999092, covariance prefactor < 2203, local dimension 430336.
The checked ports are included; their internal source archive is not distributed.
Ports align the Dobrushin row sum with the paired-site coefficient in the paper.
Extra 4*l_w bounds in historical diagnostics are only weaker screening bounds.
Dependency added: mpmath 1.3.0 (arbitrary-precision diagnostics).
Fresh version 1.1.0 replay: replays/v1.1-relocated/.

Replay audit note for version 1.1.0
---------------------------------
The initial relocated 20-job invocation ran the 17 unchanged jobs successfully.
Two new scripts first rejected an illustrative log(20) threshold, which is
insufficient; the manuscript uses the valid log(21) threshold.
The final corrected scripts use exact rational denominator rounding to keep
certificates efficient. All 20 jobs were then rerun in ONE invocation from a
relocated copy into a fresh directory. replays/v1.1-relocated/ contains that
complete final replay, not an aggregation. Its manifest identifies all 20
successful jobs and their current source hashes; the three uniqueness jobs
were rerun along with every other standalone job.
The manuscript build and source archive have also been checked separately.
Regenerate archive, source manifest and all public checksums after a build:
  python -B package_release.py
This excludes local build/, runs/ and __pycache__ directories from public hashes.
