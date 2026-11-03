"""Section 3 on a genuinely 2D 3x3 torus (18 edges, 262144 states): (12) and (13) screened with the fast int-scaled
min-cut engine (any violation it reports is a genuine up-set evaluated in floating point), plus event families."""
import time, sys
import numpy as np
from sec3_checks import setup_torus, measure, cond_open_max, covariance_functional, event_family_ratios, LOG2
from common import max_upset_scipy

for P in [[(0, 0), (1, 0)], [(0, 0), (1, 1)], [(0, 0), (1, 0), (0, 1)]]:
    t0 = time.time()
    D = setup_torus(3, 3, P)
    k = len(P); kap = 3.0 ** (-(k - 1))
    print("torus 3x3, P=%s, k=%d, kappa=%.4f (setup %.1fs)" % (P, k, kap, time.time() - t0)); sys.stdout.flush()
    for (th, s) in [(LOG2, 0.0), (LOG2, 1.0), (LOG2 - 0.5, 2.0)]:
        nu = measure(D, th, s)
        po = cond_open_max(D, nu)
        v, err = max_upset_scipy(covariance_functional(D, nu, kap), D['nE'])
        vbad, _ = max_upset_scipy(covariance_functional(D, nu, 1.0), D['nE'])
        fam, nf = event_family_ratios(D, nu, nrand=200)
        print("  theta=%+.3f s=%.1f: maxP(open H)=%.4f | (12) screened max_U=%.2e (rounding bound %.1e) | "
              "false kappa=1: %.2e | event-family min ratio %.4f (%d events)" % (th, s, po, v, err, vbad, fam, nf))
        sys.stdout.flush()
    for g in [0.3, 2.0]:
        v, err = max_upset_scipy(measure(D, LOG2, g) - measure(D, LOG2 - kap * g, 0.0), D['nE'])
        vb, _ = max_upset_scipy(measure(D, LOG2, g) - measure(D, LOG2 - 1.0 * g, 0.0), D['nE'])
        print("  (13) g=%.1f: screened max_U[nu_{log2,g} - phi_{log2-kappa g}] = %.2e (bound %.1e); "
              "with Delta=g (too strong): %.2e" % (g, v, err, vb))
        sys.stdout.flush()
    print("  time %.1fs" % (time.time() - t0))
