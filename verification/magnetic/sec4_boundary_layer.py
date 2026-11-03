"""Boundary layer: with a FIXED hidden boundary adjacent to e, the insertion ratio can drop below 1 (even below
1 + a_P when a witness is completed). This is why Section 4 must work with infinite-volume ratios R_inf."""
import numpy as np
from sec4_checks import make_w, ratio, selector, and2
for (nm, q, f) in [('selector', 4, selector), ('AND', 2, and2)]:
    w = make_w(q, f, 0.9)
    S = q * q
    for h in [0, 1, 2]:
        mn = np.inf
        n = 2 * h + 1
        for trial in range(2000):
            rng = np.random.default_rng(trial)
            closed = rng.random(n) < 0.7
            closed[h] = False
            lb, rb = int(rng.integers(S)), int(rng.integers(S))
            mn = min(mn, ratio(w, q, closed, h, lb, rb))
        print("%s eps=0.9: e at distance %d from a fixed hidden boundary: min ratio = %.4f" % (nm, h, mn))
