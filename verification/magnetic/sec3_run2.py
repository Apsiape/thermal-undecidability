"""Second runner for Section 3 (16/17-edge cases): exact certificates with networkx min-cut (float);
bisections and box sweep with the fast int-scaled engine."""
import time
from sec3_checks import *
from common import max_upset_networkx, max_upset_scipy
grid = [(LOG2, 0.0), (LOG2, 0.5), (LOG2, 3.0), (LOG2 - 0.3, 1.0)]
run_torus(4, 2, [(0, 0), (1, 0), (2, 0)], 'nx', grid, "triple in a row")
run_torus(4, 2, [(0, 0), (1, 0), (0, 1)], 'nx', grid, "L-shape triple")
run_wired_box(5, 4, [(0, 0), (1, 0)], 'sp')
D = setup_wired_box(5, 4, [(0, 0), (1, 0)])
kap = 1 / 3
for g in [0.5, 2.0]:
    nu_end = measure(D, LOG2, g, openvar='openA', thetaH_rest=LOG2)
    phi = measure(D, LOG2 - kap * g, 0.0, openvar='openA', thetaH_rest=LOG2)
    t = time.time()
    v = max_upset_networkx(nu_end - phi, D['nE'])[0]
    print("  box (13) g=%.1f exact (networkx) max_U = %.2e  [%.0fs]" % (g, v, time.time() - t))
