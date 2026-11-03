"""Section 3 checks.

nu_{theta,s}(w) ~ 2^{K(w)} exp(theta * #open horizontal + s * sum_x I_x),  I_x = 1{P+x all closed}, vertical log-odds 0.

(a) conditional horizontal open probability <= 2/3 for theta <= log 2, s >= 0;
(b) the covariance inequality (12): d_s nu(f) <= -kappa d_theta nu(f) for ALL increasing f, checked EXACTLY as
    max_{U up-set} sum_{w in U} nu(w) (G(w) - nu(G)) <= 0,   G = sum_x I_x + kappa * sum_{e in E_H} w_e,
    by max-closure (networkx min-cut; HiGHS LP as second engine);
(c) the best constant kappa* (bisection) versus kappa = 3^{-(k-1)};
(d) the integrated domination (13): nu_{log2,g} <= phi_{log2 - kappa g} exactly (max-closure), and the best Delta*;
(e) negative control: a FALSE constant (kappa=1 for k>=2) must be refuted by the same machinery;
(f) the wired-box version with anchors restricted to translates inside the box.
"""
import sys, time
import numpy as np
from common import (all_states, components_count, connectivity_labels, torus_graph,
                    max_upset_networkx, max_upset_lp, max_upset_scipy)

LOG2 = np.log(2.0)


def setup_torus(L1, L2, P):
    nv, edges, kind, start = torus_graph(L1, L2)
    nE = len(edges)
    st = all_states(nE)
    K = components_count(nv, edges, st)
    H = [e for e in range(nE) if kind[e] == 'H']
    hid = {start[e]: e for e in H}  # horizontal edge by starting site
    trans = []
    for (x, y) in [(x, y) for y in range(L2) for x in range(L1)]:
        trans.append([hid[((p[0] + x) % L1, (p[1] + y) % L2)] for p in P])
    anchors = [t[0] for t in trans]
    assert sorted(anchors) == sorted(H), "anchors must biject with horizontal edges"
    I = np.zeros((len(trans), 2 ** nE))
    for j, t in enumerate(trans):
        I[j] = np.all(st[:, t] == 0, axis=1)
    sumI = I.sum(0)
    openH = st[:, H].sum(1).astype(float)
    return dict(nv=nv, edges=edges, nE=nE, st=st, K=K, H=H, sumI=sumI, openH=openH, trans=trans)


def setup_wired_box(L1, L2, P):
    """Vertices of an L1 x L2 box; all boundary-ring vertices identified into one wired vertex.
    Keep edges with at least one interior endpoint. Anchors: translates P+x with all edges present."""
    def vid(x, y):
        if x == 0 or y == 0 or x == L1 - 1 or y == L2 - 1:
            return 0
        return 1 + (x - 1) + (L1 - 2) * (y - 1)
    nv = 1 + (L1 - 2) * (L2 - 2)
    edges, kind, start = [], [], []
    for y in range(L2):
        for x in range(L1 - 1):
            if vid(x, y) != 0 or vid(x + 1, y) != 0:
                edges.append((vid(x, y), vid(x + 1, y))); kind.append('H'); start.append((x, y))
    for y in range(L2 - 1):
        for x in range(L1):
            if vid(x, y) != 0 or vid(x, y + 1) != 0:
                edges.append((vid(x, y), vid(x, y + 1))); kind.append('V'); start.append((x, y))
    nE = len(edges)
    st = all_states(nE)
    K = components_count(nv, edges, st)
    H = [e for e in range(nE) if kind[e] == 'H']
    hid = {start[e]: e for e in H}
    trans = []
    for y in range(-3, L2 + 3):
        for x in range(-3, L1 + 3):
            sites = [(p[0] + x, p[1] + y) for p in P]
            if all(s in hid for s in sites):
                trans.append([hid[s] for s in sites])
    anchors = [t[0] for t in trans]
    assert len(set(anchors)) == len(anchors)
    I = np.zeros((len(trans), 2 ** nE))
    for j, t in enumerate(trans):
        I[j] = np.all(st[:, t] == 0, axis=1)
    sumI = I.sum(0)
    openH = st[:, H].sum(1).astype(float)
    openA = st[:, anchors].sum(1).astype(float)
    return dict(nv=nv, edges=edges, nE=nE, st=st, K=K, H=H, sumI=sumI, openH=openH, openA=openA,
                trans=trans, anchors=anchors, kind=kind)


def measure(D, theta, s, openvar='openH', thetaH_rest=None):
    logw = D['K'] * LOG2 + theta * D[openvar] + s * D['sumI']
    if thetaH_rest is not None:  # different log-odds on non-anchor horizontal edges
        logw = logw + thetaH_rest * (D['openH'] - D['openA'])
    logw -= logw.max()
    w = np.exp(logw)
    return w / w.sum()


def cond_open_max(D, nu):
    nE = D['nE']
    mx = 0.0
    idx = np.arange(2 ** nE)
    for e in D['H']:
        closed = idx[((idx >> e) & 1) == 0]
        p = nu[closed | (1 << e)] / (nu[closed | (1 << e)] + nu[closed])
        mx = max(mx, float(p.max()))
    return mx


def upset_max(m, nE, engine):
    if engine == 'nx':
        return max_upset_networkx(m, nE)[0]
    if engine == 'sp':
        return max_upset_scipy(m, nE)[0]  # true value of a genuine up-set found by int-scaled min-cut
    return max_upset_lp(m, nE)[0]


def covariance_functional(D, nu, kap, openvar='openH'):
    G = D['sumI'] + kap * D[openvar]
    return nu * (G - np.dot(nu, G))


def best_kappa(D, nu, engine, openvar='openH', lo=0.0, hi=1.5, it=22):
    nE = D['nE']
    for _ in range(it):
        mid = 0.5 * (lo + hi)
        if upset_max(covariance_functional(D, nu, mid, openvar), nE, engine) <= 1e-12:
            lo = mid
        else:
            hi = mid
    return lo


def event_family_ratios(D, nu, nv_pairs=True, nrand=300, seed=1):
    """min over increasing events f of  -d_s nu(f) / d_theta nu(f)  (= best kappa on this family)."""
    rng = np.random.default_rng(seed)
    st = D['st']; nE = D['nE']
    f_list = []
    for e in range(nE):
        f_list.append(st[:, e].astype(float))
    lab = connectivity_labels(D['nv'], D['edges'], st)
    for a in range(D['nv']):
        for b in range(a + 1, D['nv']):
            f_list.append((lab[:, a] == lab[:, b]).astype(float))
    for _ in range(nrand):
        r = rng.integers(1, 4)
        mins = [rng.random(nE) < rng.uniform(0.1, 0.6) for _ in range(r)]
        f = np.zeros(2 ** nE, bool)
        for mn in mins:
            f |= np.all(st[:, mn] == 1, axis=1)
        f_list.append(f.astype(float))
    G1 = D['sumI'] - np.dot(nu, D['sumI'])
    G2 = D['openH'] - np.dot(nu, D['openH'])
    best = np.inf
    for f in f_list:
        ds = np.dot(nu, f * G1)
        dt = np.dot(nu, f * G2)
        if dt > 1e-14:
            best = min(best, -ds / dt)
    return best, len(f_list)


def run_torus(L1, L2, P, engine, grid, label):
    t0 = time.time()
    D = setup_torus(L1, L2, P)
    k = len(P)
    kap = 3.0 ** (-(k - 1))
    print("-" * 100)
    print("%s: torus %dx%d, nE=%d, P=%s, k=%d, kappa=3^-(k-1)=%.4f  (setup %.1fs)" %
          (label, L1, L2, D['nE'], P, k, kap, time.time() - t0))
    for (theta, s) in grid:
        nu = measure(D, theta, s)
        po = cond_open_max(D, nu)
        v = upset_max(covariance_functional(D, nu, kap), D['nE'], engine)
        kb = best_kappa(D, nu, 'sp')
        fam, nf = event_family_ratios(D, nu)
        print("  theta=%+.3f s=%.2f | max cond P(open H)=%.4f (<=2/3? %s) | max_U[(12) functional]=%.2e |"
              " kappa*=%.4f (>= kappa? %s) | event-family min ratio=%.4f over %d events" %
              (theta, s, po, po <= 2 / 3 + 1e-12, v, kb, kb >= kap - 1e-9, fam, nf))
        sys.stdout.flush()
    # negative control: a false constant
    nu = measure(D, LOG2, 1.0)
    vbad = upset_max(covariance_functional(D, nu, 1.0), D['nE'], engine)
    print("  negative control (kappa=1.0 at theta=log2,s=1): max_U = %.3e  -> %s" %
          (vbad, "REFUTED (machinery has teeth)" if vbad > 1e-10 else "not refuted"))
    # integrated domination (13)
    for g in [0.2, 1.0, 3.0]:
        nu_end = measure(D, LOG2, g)
        Delta = kap * g
        phi = measure(D, LOG2 - Delta, 0.0)
        v13 = upset_max(nu_end - phi, D['nE'], engine)
        # best Delta*: largest Delta with nu_end <= phi_{log2-Delta}
        lo, hi = 0.0, 5.0
        for _ in range(22):
            mid = 0.5 * (lo + hi)
            if upset_max(nu_end - measure(D, LOG2 - mid, 0.0), D['nE'], 'sp') <= 1e-12:
                lo = mid
            else:
                hi = mid
        print("  (13) g=%.2f: Delta=kappa*g=%.4f  max_U[nu_{log2,g}-phi_{log2-Delta}](U)=%.2e  "
              "(<=0? %s) | best Delta*=%.4f (ratio Delta*/g=%.3f)" % (g, Delta, v13, v13 <= 1e-12, lo, lo / g))
        sys.stdout.flush()
    print("  total %.1fs" % (time.time() - t0))


def run_wired_box(L1, L2, P, engine):
    t0 = time.time()
    D = setup_wired_box(L1, L2, P)
    k = len(P)
    kap = 3.0 ** (-(k - 1))
    print("-" * 100)
    print("wired box %dx%d (boundary identified), nE=%d, P=%s, #anchors=%d of %d horizontal edges" %
          (L1, L2, D['nE'], P, len(D['anchors']), len(D['H'])))
    # interpolation: theta_A on anchors, log2 on other horizontal edges, 0 on vertical
    worst = -np.inf
    for thA in [LOG2, LOG2 - 0.4, -0.5]:
        for s in [0.0, 0.7, 3.0]:
            nu = measure(D, thA, s, openvar='openA', thetaH_rest=LOG2)
            po = cond_open_max(D, nu)
            G = D['sumI'] + kap * D['openA']
            m = nu * (G - np.dot(nu, G))
            v = upset_max(m, D['nE'], engine)
            worst = max(worst, v)
            print("  thetaA=%+.3f s=%.2f: max cond P(open H)=%.4f, max_U[d_s + kappa d_thetaA]=%.2e" % (thA, s, po, v))
    for g in [0.5, 2.0]:
        nu_end = measure(D, LOG2, g, openvar='openA', thetaH_rest=LOG2)
        phi = measure(D, LOG2 - kap * g, 0.0, openvar='openA', thetaH_rest=LOG2)
        v = upset_max(nu_end - phi, D['nE'], engine)
        print("  box (13) g=%.2f: max_U[nu - phi(anchors at log2-kappa g, others log2)] = %.2e" % (g, v))
    print("  total %.1fs" % (time.time() - t0))


if __name__ == "__main__":
    grid = [(LOG2, 0.0), (LOG2, 0.5), (LOG2, 3.0), (LOG2 - 0.3, 1.0), (0.0, 2.0), (-1.0, 0.3), (LOG2, 8.0)]
    run_torus(3, 2, [(0, 0)], 'nx', grid[:3], "k=1 sanity (equality expected)")
    run_torus(3, 2, [(0, 0), (1, 0)], 'nx', grid, "pair in a row")
    run_torus(3, 2, [(0, 0), (0, 1)], 'nx', grid, "stacked pair")
    # Release replay uses the review's separate sec3_run2.py for larger cases.
    # Mathematical functions above are unchanged. Preserve the full original LP
    # grid as an option instead of repeating it in every default replay.
    if "--full-lp" in sys.argv:
        run_torus(4, 2, [(0, 0), (1, 0), (2, 0)], 'lp', grid[:4], "triple in a row")
        run_torus(4, 2, [(0, 0), (1, 0), (0, 1)], 'lp', grid[:4], "L-shape triple")
        run_wired_box(5, 4, [(0, 0), (1, 0)], 'lp')
    else:
        print("Larger cases: sec3_run2.py (included in run_all.py); original extended LP grid: --full-lp")
