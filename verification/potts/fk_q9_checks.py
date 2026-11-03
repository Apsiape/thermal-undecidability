"""Exact finite-volume checks of the q = 9 random-cluster chain in the Potts-SSB claim.

(1) FK identity: sum_sigma prod_e (w_e + 3 1{same}) = sum_omega 9^k 3^|omega| prod_closed w_e
    (direct 9^V spin sum vs 2^E bond sum), for random positive w.
(2) Colour-1 boundary identity: (9 mu(sigma_0=1) - 1)/8 = phi^1(0 <-> boundary) in finite volume.
(3) Anchor covariance inequality at q = 9:
      Cov(f, I_t) <= -4^{-(k-1)} Cov(f, omega_{e_t})   (theta_e <= log 3, s >= 0),
    and nu(I_t | omega_{e_t}=0) >= 4^{-(k-1)}.
(4) Interpolation endpoint: nu_g <= FK(odds 3 e^{-kappa g} on anchors), kappa = 4^{-(k-1)},
    checked on random increasing events and connection events, free and wired.
(5) Target domination at q = 9 with a real CA collision layer (AND rule, lam large):
      mu(omega) ~ 9^k 3^|omega| W(C_H) W(C_V)  <=  nu_g  <=  nu_0.
(6) Stress: replacing kappa by 1 (no 4^{-(k-1)} factor) should be able to FAIL (4), showing
    the factor is load-bearing; we report whether a violation is found.
"""
import itertools, math, random
import numpy as np

random.seed(9)
np.random.seed(9)
Q = 9
Y = 3.0  # critical odds sqrt(9)


def grid(nx, ny):
    V = [(x, y) for y in range(ny) for x in range(nx)]
    vid = {v: i for i, v in enumerate(V)}
    E = []
    for (x, y) in V:
        if x + 1 < nx:
            E.append(((x, y), (x + 1, y), 'H'))
        if y + 1 < ny:
            E.append(((x, y), (x, y + 1), 'V'))
    return V, vid, E


def clusters(nV, edges_idx, mask, wired_set=None):
    par = list(range(nV + 1))  # nV = ghost boundary vertex

    def f(a):
        while par[a] != a:
            par[a] = par[par[a]]
            a = par[a]
        return a
    if wired_set is not None:
        for v in wired_set:
            par[f(v)] = f(nV)
    for j, (a, b) in enumerate(edges_idx):
        if mask >> j & 1:
            ra, rb = f(a), f(b)
            if ra != rb:
                par[ra] = rb
    roots = set(f(v) for v in range(nV))
    if wired_set is not None:
        k = len([r for r in roots if r != f(nV)])  # boundary cluster gets weight 1
    else:
        k = len(roots)
    return k, f


def check_fk_identity():
    V, vid, E = grid(3, 2)
    ei = [(vid[a], vid[b]) for a, b, _ in E]
    nE, nV = len(E), len(V)
    worst = 0.0
    for trial in range(3):
        w = np.random.uniform(0.6, 1.6, size=nE)
        # direct spin sum
        spins = np.array(list(itertools.product(range(Q), repeat=nV)), dtype=np.int8)
        val = np.ones(len(spins))
        for j, (a, b) in enumerate(ei):
            val *= w[j] + Y * (spins[:, a] == spins[:, b])
        direct = val.sum()
        fk = 0.0
        for m in range(1 << nE):
            k, _ = clusters(nV, ei, m)
            closed = [j for j in range(nE) if not (m >> j & 1)]
            fk += Q ** k * Y ** bin(m).count('1') * np.prod(w[closed])
        worst = max(worst, abs(direct - fk) / fk)
    return worst


def check_colour1():
    # interior 2x3 block, boundary spins fixed to colour 1 on the outer ring; edges interior-interior and interior-boundary
    nx, ny = 3, 2
    V = [(x, y) for y in range(ny) for x in range(nx)]
    vid = {v: i for i, v in enumerate(V)}
    E = []
    B = []  # boundary edges: (interior vertex)
    for (x, y) in V:
        for dx, dy in [(1, 0), (0, 1), (-1, 0), (0, -1)]:
            u = (x + dx, y + dy)
            if u in vid:
                if (dx, dy) in [(1, 0), (0, 1)]:
                    E.append((vid[(x, y)], vid[u]))
            else:
                B.append(vid[(x, y)])
    nV = len(V)
    spins = np.array(list(itertools.product(range(Q), repeat=nV)), dtype=np.int8)
    val = np.ones(len(spins))
    for (a, b) in E:
        val *= 1 + Y * (spins[:, a] == spins[:, b])
    for a in B:
        val *= 1 + Y * (spins[:, a] == 0)
    Z = val.sum()
    x0 = vid[(1, 0)]
    p1 = val[spins[:, x0] == 0].sum() / Z
    M = (Q * p1 - 1) / (Q - 1)
    # FK side: all edges incl. boundary edges to a ghost
    allE = E + [(a, nV) for a in B]
    nE = len(allE)
    num = den = 0.0
    for m in range(1 << nE):
        # ghost vertex nV is wired boundary; count clusters not containing ghost
        par = list(range(nV + 1))

        def f(a):
            while par[a] != a:
                par[a] = par[par[a]]
                a = par[a]
            return a
        for j, (a, b) in enumerate(allE):
            if m >> j & 1:
                ra, rb = f(a), f(b)
                if ra != rb:
                    par[ra] = rb
        roots = set(f(v) for v in range(nV))
        k = len([r for r in roots if r != f(nV)])
        wt = Q ** k * Y ** bin(m).count('1')
        den += wt
        if f(x0) == f(nV):
            num += wt
    return M, num / den


class FKSystem:
    def __init__(self, nx, ny, wired):
        self.V, self.vid, self.E = grid(nx, ny)
        self.nV, self.nE = len(self.V), len(self.E)
        self.ei = [(self.vid[a], self.vid[b]) for a, b, _ in self.E]
        self.orient = [o for _, _, o in self.E]
        bset = [self.vid[(x, y)] for (x, y) in self.V if x in (0, nx - 1) or y in (0, ny - 1)] if wired else None
        self.wired = wired
        n = 1 << self.nE
        self.masks = np.arange(n)
        self.open = np.array([[(m >> j) & 1 for j in range(self.nE)] for m in range(n)], dtype=np.int8)
        self.k = np.zeros(n)
        self.conn = {}
        reps = []
        for m in range(n):
            k, f = clusters(self.nV, self.ei, m, bset)
            self.k[m] = k
            reps.append([f(v) for v in range(self.nV)] + [f(self.nV)])
        self.reps = np.array(reps)

    def connect(self, a, b):
        return (self.reps[:, a] == self.reps[:, b]).astype(float)

    def measure(self, logodds, rewards=None, s=0.0):
        logw = self.k * math.log(Q) + self.open @ np.asarray(logodds)
        if rewards is not None:
            logw = logw + s * rewards.sum(axis=1)
        logw -= logw.max()
        w = np.exp(logw)
        return w / w.sum()

    def translates(self, Pshape):
        """horizontal translates of a pattern of horizontal edges given as offsets of left endpoints."""
        Hidx = {(a, b): j for j, (a, b, o) in enumerate(self.E) if o == 'H'}
        Hleft = {a: j for (a, b), j in Hidx.items()}
        out = []
        for (x, y) in self.V:
            js = []
            for (dx, dy) in Pshape:
                p = (x + dx, y + dy)
                if p in Hleft:
                    js.append(Hleft[p])
                else:
                    js = None
                    break
            if js is not None:
                out.append(js)
        return out

    def closed_indicators(self, trans):
        cl = 1 - self.open
        return np.stack([cl[:, js].prod(axis=1) for js in trans], axis=1).astype(float)


def random_up_event(sys, nmin=3, size=(2, 5)):
    sets = [random.sample(range(sys.nE), random.randint(*size)) for _ in range(nmin)]
    f = np.zeros(len(sys.masks))
    for S in sets:
        f = np.maximum(f, sys.open[:, S].prod(axis=1))
    return f


def check_covariance_and_domination(nx, ny, wired, Pshape, g, kappa, nf=200):
    sys = FKSystem(nx, ny, wired)
    trans = sys.translates(Pshape)
    if not trans:
        return dict(trans=[])
    I = sys.closed_indicators(trans)
    k = len(Pshape)
    a_bound = 4.0 ** (-(k - 1))
    anchors = [js[0] for js in trans]
    assert len(set(anchors)) == len(anchors)
    th_c = math.log(Y)
    fs = [random_up_event(sys) for _ in range(nf)]
    fs += [sys.connect(0, sys.nV - 1), sys.connect(0, sys.nV)]  # x<->y, x<->wired ghost
    worst_cov = -1e9
    worst_cond = 1e9
    # covariance inequality along the path
    for sstep in np.linspace(0, g, 5):
        lo = np.full(sys.nE, th_c)
        for e in anchors:
            lo[e] = th_c - kappa * g + kappa * sstep
        nu = sys.measure(lo, I, sstep)
        for t, js in enumerate(trans):
            e = js[0]
            ce = 1 - sys.open[:, e]
            pce = (nu * ce).sum()
            worst_cond = min(worst_cond, (nu * I[:, t]).sum() / pce)
            for f in fs:
                Ef = (nu * f).sum()
                covI = (nu * f * I[:, t]).sum() - Ef * (nu * I[:, t]).sum()
                cove = (nu * f * sys.open[:, e]).sum() - Ef * (nu * sys.open[:, e]).sum()
                worst_cov = max(worst_cov, covI + a_bound * cove)
    # endpoint domination
    lo_g = np.full(sys.nE, th_c)
    nu_g = sys.measure(lo_g, I, g)
    lo_0 = np.full(sys.nE, th_c)
    for e in anchors:
        lo_0[e] = th_c - kappa * g
    nu_0 = sys.measure(lo_0)
    worst_dom = max(((nu_g * f).sum() - (nu_0 * f).sum()) for f in fs)
    return dict(cov_violation=worst_cov, min_cond=worst_cond, a=a_bound, dom_violation=worst_dom, sys=sys,
                trans=trans, I=I, anchors=anchors, fs=fs)


def check_target(nx, ny, wired, rule_name, lam=0.5):
    """Target with real CA collision weights in BOTH orientation layers, vs comparator with witness
    rewards on BOTH orientations, vs ordinary FK with odds 3 e^{-kappa g} on all anchors."""
    from fractions import Fraction as Fr
    import collision_checks as cc
    if rule_name == 'AND2':
        ca = cc.make_ca(2, [(0, 0), (1, 0)], lambda v: v[0] & v[1])
    else:
        ca = cc.make_ca(2, [(0, 0), (1, 0), (0, 1)], lambda v: 1 if sum(v) >= 2 else 0)
    sys = FKSystem(nx, ny, wired)
    lamF = Fr(lam).limit_denominator(1000)
    centers = [a for a, b, o in sys.E]
    cache = {}

    def W(C):
        key = tuple(sorted(C))
        if key not in cache:
            cache[key] = float(cc.W_brute(ca, list(key), lamF))
        return cache[key]
    layer = {o: [j for j in range(sys.nE) if sys.orient[j] == o] for o in 'HV'}
    logw = np.zeros(len(sys.masks))
    for m in range(len(sys.masks)):
        for o in 'HV':
            C = [centers[j] for j in layer[o] if not (m >> j & 1)]
            logw[m] += math.log(W(C))
    logw += sys.k * math.log(Q) + sys.open.sum(axis=1) * math.log(Y)
    logw -= logw.max()
    mu = np.exp(logw); mu /= mu.sum()
    # smallest witness among |T| <= 2
    P = None
    for r in (1, 2):
        for T in itertools.combinations([(0, 0), (1, 0), (0, 1)], r):
            if cc.c_T(ca, T) > 0:
                P = list(T); break
        if P: break
    cP = float(cc.c_T(ca, P))
    k = len(P)
    wmax = 1 + lam * (ca['qa'] - 1)
    aP = lam ** k * cP / wmax ** len(cc.D_of(P, ca['N']))
    g = math.log(1 + aP) / k
    kappa = 4.0 ** (-(k - 1))
    # translates in each layer: sets of edges of orientation o whose centers are P + t
    cidx = {o: {centers[j]: j for j in layer[o]} for o in 'HV'}
    trans = []
    for o in 'HV':
        for t in sys.V:
            js = [cidx[o].get((p[0] + t[0], p[1] + t[1])) for p in P]
            if all(j is not None for j in js):
                trans.append(js)
    I = sys.closed_indicators(trans)
    anchors = [js[0] for js in trans]
    assert len(set(anchors)) == len(anchors)
    nu_g = sys.measure(np.full(sys.nE, math.log(Y)), I, g)
    lo0 = np.full(sys.nE, math.log(Y))
    for e in anchors:
        lo0[e] -= kappa * g
    nu_0 = sys.measure(lo0)
    fs = [random_up_event(sys) for _ in range(300)] + [sys.connect(0, sys.nV - 1), sys.connect(0, sys.nV)]
    v1 = max(((mu * f).sum() - (nu_g * f).sum()) for f in fs)
    v2 = max(((nu_g * f).sum() - (nu_0 * f).sum()) for f in fs)
    return v1, v2, g, P, len(trans)


def main():
    class _O(list):
        def append(self, x):
            print(x, flush=True); super().append(x)
    out = _O()
    rel = check_fk_identity()
    out.append(f'(1) FK identity q=9 on 3x2 grid, max relative error {rel:.2e}')
    M, phi = check_colour1()
    out.append(f'(2) colour-1 boundary: (9mu(s0=1)-1)/8 = {M:.12f}, phi^1(0<->bdry) = {phi:.12f}, diff {abs(M-phi):.2e}')
    for (nx, ny) in [(3, 3), (4, 3)]:
        for wired in (False, True):
            for Pshape in [[(0, 0), (1, 0)], [(0, 0), (0, 1)], [(0, 0), (1, 0), (0, 1)]]:
                for g in (0.3, 2.0):
                    k = len(Pshape)
                    try:
                        r = check_covariance_and_domination(nx, ny, wired, Pshape, g, 4.0 ** (-(k - 1)), nf=120)
                    except AssertionError:
                        continue
                    if not r['trans']:
                        continue
                    out.append(f'(3,4) {nx}x{ny} {"wired" if wired else "free "} P={Pshape} g={g}: '
                               f'max[Cov(f,I)+a Cov(f,w_e)]={r["cov_violation"]:.2e} (<=0 required), '
                               f'min nu(I|e closed)={r["min_cond"]:.4f} >= a={r["a"]:.4f}: {r["min_cond"] >= r["a"] - 1e-12}, '
                               f'max[nu_g(f)-nu_0(f)]={r["dom_violation"]:.2e}')
    # stress: kappa = 1 instead of 4^{-(k-1)}
    viol = []
    for (nx, ny) in [(3, 3), (4, 3)]:
        for wired in (False, True):
            for Pshape in [[(0, 0), (1, 0)], [(0, 0), (1, 0), (2, 0)]]:
                r = check_covariance_and_domination(nx, ny, wired, Pshape, 3.0, 1.0, nf=200)
                if r['trans']:
                    viol.append(r['dom_violation'])
    out.append(f'(6) stress kappa=1 (factor dropped): max[nu_g(f)-nu_0(f)] over cases = {max(viol):.3e} '
               f'({"VIOLATION found: the 4^-(k-1) factor is load-bearing" if max(viol) > 1e-12 else "no violation found"})')
    for rule in ('AND2', 'MAJ3'):
        for (nx, ny) in [(3, 3), (4, 2)]:
            for wired in (False, True):
                v1, v2, g, P, nt = check_target(nx, ny, wired, rule)
                out.append(f'(5) target {rule} lam=1/2 {nx}x{ny} {"wired" if wired else "free "}: witness P={P} '
                           f'translates(H+V)={nt} g={g:.3e} max[mu(f)-nu_g(f)]={v1:.2e}, '
                           f'max[nu_g(f)-nu_0(f)]={v2:.2e} (both <=0 required)')


if __name__ == '__main__':
    main()
