"""Claim 3: finite-volume tests of the tilted FK measure P_F(omega) ~ FK_crit(omega) * W(C1) W(C2)
for the counterexample CA F(X)_i = (U_{i+C_i e1}, C_i) (q = 4) of (27).

(0) W(C) for this CA = monomer-dimer partition function on horizontal NN pairs inside C, dimer activity
    z = eps^4/4  (checked against direct enumeration on random row subsets).
(1) FKG lattice condition of the full tilted measure fails (explicit pair, real FK cluster weights).
(2) Positive association: min covariance over pairs of single-edge events, connection events, and all
    pairs of up-sets on the marginal of 4 edges.  (Lattice-condition failure does NOT by itself imply
    failure of association.)
(3) Domination P_F <= FK_crit (eq. 25): checked via Holley-free route: P_F(A) <= FK(A) for all up-sets
    on 4-edge marginals and for connection events.
(4) Reviewer's reduction: P_F <=_st mu2 := FK_crit * prod_x exp(z' 1{x, x+e1 both 'closed-sites'})
    (a monotone, log-supermodular tilt) -- full Holley inequality checked over ALL pairs on a 3x3 box,
    plus the lattice condition of mu2.
"""
import itertools, random
import numpy as np
from counterexample27 import W as W_sym, e as eps_sym

P1, P2 = 2 / 3, 1 / 2  # critical anisotropic FK-Ising

# ---------- (0) W(C) for the counterexample CA ----------
def dimer_pf(row_sites, z):
    """monomer-dimer partition function on a set of integers (NN pairs)."""
    s = sorted(row_sites)
    # transfer: runs of consecutive integers -> Fibonacci-like recursion
    tot = 1.0
    run = 1
    def run_pf(n):
        a, b = 1.0, 1.0  # Z(0), Z(1)
        if n == 0:
            return 1.0
        for _ in range(n - 1):
            a, b = b, b + z * a
        return b
    if not s:
        return 1.0
    for i in range(1, len(s)):
        if s[i] == s[i - 1] + 1:
            run += 1
        else:
            tot *= run_pf(run)
            run = 1
    tot *= run_pf(run)
    return tot

def W_set(C, z):
    """C = set of 2D sites (x,y); rows independent (F's inputs lie in the same row)."""
    rows = {}
    for (x, y) in C:
        rows.setdefault(y, []).append(x)
    out = 1.0
    for y, xs in rows.items():
        out *= dimer_pf(xs, z)
    return out

def check_dimer_formula():
    rng = random.Random(1)
    worst = 0.0
    for _ in range(25):
        k = rng.randint(1, 5)
        S = tuple(sorted(rng.sample(range(1, 8), k)))
        ws = W_sym(S)
        for ev in (0.4, 0.9):
            a = float(ws.subs(eps_sym, ev))
            b = dimer_pf(S, ev ** 4 / 4)
            worst = max(worst, abs(a - b))
    return worst

# ---------- lattice / FK machinery ----------
def build_box(Lx, Ly):
    sites = [(x, y) for y in range(Ly) for x in range(Lx)]
    idx = {s: i for i, s in enumerate(sites)}
    edges = []  # (u, v, orientation, start site)
    for (x, y) in sites:
        if x + 1 < Lx:
            edges.append((idx[(x, y)], idx[(x + 1, y)], 1, (x, y)))
        if y + 1 < Ly:
            edges.append((idx[(x, y)], idx[(x, y + 1)], 2, (x, y)))
    return sites, edges

def n_clusters(nv, edges, omega):
    par = list(range(nv))
    def find(a):
        while par[a] != a:
            par[a] = par[par[a]]
            a = par[a]
        return a
    k = nv
    for (u, v, _, _), o in zip(edges, omega):
        if o:
            ru, rv = find(u), find(v)
            if ru != rv:
                par[ru] = rv
                k -= 1
    return k, find

def all_weights(sites, edges, eps, extra=None):
    """returns arrays over all omega (bit i = edge i open): FK weight, tilt W(C1)W(C2), and conn info."""
    nE = len(edges)
    nv = len(sites)
    z = eps ** 4 / 4
    N = 1 << nE
    fk = np.empty(N)
    tilt = np.empty(N)
    roots = np.empty((N, nv), dtype=np.int16)
    for m in range(N):
        omega = [(m >> i) & 1 for i in range(nE)]
        k, find = n_clusters(nv, edges, omega)
        w = 1.0
        C1, C2 = set(), set()
        for (u, v, r, st), o in zip(edges, omega):
            p = P1 if r == 1 else P2
            w *= p if o else (1 - p)
            if not o:
                (C1 if r == 1 else C2).add(st)
        fk[m] = w * 2.0 ** k
        tilt[m] = W_set(C1, z) * W_set(C2, z)
        roots[m] = [find(i) for i in range(nv)]
    return fk, tilt, roots

def upsets(n):
    """all up-sets of {0,1}^n as boolean masks over 2^n points."""
    pts = list(range(1 << n))
    res = []
    for bits in range(1 << (1 << n)):
        ok = True
        for a in pts:
            if (bits >> a) & 1:
                for i in range(n):
                    b = a | (1 << i)
                    if not (bits >> b) & 1:
                        ok = False
                        break
            if not ok:
                break
        if ok:
            res.append(np.array([(bits >> a) & 1 for a in pts], dtype=bool))
    return res

def main():
    print('(0) max |W_direct - dimer formula| on random row subsets:', check_dimer_formula())

    # ---- (1) lattice condition failure, 4x3 box, explicit configurations ----
    sites, edges = build_box(4, 3)
    nE = len(edges)
    eps = 0.9
    fk, tilt, roots = all_weights(sites, edges, eps)
    mu = fk * tilt
    mu /= mu.sum()
    fk_n = fk / fk.sum()
    # horizontal edges starting at (0,1),(1,1),(2,1)
    hid = {e[3]: i for i, e in enumerate(edges) if e[2] == 1}
    full = (1 << nE) - 1
    a, b, c = hid[(0, 1)], hid[(1, 1)], hid[(2, 1)]
    om1 = full & ~(1 << a) & ~(1 << b)       # closed {a,b}
    om2 = full & ~(1 << b) & ~(1 << c)       # closed {b,c}
    join, meet = om1 | om2, om1 & om2
    lhs = mu[join] * mu[meet]
    rhs = mu[om1] * mu[om2]
    print(f'(1) 4x3 box, eps={eps}: mu(w1 v w2) mu(w1 ^ w2) / [mu(w1) mu(w2)] = {lhs / rhs:.12f}  (<1 => FKG lattice condition fails)')
    fkr = fk[join] * fk[meet] / (fk[om1] * fk[om2])
    print('    FK part of that ratio (cluster counts unchanged):', fkr)

    # ---- (2)+(3) association and domination tests ----
    for eps in (0.5, 0.9, 0.999):
        fk, tilt, roots = all_weights(sites, edges, eps)
        mu = fk * tilt; mu /= mu.sum()
        fkn = fk / fk.sum()
        X = np.array([[(m >> i) & 1 for i in range(nE)] for m in range(1 << nE)], dtype=float)
        Em = mu @ X
        cov = (X * mu[:, None]).T @ X - np.outer(Em, Em)
        np.fill_diagonal(cov, np.inf)
        # connection events between pairs of sites
        nv = len(sites)
        conn = []
        for i in range(nv):
            for j in range(i + 1, nv):
                conn.append(roots[:, i] == roots[:, j])
        conn = np.array(conn, dtype=float)
        Pc = conn @ mu
        covc = (conn * mu) @ conn.T - np.outer(Pc, Pc)
        np.fill_diagonal(covc, np.inf)
        dom_conn = (Pc - conn @ fkn).max()
        dom_edge = (Em - fkn @ X).max()
        print(f'(2) eps={eps}: min Cov(edge_e, edge_f) = {cov.min():.3e};  min Cov(conn, conn) = {covc.min():.3e}')
        print(f'(3) eps={eps}: max [P_F - P_FK] over single-edge events = {dom_edge:.3e}, over connection events = {dom_conn:.3e}  (<=0 expected)')
        # all up-set pairs on the marginal of the 3 horizontal edges in row 1 plus one vertical edge
        sub = [a, b, c, [i for i, e in enumerate(edges) if e[2] == 2 and e[3] == (1, 0)][0]]
        marg = np.zeros(16); margfk = np.zeros(16)
        for m in range(1 << nE):
            key = sum(((m >> s) & 1) << t for t, s in enumerate(sub))
            marg[key] += mu[m]; margfk[key] += fkn[m]
        U = upsets(4)
        Um = np.array(U, dtype=float)
        PU = Um @ marg
        joint = (Um * marg) @ Um.T
        assoc = (joint - np.outer(PU, PU)).min()
        domU = (PU - Um @ margfk).max()
        print(f'    4-edge marginal: {len(U)} up-sets; min Cov over all up-set pairs = {assoc:.3e}; max P_F(A)-P_FK(A) = {domU:.3e}')

    # ---- (2b) path of 3 horizontal edges (tree): explicit covariance of the two outer edges ----
    print('(2b) path of three horizontal edges (FK on a tree = product with p_hat = p/(p+2(1-p))):')
    for eps in (0.5, 0.9, 0.999):
        z = eps ** 4 / 4
        ph = P1 / (P1 + 2 * (1 - P1))
        tot = 0; E1 = 0; E3 = 0; E13 = 0
        for o in itertools.product((0, 1), repeat=3):
            C = {i for i in range(3) if not o[i]}
            w = np.prod([ph if oi else 1 - ph for oi in o]) * dimer_pf(C, z)
            tot += w; E1 += w * o[0]; E3 += w * o[2]; E13 += w * o[0] * o[2]
        print(f'    eps={eps}: Cov(w1,w3) = {E13 / tot - E1 * E3 / tot ** 2:.3e}')

    # ---- (4) reviewer's reduction: Holley domination by a monotone tilt, 3x3 box, all pairs ----
    sites3, edges3 = build_box(3, 3)
    nE3 = len(edges3)
    for eps in (0.9, 0.999):
        z = eps ** 4 / 4
        fk3, tilt3, _ = all_weights(sites3, edges3, eps)
        PF = fk3 * tilt3; PF /= PF.sum()
        # sharp local constant a = min over C, e with n_e(C)>=1 of (R_F - 1)/n_e
        N3 = 1 << nE3
        closed_sets = []
        for m in range(N3):
            C1 = frozenset(ed[3] for i, ed in enumerate(edges3) if not (m >> i) & 1 and ed[2] == 1)
            C2 = frozenset(ed[3] for i, ed in enumerate(edges3) if not (m >> i) & 1 and ed[2] == 2)
            closed_sets.append((C1, C2))
        def npat(Cr, s):  # number of horizontal pairs {x, x+e1} containing s with the other in Cr
            x, y = s
            return int((x - 1, y) in Cr) + int((x + 1, y) in Cr)
        amin = np.inf
        for m in range(N3):
            for i, ed in enumerate(edges3):
                if (m >> i) & 1:
                    continue  # look at configurations with e closed: C includes e
                Cr = closed_sets[m][0 if ed[2] == 1 else 1]
                s = ed[3]
                n = npat(Cr, s)
                if n >= 1:
                    R = W_set(Cr, z) / W_set(Cr - {s}, z)
                    amin = min(amin, (R - 1) / n)
        zp = np.log1p(amin) / 2  # |P0| = 2
        # mu2 = FK * prod over horizontal pairs inside C_r of exp(z')
        def npairs(Cr):
            return sum(1 for (x, y) in Cr if (x + 1, y) in Cr)
        mu2 = fk3 * np.array([np.exp(zp * (npairs(C1) + npairs(C2))) for (C1, C2) in closed_sets])
        mu2 /= mu2.sum()
        # Holley: mu2(w v w') PF(w ^ w') >= PF(w) mu2(w')  for all pairs; lattice: mu2(v)mu2(^) >= mu2 mu2
        ms = np.arange(N3)
        worst_h = np.inf; worst_l = np.inf
        for w in range(N3):
            jn = ms | w; mt = ms & w
            h = mu2[jn] * PF[mt] - PF[w] * mu2[ms]
            l = mu2[jn] * mu2[mt] - mu2[w] * mu2[ms]
            worst_h = min(worst_h, (h / (PF[w] * mu2[ms])).min())
            worst_l = min(worst_l, (l / (mu2[w] * mu2[ms])).min())
        print(f"(4) 3x3 box eps={eps}: a_min={amin:.4e}, z'={zp:.4e}; min relative Holley slack (>=0 => PF <=st mu2) = {worst_h:.3e}; "
              f"min relative lattice slack of mu2 (>=0 => monotone) = {worst_l:.3e}")

if __name__ == '__main__':
    main()
