"""Section 2 checks: positivity/factorisation of collision activities, witness-completion inequality (5),
the bound W(C) <= w_max^{|D(P)|} W(C \\ D(P)), monotonicity of W/V (7), FKG lattice property of nu_g (8),
and exact stochastic domination mu_F <= nu_g (9) on a small box (two engines: networkx min-cut, HiGHS LP)."""
import sys, itertools, time
import numpy as np
from common import (CA, Collision, D_of, all_states, components_count, box_graph,
                    max_upset_networkx, max_upset_lp, is_upset)

np.set_printoptions(linewidth=160)


def maj3(X):
    return (X.sum(axis=1) >= 2).astype(np.int64)


def selector(X):
    # symbol s = U + 2*C ; F(U,C)_i = (U_{i+C_i}, C_i)
    Ua, Ca = X[:, 0] % 2, X[:, 0] // 2
    Ub = X[:, 1] % 2
    U = np.where(Ca == 0, Ua, Ub)
    return U + 2 * Ca


def xor2(X):
    return (X[:, 0] + X[:, 1]) % 2


def eca(rule):
    tab = np.array([(rule >> k) & 1 for k in range(8)], dtype=np.int64)
    def f(X):
        return tab[4 * X[:, 0] + 2 * X[:, 1] + X[:, 2]]
    return f


CAS = [
    CA(2, [(0, 0), (1, 0), (0, 1)], maj3, "2D majority on {0,e1,e2} (q=2)"),
    CA(4, [(0, 0), (1, 0)], selector, "selector CA (23), rowwise (q=4)"),
    CA(2, [(0, 0), (1, 0), (2, 0)], eca(232), "ECA 232 rowwise (q=2)"),
    CA(2, [(0, 0), (1, 0), (2, 0)], eca(23), "ECA 23 rowwise (q=2)"),
    CA(2, [(0, 0), (1, 0)], xor2, "XOR (surjective control, q=2)"),
]


def popcount(m):
    return bin(m).count("1")


def find_witness(col, tol=1e-13):
    best = None
    for T in range(1, 2 ** col.n):
        if col.c[T] > tol:
            if best is None or popcount(T) < popcount(best):
                best = T
    return best


def translates_in(P, R):
    """All translates P+x contained in region R (as frozensets)."""
    Rs = set(R)
    out = set()
    p0 = P[0]
    for r in R:
        x = (r[0] - p0[0], r[1] - p0[1])
        T = frozenset((p[0] + x[0], p[1] + x[1]) for p in P)
        if T <= Rs:
            out.add(T)
    return [sorted(T) for T in out]


def region_checks(ca, R, eps):
    col = Collision(ca, R)
    n = col.n
    W = col.W_all(eps)
    W2 = col.W_direct(eps)
    q = ca.q
    wmax = 1 + eps ** 2 * (q - 1)
    res = {}
    res['W engines maxdiff'] = float(np.max(np.abs(W - W2)))
    res['min c_T'] = float(col.c.min())
    res['min W'] = float(W.min())
    # factorisation
    fact_err, fact_n = 0.0, 0
    Nset = ca.N
    def inp(S):
        return set((s[0] + nn[0], s[1] + nn[1]) for s in S for nn in Nset)
    masks_sites = [[col.R[k] for k in range(n) if (m >> k) & 1] for m in range(2 ** n)]
    inps = [inp(s) for s in masks_sites]
    for A in range(1, 2 ** n):
        for B in range(1, 2 ** n):
            if A & B or A > B:
                continue
            if inps[A] & inps[B]:
                continue
            fact_err = max(fact_err, abs(col.c[A | B] - col.c[A] * col.c[B])); fact_n += 1
    res['factorisation pairs'] = fact_n
    res['factorisation maxerr'] = fact_err
    # monotone W
    mono = min(W[C | (1 << i)] - W[C] for C in range(2 ** n) for i in range(n) if not (C >> i) & 1)
    res['min W(C+i)-W(C)'] = float(mono)
    Pm = find_witness(col)
    if Pm is None:
        res['witness'] = None
        res['max |c_T|, T nonempty'] = float(np.max(np.abs(col.c[1:])))
        return res, col
    P = masks_sites[Pm]
    k = len(P)
    cP = col.c[Pm]
    D = D_of(P, ca.N)
    aP = eps ** (2 * k) * cP / wmax ** len(D)
    g = np.log1p(aP) / k
    res['witness P'] = P
    res['k'] = k
    res['c_P'] = float(cP)
    res['|D(P)|'] = len(D)
    res['a_P'] = float(aP)
    trans = translates_in(P, col.R)
    res['#translates in R'] = len(trans)
    # (5) witness completion, and the D-bound
    min_ratio_wc = np.inf
    worst_Dbound = -np.inf
    for T in trans:
        Tm = col.mask(T)
        DT = D_of(T, ca.N)
        Dm = col.mask([d for d in DT if d in col.pos])
        for C in range(2 ** n):
            # D-bound: W(C) <= wmax^{|D cap C|} W(C \ D)
            lhs = W[C]; rhs = wmax ** popcount(C & Dm) * W[C & ~Dm]
            worst_Dbound = max(worst_Dbound, lhs - rhs)
            for i in range(n):
                if not (Tm >> i) & 1:
                    continue
                if (C >> i) & 1:
                    continue
                if (Tm & ~(1 << i)) & ~C:
                    continue
                r = W[C | (1 << i)] / W[C]
                min_ratio_wc = min(min_ratio_wc, r)
    res['min ratio under witness completion'] = float(min_ratio_wc)
    res['1+a_P'] = float(1 + aP)
    res['(5) slack'] = float(min_ratio_wc - (1 + aP))
    res['max [W(C) - wmax^|DnC| W(C\\D)]'] = float(worst_Dbound)
    # (7) W/V monotone
    tmasks = [col.mask(T) for T in trans]
    cnt = np.array([sum(1 for tm in tmasks if (C & tm) == tm) for C in range(2 ** n)])
    V = np.exp(g * cnt)
    ratio = W / V
    worst7 = min(ratio[C | (1 << i)] / ratio[C] - 1 for C in range(2 ** n) for i in range(n) if not (C >> i) & 1)
    res['(7) min [ (W/V)(C+i)/(W/V)(C) - 1 ]'] = float(worst7)
    return res, col


def fk_box_checks(ca, eps, L1=3, L2=3, pH=2 / 3, pV=1 / 2, engines=True):
    nv, edges, kind, start = box_graph(L1, L2)
    nE = len(edges)
    Hidx = [e for e in range(nE) if kind[e] == 'H']
    Vidx = [e for e in range(nE) if kind[e] == 'V']
    RH = [start[e] for e in Hidx]
    RV = [start[e] for e in Vidx]
    colH = Collision(ca, RH)
    colV = Collision(ca, RV)
    WH = colH.W_all(eps); WV = colV.W_all(eps)
    st = all_states(nE)
    K = components_count(nv, edges, st)
    # closed-set masks (in each region's bit order)
    closedH = np.zeros(2 ** nE, dtype=np.int64)
    for b, e in enumerate(Hidx):
        closedH |= ((1 - st[:, e]).astype(np.int64) << b)
    closedV = np.zeros(2 ** nE, dtype=np.int64)
    for b, e in enumerate(Vidx):
        closedV |= ((1 - st[:, e]).astype(np.int64) << b)
    oH = st[:, Hidx].sum(1); oV = st[:, Vidx].sum(1)
    base = (2.0 ** K) * (pH / (1 - pH)) ** oH * (pV / (1 - pV)) ** oV
    muF = base * WH[closedH] * WV[closedV]
    muF /= muF.sum()
    phi = base / base.sum()
    # witness from a big region
    big = Collision(ca, [(x, y) for y in range(2) for x in range(3)] if ca.m == 3 and ca.N[2] == (0, 1)
                    else [(x, 0) for x in range(5)])
    Pm = find_witness(big)
    out = {'nE': nE}
    if Pm is None:
        out['witness'] = None
        out['max |muF - phi|'] = float(np.max(np.abs(muF - phi)))
        return out
    P = [big.R[k] for k in range(big.n) if (Pm >> k) & 1]
    k = len(P); cP = big.c[Pm]
    q = ca.q; wmax = 1 + eps ** 2 * (q - 1)
    aP = eps ** (2 * k) * cP / wmax ** len(D_of(P, ca.N))
    g = np.log1p(aP) / k
    trans = translates_in(P, RH)
    tmasks = [colH.mask(T) for T in trans]
    cnt = np.zeros(2 ** nE)
    for tm in tmasks:
        cnt += ((closedH & tm) == tm)
    nu = base * np.exp(g * cnt)
    nu /= nu.sum()
    out.update({'witness P': P, 'k': k, 'g': float(g), '#translates in box': len(trans)})
    # FKG lattice condition for nu: nu(a|b) nu(a&b) >= nu(a) nu(b)
    S = 2 ** nE
    idx = np.arange(S)
    worst = np.inf
    for a in range(S):
        b = idx
        lhs = nu[a | b] * nu[a & b]
        rhs = nu[a] * nu[b]
        worst = min(worst, float(np.min((lhs - rhs) / np.maximum(rhs, 1e-300))))
    out['nu_g lattice condition min rel slack'] = worst
    # Holley: muF(a & b) nu(a | b) >= muF(a) nu(b)
    worstH = np.inf
    for a in range(S):
        b = idx
        lhs = muF[a & b] * nu[a | b]
        rhs = muF[a] * nu[b]
        worstH = min(worstH, float(np.min((lhs - rhs) / np.maximum(rhs, 1e-300))))
    out['Holley(muF<=nu_g) min rel slack'] = worstH
    if engines:
        # exact domination via max-closure: max_U (muF - nu)(U) over up-sets of OPEN edges
        t = time.time()
        v1, U1 = max_upset_networkx(muF - nu, nE)
        v2, x2 = max_upset_lp(muF - nu, nE)
        out['max_U [muF-nu_g](U) (networkx, LP)'] = (float(v1), float(v2))
        v3, _ = max_upset_networkx(muF - phi, nE)
        out['max_U [muF-phi_crit](U) (networkx)'] = float(v3)
        v4, _ = max_upset_networkx(nu - muF, nE)
        out['max_U [nu_g-muF](U) (should be >0: strict)'] = float(v4)
        out['engine time s'] = round(time.time() - t, 1)
    return out


if __name__ == "__main__":
    for ca in CAS:
        print("=" * 100)
        print(ca.name)
        if ca.N == [(0, 0), (1, 0), (0, 1)]:
            R = [(x, y) for y in range(3) for x in range(3)]
        elif ca.q == 4:
            R = [(x, 0) for x in range(7)]
        else:
            R = [(x, 0) for x in range(9)]
        for eps in [0.5, 0.9]:
            res, col = region_checks(ca, R, eps)
            print(" eps=%.2f region |R|=%d" % (eps, len(R)))
            for kk, vv in res.items():
                print("   %-45s %s" % (kk, vv))
        for eps in [0.9]:
            t = time.time()
            out = fk_box_checks(ca, eps)
            print(" FK box 3x3 (12 edges), eps=%.2f" % eps)
            for kk, vv in out.items():
                print("   %-45s %s" % (kk, vv))
            print("   time %.1fs" % (time.time() - t))
        sys.stdout.flush()
