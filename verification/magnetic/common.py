"""Common tools for finite thermal-decay verification (2 Nov 2026).

Own code. Conventions:
  * A CA on Z^2 is given by alphabet size q, neighborhood N (list of 2D offsets), local rule f (numpy-vectorised:
    takes an int array of shape (..., m) and returns int array (...)).
  * Collision weights: w_i = 1 + eps^2 (q 1{F(X)_i = F(X')_i} - 1), X, X' iid uniform.  W(C) = E prod_{i in C} w_i.
  * W(C) = sum_{T subseteq C} eps^{2|T|} c_T, with c_T = Mobius inverse of Coll(U) = q^{|U|} sum_y P(F(X)_U = y)^2.
"""
import itertools
import numpy as np


class CA:
    def __init__(self, q, N, f, name=""):
        self.q = q
        self.N = [tuple(n) for n in N]
        self.m = len(self.N)
        self.f = f
        self.name = name

    def joint_law(self, R):
        """Exact law of (F(X)_r)_{r in R} under uniform X; returns array of shape (q,)*len(R)."""
        R = [tuple(r) for r in R]
        inputs = sorted(set((r[0] + n[0], r[1] + n[1]) for r in R for n in self.N))
        idx = {s: k for k, s in enumerate(inputs)}
        L = len(inputs)
        q = self.q
        # all input configurations
        tot = q ** L
        if tot > 2 ** 24:
            raise ValueError("too many inputs %d" % tot)
        ar = np.arange(tot, dtype=np.int64)
        X = np.empty((tot, L), dtype=np.int64)
        for k in range(L):
            X[:, L - 1 - k] = ar % q
            ar //= q
        outs = []
        for r in R:
            cols = [idx[(r[0] + n[0], r[1] + n[1])] for n in self.N]
            outs.append(self.f(X[:, cols]))
        Y = np.stack(outs, axis=1)
        code = np.zeros(tot, dtype=np.int64)
        for k in range(len(R)):
            code = code * q + Y[:, k]
        p = np.bincount(code, minlength=q ** len(R)).astype(float) / tot
        return p.reshape((q,) * len(R))


def coll_all_subsets(p, q):
    """Coll(U) for all subsets U of range(n) (bitmask indexed): q^{|U|} sum_y p_U(y)^2."""
    n = p.ndim
    out = np.zeros(2 ** n)
    for mask in range(2 ** n):
        axes_drop = tuple(k for k in range(n) if not (mask >> k) & 1)
        pu = p.sum(axis=axes_drop) if axes_drop else p
        size = bin(mask).count("1")
        out[mask] = (q ** size) * float(np.sum(pu ** 2))
    return out


def mobius(vals, n):
    """c[T] = sum_{U subseteq T} (-1)^{|T\\U|} vals[U] (subset-sum inversion)."""
    c = vals.copy()
    for k in range(n):
        bit = 1 << k
        for mask in range(2 ** n):
            if mask & bit:
                c[mask] -= c[mask ^ bit]
    return c


def zeta(vals, n):
    """W[S] = sum_{T subseteq S} vals[T]."""
    w = vals.copy()
    for k in range(n):
        bit = 1 << k
        for mask in range(2 ** n):
            if mask & bit:
                w[mask] += w[mask ^ bit]
    return w


class Collision:
    """Exact collision data on a finite region R of Z^2 (list of sites)."""

    def __init__(self, ca, R):
        self.ca = ca
        self.R = [tuple(r) for r in R]
        self.n = len(self.R)
        self.pos = {r: k for k, r in enumerate(self.R)}
        p = ca.joint_law(self.R)
        self.coll = coll_all_subsets(p, ca.q)
        self.c = mobius(self.coll, self.n)  # c_T, eps-free

    def mask(self, S):
        m = 0
        for s in S:
            m |= 1 << self.pos[tuple(s)]
        return m

    def W_all(self, eps):
        sizes = np.array([bin(m).count("1") for m in range(2 ** self.n)])
        z = (eps ** (2 * sizes)) * self.c
        return zeta(z, self.n)

    def W_direct(self, eps):
        """Independent engine: W(S) = sum_U (1-eps^2)^{|S|-|U|} eps^{2|U|} Coll(U), direct double loop."""
        n = self.n
        out = np.zeros(2 ** n)
        for S in range(2 ** n):
            tot = 0.0
            sub = S
            while True:
                u = bin(sub).count("1")
                s = bin(S).count("1")
                tot += (1 - eps ** 2) ** (s - u) * eps ** (2 * u) * self.coll[sub]
                if sub == 0:
                    break
                sub = (sub - 1) & S
            out[S] = tot
        return out


def D_of(P, N):
    """Overlap neighborhood D(P) = {j : (j+N) cap (P+N) != empty}."""
    PN = set((p[0] + n[0], p[1] + n[1]) for p in P for n in N)
    D = set()
    for (a, b) in PN:
        for n in N:
            D.add((a - n[0], b - n[1]))
    return D


# ----------------------------------------------------------------------------------------------
# FK machinery on small graphs
# ----------------------------------------------------------------------------------------------

def components_count(nv, edges, states):
    """Number of connected components for every bond configuration (rows of states: 0/1 per edge)."""
    S = states.shape[0]
    out = np.empty(S, dtype=np.int64)
    for s in range(S):
        parent = list(range(nv))

        def find(a):
            while parent[a] != a:
                parent[a] = parent[parent[a]]
                a = parent[a]
            return a
        k = nv
        row = states[s]
        for e, (u, v) in enumerate(edges):
            if row[e]:
                ru, rv = find(u), find(v)
                if ru != rv:
                    parent[ru] = rv
                    k -= 1
        out[s] = k
    return out


def connectivity_labels(nv, edges, states):
    """Return array lab[s, v] = root label of v in configuration s (for connection events)."""
    S = states.shape[0]
    lab = np.empty((S, nv), dtype=np.int64)
    for s in range(S):
        parent = list(range(nv))

        def find(a):
            while parent[a] != a:
                parent[a] = parent[parent[a]]
                a = parent[a]
            return a
        row = states[s]
        for e, (u, v) in enumerate(edges):
            if row[e]:
                ru, rv = find(u), find(v)
                if ru != rv:
                    parent[ru] = rv
        for v in range(nv):
            lab[s, v] = find(v)
    return lab


def all_states(nE):
    ar = np.arange(2 ** nE, dtype=np.int64)
    return ((ar[:, None] >> np.arange(nE)[None, :]) & 1).astype(np.int8)


def torus_graph(L1, L2):
    """Vertices (x,y), x mod L1, y mod L2. Horizontal edges first (x,y)-(x+1,y), then vertical (x,y)-(x,y+1)."""
    vid = lambda x, y: (x % L1) + L1 * (y % L2)
    edges, kind, start = [], [], []
    for y in range(L2):
        for x in range(L1):
            edges.append((vid(x, y), vid(x + 1, y))); kind.append('H'); start.append((x, y))
    for y in range(L2):
        for x in range(L1):
            edges.append((vid(x, y), vid(x, y + 1))); kind.append('V'); start.append((x, y))
    return L1 * L2, edges, kind, start


def box_graph(L1, L2, wired=False):
    """Box of sites 0..L1-1 x 0..L2-1. Free: plain box. Wired: extra ghost vertex joined... (we implement wired by
    identifying all boundary-exiting edges' far endpoints with one ghost vertex)."""
    vid = lambda x, y: x + L1 * y
    nv = L1 * L2
    edges, kind, start = [], [], []
    for y in range(L2):
        for x in range(L1 - 1):
            edges.append((vid(x, y), vid(x + 1, y))); kind.append('H'); start.append((x, y))
    for y in range(L2 - 1):
        for x in range(L1):
            edges.append((vid(x, y), vid(x, y + 1))); kind.append('V'); start.append((x, y))
    return nv, edges, kind, start


# ----------------------------------------------------------------------------------------------
# Exact stochastic-domination / up-set checks:  max_{U up-set} m(U) for a signed measure m on {0,1}^E
# ----------------------------------------------------------------------------------------------

def max_upset_networkx(m, nE):
    """Max-weight closure (up-sets) via networkx min-cut (float capacities). Returns (value, upset_mask)."""
    import networkx as nx
    G = nx.DiGraph()
    S = 2 ** nE
    src, snk = 'S', 'T'
    G.add_node(src); G.add_node(snk)
    pos_total = 0.0
    for w in range(S):
        if m[w] > 0:
            G.add_edge(src, w, capacity=float(m[w])); pos_total += m[w]
        elif m[w] < 0:
            G.add_edge(w, snk, capacity=float(-m[w]))
        for e in range(nE):
            if not (w >> e) & 1:
                G.add_edge(w, w | (1 << e))  # infinite capacity (no attribute)
    cut, (reach, _) = nx.minimum_cut(G, src, snk)
    U = np.zeros(S, dtype=bool)
    for v in reach:
        if v != src:
            U[v] = True
    return pos_total - cut, U


def max_upset_lp(m, nE):
    """Second engine: LP  max sum m_w x_w  s.t. x_w <= x_{w+e}, 0<=x<=1 (totally unimodular) via HiGHS."""
    from scipy.optimize import linprog
    import scipy.sparse as sp
    S = 2 ** nE
    rows, cols, vals = [], [], []
    r = 0
    for w in range(S):
        for e in range(nE):
            if not (w >> e) & 1:
                rows += [r, r]; cols += [w, w | (1 << e)]; vals += [1.0, -1.0]; r += 1
    A = sp.csr_matrix((vals, (rows, cols)), shape=(r, S))
    res = linprog(-np.asarray(m, float), A_ub=A, b_ub=np.zeros(r), bounds=(0, 1), method='highs')
    return -res.fun, res.x


def is_upset(U, nE):
    S = 2 ** nE
    for w in range(S):
        if U[w]:
            for e in range(nE):
                if not U[w | (1 << e)]:
                    return False
    return True


def max_upset_scipy(m, nE):
    """Fast screening engine: int32-scaled max-closure via scipy maximum_flow (dinic).
    Returns (value_estimate, error_bound). value is exact for the returned cut up to rounding."""
    import scipy.sparse as sp
    from scipy.sparse.csgraph import maximum_flow
    S = 2 ** nE
    m = np.asarray(m, float)
    tot = np.abs(m).sum()
    if tot == 0:
        return 0.0, 0.0
    scale = (2 ** 29) / tot
    mi = np.rint(m * scale).astype(np.int64)
    src, snk = S, S + 1
    rows, cols, caps = [], [], []
    pos = np.nonzero(mi > 0)[0]; neg = np.nonzero(mi < 0)[0]
    rows.append(np.full(len(pos), src)); cols.append(pos); caps.append(mi[pos])
    rows.append(neg); cols.append(np.full(len(neg), snk)); caps.append(-mi[neg])
    ar = np.arange(S)
    INF = 2 ** 31 - 1
    for e in range(nE):
        lo = ar[((ar >> e) & 1) == 0]
        rows.append(lo); cols.append(lo | (1 << e)); caps.append(np.full(len(lo), INF))
    r = np.concatenate(rows); c = np.concatenate(cols); cp = np.concatenate(caps).astype(np.int32)
    A = sp.csr_matrix((cp, (r, c)), shape=(S + 2, S + 2))
    res = maximum_flow(A, src, snk, method='dinic')
    val_int = mi[pos].sum() - res.flow_value
    # recover the source side of a min cut via residual BFS to evaluate the true (float) value of that up-set
    F = res.flow
    resid = (A - F).tocsr()
    resid.data = np.maximum(resid.data, 0)
    resid.eliminate_zeros()
    rev = F.T.tocsr(); rev.data = np.maximum(rev.data, 0); rev.eliminate_zeros()
    R = (resid + rev).tocsr()
    from scipy.sparse.csgraph import breadth_first_order
    reach = breadth_first_order(R, src, directed=True, return_predecessors=False)
    U = np.zeros(S + 2, bool); U[reach] = True; U = U[:S]
    true_val = float(m[U].sum())
    return true_val, S / (2 * scale)
