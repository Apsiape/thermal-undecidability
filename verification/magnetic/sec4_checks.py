"""Section 4 checks (one row of horizontal factors; rowwise CA with N = {0, 1}).

(A) Hidden insertion ratios with ARBITRARY hidden boundary condition xi:
      R_xi(C, e; window) = E^xi[prod_{C+e} w] / E^xi[prod_C w]
    computed by transfer matrices.  Checks: convergence (uniform in C and xi) to a limit R_inf as the window grows
    (claim (17)); R_inf >= 1 always and >= 1 + a_P when closing e completes a witness translate (claim (18));
    and that near a fixed hidden boundary R can be < 1 (why the infinite-volume formulation is needed).
(B) Exact Dobrushin coefficients of the hidden specification, versus the bound L m (m-1)/2 <= 4 L m (m-1)  (claim (3)).
(C) Brute-force check of the exact edge-odds identity (19) in a small joint (visible + hidden + bond) system with
    fixed hidden boundary and fixed visible boundary spins.
"""
import itertools
import numpy as np

rng = np.random.default_rng(7)


def selector(a, b):
    Ua, Ca = a % 2, a // 2
    Ub = b % 2
    return (Ua if Ca == 0 else Ub) + 2 * Ca


def and2(a, b):
    return a & b


def make_w(q, f, eps):
    """w as a (q^2 x q^2) matrix over hidden pair-states s=(x,x') at sites i, i+1."""
    S = q * q
    w = np.empty((S, S))
    for s in range(S):
        x, xp = divmod(s, q)
        for t in range(S):
            y, yp = divmod(t, q)
            same = f(x, y) == f(xp, yp)
            w[s, t] = 1 + eps ** 2 * (q * same - 1)
    return w


def W_window(w, q, closed, n, left_bc, right_bc):
    """closed: boolean array of length n (factor i between hidden sites i and i+1); hidden sites 0..n.
    Boundary hidden at sites 0 and n fixed (or None = uniform)."""
    S = q * q
    v = np.full(S, 1.0 / S) if left_bc is None else np.eye(S)[left_bc]
    for i in range(n):
        M = (w if closed[i] else np.ones((S, S))) / S
        v = v @ M
        v = v / 1.0
    if right_bc is None:
        return v.sum()
    return v[right_bc] * S  # undo the 1/S of last step's site (conditioning on site n)


def ratio(w, q, closed, e, left_bc, right_bc):
    c2 = closed.copy(); c2[e] = True
    return W_window(w, q, c2, len(closed), left_bc, right_bc) / W_window(w, q, closed, len(closed), left_bc, right_bc)


def partA(name, q, f, eps, P_offsets, cP):
    print("=" * 100)
    S = q * q
    w = make_w(q, f, eps)
    wmax = 1 + eps ** 2 * (q - 1)
    k = len(P_offsets)
    Dsize = (max(P_offsets) - min(P_offsets) + 1) + 2  # D(P) for N={0,1}: [min-1, max+1]
    aP = eps ** (2 * k) * cP / wmax ** Dsize
    print("%s, eps=%.2f: witness offsets %s, c_P=%.4f, |D(P)|=%d, 1+a_P=%.6f" % (name, eps, P_offsets, cP, Dsize, 1 + aP))
    # random closed configurations on a long line; e at center
    half_sizes = [2, 4, 8, 16, 32]
    worst_spread = {h: 0.0 for h in half_sizes}
    min_Rinf, min_Rinf_completed, n_completed = np.inf, np.inf, 0
    min_near_boundary = np.inf
    for trial in range(300):
        Lbig = 2 * 40 + 1
        dens = rng.uniform(0.2, 0.95)
        closed_big = rng.random(Lbig) < dens
        c = Lbig // 2
        closed_big[c] = False
        # force witness completion in half the trials
        if trial % 2 == 0:
            j = rng.integers(0, k)
            base = c - P_offsets[j]
            for o in P_offsets:
                if base + o != c:
                    closed_big[base + o] = True
        completed = any(all(closed_big[c - P_offsets[j] + o] or (c - P_offsets[j] + o == c) for o in P_offsets)
                        for j in range(k))
        Rs = {}
        for h in half_sizes + [40]:
            vals = []
            sub = closed_big[c - h:c + h + 1]
            for lb in [None, 0, S - 1, int(rng.integers(S))]:
                for rb in [None, 0, S - 1, int(rng.integers(S))]:
                    vals.append(ratio(w, q, sub, h, lb, rb))
            Rs[h] = (min(vals), max(vals))
        Rinf = 0.5 * (Rs[40][0] + Rs[40][1])
        for h in half_sizes:
            worst_spread[h] = max(worst_spread[h], max(abs(Rs[h][0] - Rinf), abs(Rs[h][1] - Rinf)))
        min_Rinf = min(min_Rinf, Rinf)
        if completed:
            n_completed += 1
            min_Rinf_completed = min(min_Rinf_completed, Rinf)
        min_near_boundary = min(min_near_boundary, Rs[2][0])
    print("  sup_{C, xi} |R_window - R_inf| by half-window: " +
          ", ".join("h=%d: %.2e" % (h, worst_spread[h]) for h in half_sizes))
    print("  min R_inf over all trials = %.6f (>= 1? %s)" % (min_Rinf, min_Rinf >= 1 - 1e-12))
    print("  min R_inf over %d witness-completing trials = %.6f  (>= 1+a_P=%.6f? %s)" %
          (n_completed, min_Rinf_completed, 1 + aP, min_Rinf_completed >= 1 + aP))
    print("  min ratio with half-window 2 and adversarial fixed hidden boundary = %.6f (can be < 1: boundary layer)" %
          min_near_boundary)


def partB(q, f, eps):
    """Exact Dobrushin row sum for the 1D hidden spec: site j interacts via factors j-1 (sites j-1,j) and j (j,j+1).
    c_{j,l} = sup over boundary configs differing only at l of TV of the single-site conditional at j."""
    S = q * q
    w = make_w(q, f, eps)
    L = np.log((1 + (q - 1) * eps ** 2) / (1 - eps ** 2))
    worst = 0.0
    # all factors closed (worst case); conditional at j given s_{j-1}=a, s_{j+1}=b: ~ w[a, s] w[s, b]
    row = 0.0
    for l in ['left', 'right']:
        cmax = 0.0
        for a in range(S):
            for a2 in range(S):
                for b in range(S):
                    if l == 'left':
                        p1 = w[a, :] * w[:, b]; p2 = w[a2, :] * w[:, b]
                    else:
                        p1 = w[b, :] * w[:, a]; p2 = w[b, :] * w[:, a2]
                    p1 /= p1.sum(); p2 /= p2.sum()
                    cmax = max(cmax, 0.5 * np.abs(p1 - p2).sum())
        row += cmax
    m = 2
    print("  Dobrushin (q=%d, eps=%.3f): exact row sum = %.3e ; L m(m-1)/2 = %.3e ; claimed 4 L m(m-1) = %.3e" %
          (q, eps, row, L * m * (m - 1) / 2, 4 * L * m * (m - 1)))


def partC(q, f, eps, n=3, pH=2 / 3, seed=0):
    """Joint brute force: visible sites 0..n+1 with sigma_0, sigma_{n+1} fixed (+,+ or +,-), edges (i,i+1), i=0..n.
    Hidden pair-states at sites 0..n+1 (factor i uses hidden sites i, i+1); hidden sites 0 and n+1 fixed (xi).
    Check (19): odds(omega_e=1 | rest) = y * alpha / R  with  alpha = P(sigma_u=sigma_v | omega_e=0, rest) and
    R = E^xi[prod_{C+e} w]/E^xi[prod_C w]  (C = closed set of the rest)."""
    rs = np.random.default_rng(seed)
    S = q * q
    w = make_w(q, f, eps)
    y = pH / (1 - pH)
    nE = n + 1
    xi_l, xi_r = int(rs.integers(S)), int(rs.integers(S))
    worst = 0.0
    for bc in [(1, 1), (1, -1)]:
        # enumerate sigma_1..sigma_n, hidden s_1..s_n, bonds
        joint = {}
        for sig in itertools.product([1, -1], repeat=n):
            sigma = (bc[0],) + sig + (bc[1],)
            for hid in itertools.product(range(S), repeat=n):
                h = (xi_l,) + hid + (xi_r,)
                for om in itertools.product([0, 1], repeat=nE):
                    wt = 1.0
                    for i in range(nE):
                        if om[i]:
                            wt *= pH * (sigma[i] == sigma[i + 1])
                        else:
                            wt *= (1 - pH) * w[h[i], h[i + 1]]
                        if wt == 0:
                            break
                    if wt:
                        joint[(sig, hid, om)] = joint.get((sig, hid, om), 0) + wt
        # bond marginal and alpha
        bond = {}
        same = {}
        for (sig, hid, om), wt in joint.items():
            bond[om] = bond.get(om, 0) + wt
        for e in range(nE):
            for om in itertools.product([0, 1], repeat=nE):
                if om[e] == 1:
                    continue
                om1 = om[:e] + (1,) + om[e + 1:]
                if bond.get(om, 0) == 0:
                    continue
                lhs = bond.get(om1, 0) / bond[om]
                # alpha
                num = 0.0
                for (sig, hid, o), wt in joint.items():
                    if o == om:
                        sigma = (bc[0],) + sig + (bc[1],)
                        num += wt * (sigma[e] == sigma[e + 1])
                alpha = num / bond[om]
                closed = np.array([om[i] == 0 for i in range(nE)])
                closed_wo = closed.copy(); closed_wo[e] = False
                # R with hidden boundary: hidden sites 0..n+1 -> transfer over n+1 factors, both ends fixed
                R = ratio(w, q, closed_wo, e, xi_l, xi_r)
                rhs = y * alpha / R
                worst = max(worst, abs(lhs - rhs) / max(rhs, 1e-300))
    print("  (19) brute force, n=%d visible interior sites, hidden bc=(%d,%d), visible bc (+,+),(+,-): "
          "max rel error = %.2e" % (n, xi_l, xi_r, worst))


if __name__ == "__main__":
    # witness data: selector -> P = {0,1}, c_P = 0.25 (sec2); AND -> P = {0}, c_P computed here
    # c_{0} for AND: law of x_i x_{i+1}: P(1)=1/4 -> Coll = 2*(1/16+9/16) = 1.25 -> c = 0.25
    partA("selector CA (q=4)", 4, selector, 0.9, [0, 1], 0.25)
    partA("selector CA (q=4)", 4, selector, 0.5, [0, 1], 0.25)
    partA("AND rule (q=2)", 2, and2, 0.9, [0], 0.25)
    print("=" * 100)
    for (q, f, nm) in [(4, selector, 'selector'), (2, and2, 'AND')]:
        for eps in [0.5, 0.1, 0.01]:
            partB(q, f, eps)
    print("=" * 100)
    partC(4, selector, 0.9, n=2, seed=1)
    partC(4, selector, 0.9, n=2, seed=2)
    partC(2, and2, 0.9, n=3, seed=3)
    partC(2, and2, 0.9, n=3, seed=4)
