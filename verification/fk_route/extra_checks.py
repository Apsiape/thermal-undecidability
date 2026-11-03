"""(a) Locate the negative edge-edge covariance of the tilted measure in the 4x3 box (association failure).
(b) For random 1D CAs (r=1): check the inequalities used in the reviewer's Holley reduction:
      W(C) <= q^{|C cap Y|} W(C \\ Y)                      (collision-probability bound)
      W(C u e) - W(C) = sum_{P polymer, e in P, P subset C u e} z_P W(C \\ Pdot)   (polymer identity)
    where polymers = 'connected' sets (gaps <= 2), compatibility = distance >= 3, Pdot = P + [-2,2]."""
import itertools, random
import numpy as np
from fkg_tests import build_box, all_weights
from claim2_identities import rand_rule, W_direct, c_T

def part_a():
    sites, edges = build_box(4, 3)
    nE = len(edges)
    for eps in (0.95, 0.98, 0.999):
        fk, tilt, _ = all_weights(sites, edges, eps)
        mu = fk * tilt; mu /= mu.sum()
        X = np.array([[(m >> i) & 1 for i in range(nE)] for m in range(1 << nE)], dtype=float)
        Em = mu @ X
        cov = (X * mu[:, None]).T @ X - np.outer(Em, Em)
        np.fill_diagonal(cov, np.inf)
        i, j = np.unravel_index(np.argmin(cov), cov.shape)
        print(f'(a) eps={eps}: min Cov = {cov[i, j]:.3e} between edge {edges[i][2:]} and edge {edges[j][2:]}  [(orientation, start site)]')

def components(T):
    T = sorted(T)
    comps, cur = [], [T[0]]
    for t in T[1:]:
        if t - cur[-1] <= 2:
            cur.append(t)
        else:
            comps.append(tuple(cur)); cur = [t]
    comps.append(tuple(cur))
    return comps

def part_b():
    rng = random.Random(7)
    worst_bound = -np.inf
    worst_id = 0.0
    for trial in range(10):
        q = 2
        f = rand_rule(q, rng=rng)
        eps = 0.8
        cache = {}
        def Wf(S):
            S = tuple(sorted(S))
            if S not in cache:
                cache[S] = W_direct(f, q, S, eps) if S else 1.0
            return cache[S]
        zc = {}
        def z(P):
            P = tuple(sorted(P))
            if P not in zc:
                zc[P] = eps ** (2 * len(P)) * c_T(f, q, P)
            return zc[P]
        for _ in range(6):
            C = set(rng.sample(range(0, 7), rng.randint(1, 4)))
            Y = set(rng.sample(range(0, 7), 2))
            lhs = Wf(C)
            rhs = q ** len(C & Y) * Wf(C - Y)
            worst_bound = max(worst_bound, lhs - rhs)
            e = rng.choice([s for s in range(0, 7) if s not in C] or [7])
            Ce = C | {e}
            diff = Wf(Ce) - Wf(C)
            tot = 0.0
            for m in range(1, len(Ce) + 1):
                for P in itertools.combinations(sorted(Ce), m):
                    if e in P and len(components(P)) == 1:
                        Pdot = {s + d for s in P for d in range(-2, 3)}
                        tot += z(P) * Wf(C - Pdot)
            worst_id = max(worst_id, abs(diff - tot))
    print('(b) max [W(C) - q^{|C^Y|} W(C\\Y)] (<=0 expected):', worst_bound)
    print('(b) max |W(Cue)-W(C) - sum_P z_P W(C\\Pdot)| :', worst_id)

if __name__ == '__main__':
    part_a()
    part_b()
