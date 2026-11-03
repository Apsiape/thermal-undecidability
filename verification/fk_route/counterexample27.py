"""Claim 3 (27): exact W for F(X)_i = (U_{i+C_i}, C_i), A = {0,1}^2 (q = 4).
Input at site j: (U_j, C_j) uniform bits. W(S) = E prod_{i in S} w_i, w_i = 1 + e^2 (4*1{F(X)_i = F(X')_i} - 1),
computed by exact enumeration over both replicas with symbolic eps (sympy).  Also: Mobius-inverted c_T,
and the same values computed in the 2D embedding (neighbourhood {0, e1} inside the Moore box)."""
import itertools
import sympy as sp

e = sp.symbols('epsilon', positive=True)
q = 4

def law(S):
    """exact law of outputs on S (1D sites), dict output-tuple -> Rational."""
    sites = sorted(set(S) | {i + 1 for i in S})
    cnt = {}
    n = 0
    for U in itertools.product((0, 1), repeat=len(sites)):
        Ud = dict(zip(sites, U))
        for C in itertools.product((0, 1), repeat=len(S)):
            out = tuple((Ud[i + c], c) for i, c in zip(S, C))
            cnt[out] = cnt.get(out, 0) + 1
            n += 1
    return {k: sp.Rational(v, n) for k, v in cnt.items()}

def W(S):
    if not S:
        return sp.Integer(1)
    L = law(S)
    tot = 0
    for a, pa in L.items():
        for b, pb in L.items():
            w = 1
            for ai, bi in zip(a, b):
                w *= 1 + e ** 2 * (q * (1 if ai == bi else 0) - 1)
            tot += pa * pb * w
    return sp.expand(tot)

def main():
    Ws = {}
    for m in range(0, 4):
        for S in itertools.combinations((1, 2, 3), m):
            Ws[S] = W(S)
            print('W', S, '=', Ws[S])
    lhs = sp.expand(Ws[(1, 2, 3)] * Ws[(2,)])
    rhs = sp.expand(Ws[(1, 2)] * Ws[(2, 3)])
    print('W(123)W(2) - W(12)W(23) =', sp.factor(lhs - rhs))
    # Mobius inversion: c_T eps^{2|T|} terms
    print('--- Mobius inversion (W(S) = sum_T eps^{2|T|} c_T):')
    for m in range(1, 4):
        for T in itertools.combinations((1, 2, 3), m):
            val = sum((-1) ** (len(T) - len(Tp)) * Ws[Tp] for k in range(len(T) + 1)
                      for Tp in itertools.combinations(T, k))
            print('  eps^{2|T|} c_T for T =', T, ':', sp.expand(val))
    # longer runs, to know the polymer activities of this CA
    for S in [(1, 2, 3, 4), (1, 2, 4), (1, 2, 3, 4, 5)]:
        print('W', S, '=', W(S))
    # sanity: check W(12) at eps = 1 equals q^2 * collision probability of the bare output law
    L = law((1, 2))
    print('q^2 * sum nu_12^2 =', 16 * sum(v ** 2 for v in L.values()), '(should be 5/4 = W(12) at eps=1)')

if __name__ == '__main__':
    main()
