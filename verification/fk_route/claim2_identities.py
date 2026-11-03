"""Claim 2 checks (exact enumeration, 1D CAs with neighbourhood {-1,0,1}; one 2D case).

For a CA F with local rule f, uniform input X, retention eps noise:
  W(S)   := E prod_{i in S} w_i(X,X'),  w_i = 1 + eps^2 (q 1{F(X)_i = F(X')_i} - 1)
  claim  W(S) = q^|S| sum_a mu_S(a)^2,   mu = noisy one-step output law
  claim  W(S) = sum_{T subset S} eps^{2|T|} c_T, c_T = sum_{k in (Z_q\0)^T} |E prod chi_k(F(X)_i)|^2 >= 0
  claim  c_T factorises over components of T with disjoint input neighbourhoods
  claim  F surjective  iff  W(S) = 1 for all S
Everything is computed with exact rationals / exact complex roots of unity in floating point
(tolerance 1e-12) -- the claims are identities, so floating agreement to 1e-12 suffices.
"""
import itertools, random
from fractions import Fraction
import numpy as np

def out_law(f, q, S, r=1):
    """Exact law nu_S of (F(X)_i)_{i in S} for uniform X (1D, nbhd {-r..r}). Returns dict."""
    lo, hi = min(S) - r, max(S) + r
    win = list(range(lo, hi + 1))
    law = {}
    tot = q ** len(win)
    for x in itertools.product(range(q), repeat=len(win)):
        xd = dict(zip(win, x))
        a = tuple(f[tuple(xd[i + d] for d in range(-r, r + 1))] for i in S)
        law[a] = law.get(a, 0) + 1
    return {a: Fraction(c, tot) for a, c in law.items()}, win

def W_direct(f, q, S, eps, r=1):
    """E prod w_i with X, X' independent uniform -- direct double enumeration over output pairs."""
    nu, _ = out_law(f, q, S, r)
    items = list(nu.items())
    tot = 0.0
    for a, pa in items:
        for b, pb in items:
            w = 1.0
            for ai, bi in zip(a, b):
                w *= 1 + eps ** 2 * (q * (ai == bi) - 1)
            tot += float(pa * pb) * w
    return tot

def W_collision(f, q, S, eps, r=1):
    """q^|S| sum_a mu_S(a)^2 where mu = noise(nu): each site kept w.p. eps else uniform."""
    nu, _ = out_law(f, q, S, r)
    n = len(S)
    K = eps * np.eye(q) + (1 - eps) * np.ones((q, q)) / q  # single-site channel
    vec = np.zeros([q] * n)
    for a, p in nu.items():
        vec[a] += float(p)
    for ax in range(n):
        vec = np.moveaxis(np.tensordot(K, vec, axes=([1], [ax])), 0, ax)
    return q ** n * float((vec ** 2).sum())

def c_T(f, q, T, r=1):
    """Fourier coefficient c_T = sum_{k in (Z_q\\0)^T} |E prod chi_{k_i}(F(X)_i)|^2."""
    if len(T) == 0:
        return 1.0
    nu, _ = out_law(f, q, T, r)
    om = np.exp(2j * np.pi / q)
    tot = 0.0
    for k in itertools.product(range(1, q), repeat=len(T)):
        s = 0
        for a, p in nu.items():
            s += float(p) * om ** sum(ki * ai for ki, ai in zip(k, a))
        tot += abs(s) ** 2
    return tot

def is_surjective_1d(f, q, r=1, maxlen=8):
    """Brute-force: F surjective iff every word of length L has a preimage (check L<=maxlen)."""
    for L in range(1, maxlen + 1):
        img = set()
        for x in itertools.product(range(q), repeat=L + 2 * r):
            img.add(tuple(f[x[i:i + 2 * r + 1]] for i in range(L)))
        if len(img) < q ** L:
            return False, L
    return True, None

def rand_rule(q, r=1, onto=True, rng=random):
    while True:
        f = {w: rng.randrange(q) for w in itertools.product(range(q), repeat=2 * r + 1)}
        if not onto or len(set(f.values())) == q:
            return f

def main():
    rng = random.Random(20261102)
    worst = 0.0
    n_rules = 0
    min_c = 1e9
    fact_err = 0.0
    surj_ok = 0
    rules = []
    # random onto rules + a few known surjective ones (XOR / permutive)
    for q in (2, 3):
        for _ in range(12):
            rules.append((q, rand_rule(q, rng=rng)))
    for q in (2, 3):
        rules.append((q, {w: (w[0] + w[2]) % q for w in itertools.product(range(q), repeat=3)}))  # permutive
        rules.append((q, {w: (w[1] + 2 * w[2] + w[0] * w[1]) % q for w in itertools.product(range(q), repeat=3)}))  # right-permutive
    for q, f in rules:
        n_rules += 1
        sets = [(0,), (0, 1), (0, 2), (0, 1, 2), (0, 3), (0, 1, 3), (0, 1, 2, 3)]
        if q == 2:
            sets += [(0, 1, 2, 3, 4), (0, 1, 4, 5)]
        allone = True
        for S in sets:
            for eps in (0.3, 0.77):
                wd = W_direct(f, q, S, eps)
                wc = W_collision(f, q, S, eps)
                # Fourier / polymer expansion
                wf = 0.0
                for m in range(len(S) + 1):
                    for T in itertools.combinations(S, m):
                        c = c_T(f, q, T)
                        min_c = min(min_c, c)
                        wf += eps ** (2 * m) * c
                worst = max(worst, abs(wd - wc), abs(wd - wf))
                assert wd >= 1 - 1e-12
                if abs(wd - 1) > 1e-12:
                    allone = False
        # factorisation: T = T1 u T2 with input nbhds disjoint (distance >= 3 for r=1)
        for T1, T2 in [((0,), (3,)), ((0, 1), (4,)), ((0, 1), (4, 5)), ((0, 2), (5,))]:
            fact_err = max(fact_err, abs(c_T(f, q, T1 + T2) - c_T(f, q, T1) * c_T(f, q, T2)))
        surj, L = is_surjective_1d(f, q, maxlen=6 if q == 2 else 4)
        # W == 1 on tested sets <=> no GoE found up to tested length (consistency check)
        if surj == allone:
            surj_ok += 1
        else:
            print('MISMATCH surj vs W==1 (may be GoE longer than tested sets):', q, surj, L, allone)
    print('rules tested:', n_rules)
    print('max |W_direct - collision|, |W_direct - Fourier sum| :', worst)
    print('min c_T over all T computed (should be >= 0):', min_c)
    print('max factorisation error |c_{T1uT2} - c_T1 c_T2|:', fact_err)
    print('rules where (surjective) == (W==1 on tested sets):', surj_ok, '/', n_rules)

    # explicit check of the eps^2 power: single-site collision of two independently noised copies
    for q in (2, 3, 5):
        for eps in (0.1, 0.5, 0.9):
            for same in (True, False):
                b, bp = 0, (0 if same else 1)
                pk = lambda c, b: eps * (c == b) + (1 - eps) / q
                coll = sum(pk(c, b) * pk(c, bp) for c in range(q))
                w = 1 + eps ** 2 * (q * same - 1)
                assert abs(q * coll - w) < 1e-12
    print('single-site: q * P(Y=Y\'|b,b\') == 1 + eps^2 (q 1{b=b\'} - 1)  [both copies noised]  OK')

    # 2D sanity: one random onto Moore-neighbourhood rule, q=2, S = two horizontally adjacent sites
    f2 = None
    while True:
        f2 = {w: rng.randrange(2) for w in itertools.product(range(2), repeat=9)}
        if len(set(f2.values())) == 2:
            break
    S2 = [(0, 0), (1, 0)]
    win = sorted({(i + dx, j + dy) for (i, j) in S2 for dx in (-1, 0, 1) for dy in (-1, 0, 1)})
    law = {}
    for x in itertools.product(range(2), repeat=len(win)):
        xd = dict(zip(win, x))
        a = tuple(f2[tuple(xd[(i + dx, j + dy)] for dx in (-1, 0, 1) for dy in (-1, 0, 1))] for (i, j) in S2)
        law[a] = law.get(a, 0) + 1
    tot = 2 ** len(win)
    eps = 0.6
    wd = sum(law[a] * law[b] / tot ** 2 * np.prod([1 + eps ** 2 * (2 * (ai == bi) - 1) for ai, bi in zip(a, b)])
             for a in law for b in law)
    nu = {a: c / tot for a, c in law.items()}
    K = eps * np.eye(2) + (1 - eps) * np.ones((2, 2)) / 2
    vec = np.zeros((2, 2))
    for a, p in nu.items():
        vec[a] += p
    vec = K @ vec @ K.T
    print('2D Moore rule, S = 2 adjacent sites: W_direct =', wd, ' q^2 sum mu^2 =', 4 * (vec ** 2).sum())

if __name__ == '__main__':
    main()
