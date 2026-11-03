"""Exact checks of the collision layer used by the Potts-SSB claim.

Engine 1: c_T from the inclusion-exclusion formula over output marginals.
Engine 2: W(C) by brute-force enumeration of both replicas on C+N.
Checks:
  (a) c_T >= 0 for every T tried (sum-of-squares identity);
  (b) surjective rules: all nonempty c_T == 0 and W(C) == 1 exactly;
  (c) W(C) = sum_{T subset C} lam^|T| c_T (expansion == brute force);
  (d) witness-to-bond-penalty lemma:
        W(C+e)/W(C) >= 1 + lam^k c_P / w_max^|D(P)|  when e completes P;
  (e) s != |A| breaks W == 1 in the surjective branch (why s must equal |A|).
All arithmetic is exact (fractions).
"""
import itertools, random
from fractions import Fraction as Fr

random.seed(20261103)


def make_ca(qa, N, rule):
    return dict(qa=qa, N=N, rule=rule)


def inputs_of(T, N):
    s = set()
    for (x, y) in T:
        for (a, b) in N:
            s.add((x + a, y + b))
    return sorted(s)


def output_dist(ca, T):
    """Exact distribution of (Y_i)_{i in T} under uniform iid input."""
    qa, N, rule = ca['qa'], ca['N'], ca['rule']
    T = list(T)
    inp = inputs_of(T, N)
    idx = {p: k for k, p in enumerate(inp)}
    dist = {}
    for cfg in itertools.product(range(qa), repeat=len(inp)):
        y = tuple(rule(tuple(cfg[idx[(i[0] + a, i[1] + b)]] for (a, b) in N)) for i in T)
        dist[y] = dist.get(y, 0) + 1
    tot = qa ** len(inp)
    return {k: Fr(v, tot) for k, v in dist.items()}


def c_T(ca, T, s=None):
    """E prod_{i in T} (s 1{Y_i=Y'_i} - 1), by inclusion-exclusion over subsets."""
    qa = ca['qa']
    if s is None:
        s = qa
    T = list(T)
    total = Fr(0)
    for r in range(len(T) + 1):
        for S in itertools.combinations(T, r):
            if r == 0:
                coll = Fr(1)
            else:
                d = output_dist(ca, S)
                coll = sum(p * p for p in d.values())
            total += (-1) ** (len(T) - r) * Fr(s) ** r * coll
    return total


def W_brute(ca, C, lam, s=None):
    qa, N, rule = ca['qa'], ca['N'], ca['rule']
    if s is None:
        s = qa
    C = list(C)
    if not C:
        return Fr(1)
    inp = inputs_of(C, N)
    idx = {p: k for k, p in enumerate(inp)}
    # distribution of output vector, then sum over pairs
    dist = {}
    for cfg in itertools.product(range(qa), repeat=len(inp)):
        y = tuple(rule(tuple(cfg[idx[(i[0] + a, i[1] + b)]] for (a, b) in N)) for i in C)
        dist[y] = dist.get(y, 0) + 1
    tot = Fr(qa ** len(inp)) ** 2
    acc = Fr(0)
    items = list(dist.items())
    for y, cy in items:
        for y2, cy2 in items:
            prod = Fr(1)
            for a, b in zip(y, y2):
                prod *= 1 + lam * (s * (1 if a == b else 0) - 1)
            acc += cy * cy2 * prod
    return acc / tot


def W_expand(ca, C, lam, cache):
    C = list(C)
    tot = Fr(0)
    for r in range(len(C) + 1):
        for T in itertools.combinations(C, r):
            key = tuple(sorted(T))
            if key not in cache:
                cache[key] = c_T(ca, key) if key else Fr(1)
            tot += lam ** r * cache[key]
    return tot


def D_of(P, N):
    PN = set(inputs_of(P, N))
    out = set()
    # j with (j+N) cap (P+N) nonempty: j in PN - N
    for (x, y) in PN:
        for (a, b) in N:
            out.add((x - a, y - b))
    return out


def run():
    N1 = [(0, 0), (1, 0)]
    N2 = [(0, 0), (1, 0), (0, 1)]
    cas = {
        'XOR2 (onto)': make_ca(2, N1, lambda v: v[0] ^ v[1]),
        'AND2 (not onto)': make_ca(2, N1, lambda v: v[0] & v[1]),
        'XOR3 (onto)': make_ca(2, N2, lambda v: v[0] ^ v[1] ^ v[2]),
        'MAJ3 (not onto)': make_ca(2, N2, lambda v: 1 if sum(v) >= 2 else 0),
        'ID-perm q3 (onto)': make_ca(3, N1, lambda v: (v[0] + 2 * v[1]) % 3),
    }
    # two random rules on 3 symbols, neighbourhood N1
    for t in range(2):
        tab = {k: random.randrange(3) for k in itertools.product(range(3), repeat=2)}
        cas[f'random q3 #{t}'] = make_ca(3, N1, lambda v, tab=tab: tab[v])

    centers = [(0, 0), (1, 0), (2, 0), (0, 1), (1, 1)]
    lam = Fr(1, 3)
    report = []
    allok = True
    for name, ca in cas.items():
        cache = {}
        neg = 0
        nz = 0
        nsets = 0
        minpos = None
        for r in range(1, 4):
            for T in itertools.combinations(centers, r):
                c = c_T(ca, T)
                cache[tuple(sorted(T))] = c
                nsets += 1
                if c < 0:
                    neg += 1
                if c != 0:
                    nz += 1
                    if minpos is None or len(T) < len(minpos[0]):
                        minpos = (T, c)
        # expansion vs brute force on random C
        mism = 0
        Wvals = []
        for trial in range(6):
            C = random.sample(centers, random.randint(1, 4))
            wb = W_brute(ca, C, lam)
            we = W_expand(ca, C, lam, cache)
            Wvals.append(wb)
            if wb != we:
                mism += 1
        # witness lemma
        lemma_ok = None
        worst = None
        if minpos is not None:
            P, cP = minpos
            k = len(P)
            qa = ca['qa']
            wmax = 1 + lam * (qa - 1)
            Dsz = len(D_of(P, ca['N']))
            bound = 1 + lam ** k * cP / wmax ** Dsz
            lemma_ok = True
            # e = each member of P; C = (P - e) plus random extra centers from a wider pool
            pool = [(x, y) for x in range(-1, 4) for y in range(-1, 3)]
            for e in P:
                for trial in range(5):
                    extra = random.sample([p for p in pool if p not in P], random.randint(0, 3))
                    C = [p for p in P if p != e] + extra
                    r_ = W_brute(ca, C + [e], lam) / W_brute(ca, C, lam)
                    if r_ < bound:
                        lemma_ok = False
                    worst = r_ if worst is None or r_ < worst else worst
            lemma_info = f'P={P} k={k} c_P={cP} |D(P)|={Dsz} bound={float(bound):.6f} min ratio={float(worst):.6f}'
        else:
            lemma_info = 'no witness found among |T|<=3 (consistent with onto)'
        ok = (neg == 0 and mism == 0 and (lemma_ok in (None, True)))
        if 'onto)' in name and '(not' not in name:
            ok = ok and nz == 0 and all(w == 1 for w in Wvals)
        allok = allok and ok
        report.append(f'{name}: sets={nsets} negative c_T={neg} nonzero c_T={nz} '
                      f'expansion-vs-brute mismatches={mism} W(C) sample={[str(w) for w in Wvals[:3]]} | {lemma_info} | {"OK" if ok else "FAIL"}')
    # (e) s != |A| in the surjective branch
    ca = cas['XOR2 (onto)']
    C = [(0, 0), (1, 0), (2, 0)]
    W_s3 = W_brute(ca, C, lam, s=3)
    report.append(f'(e) XOR2 onto with s=3 != |A|=2: W(C) for |C|=3 is {W_s3} (= (1+lam*(s/q-1))^3 = {(1 + lam * (Fr(3, 2) - 1)) ** 3}); s must equal |A|')
    for line in report:
        print(line)
    print('ALL COLLISION CHECKS OK' if allok else 'SOME COLLISION CHECK FAILED')


if __name__ == '__main__':
    run()
