"""Exact 1D surjectivity decision (subset construction on the de Bruijn graph) for the rules of
claim2_identities.py, to resolve the 'MISMATCH' lines: they must all be NON-surjective rules whose
shortest Garden of Eden is longer than the brute-force search window (so W(S) != 1 there is correct)."""
import itertools, random
from claim2_identities import rand_rule, W_direct

def surjective(f, q):
    states = list(itertools.product(range(q), repeat=2))
    start = frozenset(states)
    seen = {start: 0}
    frontier = [start]
    while frontier:
        nxt = []
        for Sset in frontier:
            for b in range(q):
                T = frozenset((s[1], c) for s in Sset for c in range(q) if f[(s[0], s[1], c)] == b)
                if not T:
                    return False, seen[Sset] + 1
                if T not in seen:
                    seen[T] = seen[Sset] + 1
                    nxt.append(T)
        frontier = nxt
    return True, None

def main():
    rng = random.Random(20261102)
    rules = []
    for q in (2, 3):
        for _ in range(12):
            rules.append((q, rand_rule(q, rng=rng)))
    for q in (2, 3):
        rules.append((q, {w: (w[0] + w[2]) % q for w in itertools.product(range(q), repeat=3)}))
        rules.append((q, {w: (w[1] + 2 * w[2] + w[0] * w[1]) % q for w in itertools.product(range(q), repeat=3)}))
    sets = [(0,), (0, 1), (0, 2), (0, 1, 2), (0, 3), (0, 1, 3), (0, 1, 2, 3)]
    agree = 0
    for idx, (q, f) in enumerate(rules):
        s, L = surjective(f, q)
        Wone = all(abs(W_direct(f, q, S, 0.77) - 1) < 1e-12 for S in sets)
        # surjective => W == 1 must hold (theorem); W != 1 => non-surjective
        ok = (not s) or Wone
        agree += ok
        print(f'rule {idx:2d} q={q} surjective={s} shortest GoE length={L} W==1 on tested sets={Wone} consistent={ok}')
    print('consistent:', agree, '/', len(rules))

if __name__ == '__main__':
    main()
