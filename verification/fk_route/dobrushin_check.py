"""Claim 1: Dobrushin coefficient of the space-time specification h_F = J 1{eta_{x,t} != f(eta_{x+N,t-1})}.
Counts n_xy (number of 10-site interaction sets containing x and y), checks sum_y n_xy = 90, and samples
random boundary conditions to compare the actual single-site TV distances with the Georgii bound
c_xy <= tanh(J n_xy / 2) <= J n_xy / 2 (the claim uses the weaker 2 J n_xy)."""
import itertools, random, math
import numpy as np

N = [(a, b) for a in (-1, 0, 1) for b in (-1, 0, 1)]

def main():
    rng = random.Random(3)
    J = 1e-3
    for q in (2, 3):
        f = {w: rng.randrange(q) for w in itertools.product(range(q), repeat=9)}
        zs = [(d, 1) for d in N]                      # time +1 sites whose input set contains x
        t0 = sorted({(dz[0] + a, dz[1] + b) for dz in N for (a, b) in N} - {(0, 0)})
        tm1 = [(d, -1) for d in N]
        others = [(s, 0) for s in t0] + zs + tm1
        def nxy(y):
            s, t = y
            if t != 0:
                return 1
            return sum(1 for dz in N if (s[0] - dz[0], s[1] - dz[1]) in N)
        tot = sum(nxy(y) for y in others)
        def cond(eta):
            b0 = f[tuple(eta[((a, b), -1)] for (a, b) in N)]
            en = np.zeros(q)
            for a in range(q):
                e = (a != b0)
                for dz in N:
                    inp = tuple(a if (dz[0] + u, dz[1] + v) == (0, 0) else eta[((dz[0] + u, dz[1] + v), 0)] for (u, v) in N)
                    e += (eta[(dz, 1)] != f[inp])
                en[a] = J * e
            p = np.exp(-en); return p / p.sum()
        worst_ratio = 0.0
        csum_est = {}
        for _ in range(4000):
            eta = {y: rng.randrange(q) for y in others}
            y = rng.choice(others)
            eta2 = dict(eta); eta2[y] = (eta[y] + rng.randrange(1, q)) % q
            tv = 0.5 * np.abs(cond(eta) - cond(eta2)).sum()
            bound = math.tanh(J * nxy(y) / 2)
            worst_ratio = max(worst_ratio, tv / bound)
            csum_est[y] = max(csum_est.get(y, 0), tv)
        print(f'q={q}: sum_y n_xy = {tot} (claim: 90); 2J*90 = {2*J*tot:.3f}; Georgii J*90/2 = {J*tot/2:.4f}; '
              f'max sampled TV / tanh(J n_xy/2) = {worst_ratio:.3f}; sampled lower estimate of sum_y c_xy = {sum(csum_est.values()):.4f}')

if __name__ == '__main__':
    main()
