"""Independent rational-arithmetic checks. Python standard library only.

These are finite algebraic checks, not numerical proofs of infinite-volume claims.
The checker reconstructs output laws and bond weights without importing either
review suite. Run from verification/: python exact_checks.py
"""
from collections import Counter
from fractions import Fraction as Q
from itertools import product, combinations
from functools import lru_cache


def subsets(items):
    items = tuple(items)
    for k in range(len(items) + 1):
        yield from combinations(items, k)


@lru_cache(None)
def law(S, alphabet, offsets, rule):
    S = tuple(S)
    inputs = sorted({x + n for x in S for n in offsets})
    count = Counter()
    for values in product(range(alphabet), repeat=len(inputs)):
        a = dict(zip(inputs, values))
        count[tuple(rule(tuple(a[x + n] for n in offsets)) for x in S)] += 1
    den = alphabet ** len(inputs)
    return {k: Q(v, den) for k, v in count.items()}


def collision(S, alphabet, offsets, rule):
    probs = law(S, alphabet, offsets, rule)
    return sum(pa * pb * prodq(alphabet * (a == b) - 1 for a, b in zip(ya, yb))
               for ya, pa in probs.items() for yb, pb in probs.items())


def prodq(values):
    ans = Q(1)
    for v in values:
        ans *= v
    return ans


def W_direct(S, alphabet, offsets, rule, eps):
    # Expand each local factor as (1-eps^2)+q eps^2 1{Y=Y'}.
    # Each collision probability is a sum of squares of a marginal law.
    S=tuple(sorted(S))
    ans=Q(0)
    for T in subsets(S):
        probs=law(T,alphabet,offsets,rule)
        ans+=(1-eps**2)**(len(S)-len(T))*(alphabet*eps**2)**len(T)*sum(p*p for p in probs.values())
    return ans


def selector(a):
    u, c = a[0] % 2, a[0] // 2
    return (u if c == 0 else a[1] % 2) + 2 * c


def upsets(n):
    """Exhaust every subset of the n-dimensional cube and test upward closure."""
    for mask in range(1 << (1 << n)):
        U = {s for s in range(1 << n) if (mask >> s) & 1}
        if all((s | (1 << e)) in U for s in U for e in range(n)):
            yield U


def normalize(w):
    total = sum(w)
    return [a / total for a in w]


def cov(p, f, g):
    return sum(a*b*c for a,b,c in zip(p,f,g)) - sum(a*b for a,b in zip(p,f))*sum(a*b for a,b in zip(p,g))


def main():
    eps = Q(1, 2)
    centers = (0, 1, 2)
    cs = {}
    for S in subsets(centers):
        c = collision(S, 4, (0, 1), selector)
        cs[S] = c
        assert c >= 0
        assert W_direct(S, 4, (0, 1), selector, eps) == sum(
            eps ** (2 * len(T)) * collision(T, 4, (0, 1), selector)
            for T in subsets(S))
    assert cs[(0,)] == 0 and cs[(0,1)] == Q(1,4)
    assert cs[(0,1,2)] == 0
    xor = lambda a: a[0] ^ a[1]
    for S in subsets(centers):
        assert collision(S, 2, (0,1), xor) == (1 if not S else 0)
        assert W_direct(S, 2, (0,1), xor, eps) == 1
    # Disjoint input supports imply exact factorization.
    assert collision((0,1,4,5),4,(0,1),selector) == cs[(0,1)] ** 2
    print("PASS: collision expansion, positivity, XOR control, factorization")

    wmax = 1 + 3 * eps ** 2
    aP = eps ** 4 * Q(1,4) / wmax ** 4
    allcenters = tuple(range(-1,4))
    ncompletion = 0
    for C in subsets(allcenters):
        C = set(C)
        for e in (0,1):
            if e not in C and {0,1} - {e} <= C:
                assert W_direct(C | {e},4,(0,1),selector,eps) >= (
                    1+aP)*W_direct(C,4,(0,1),selector,eps)
                ncompletion += 1
    print("PASS: witness completion",ncompletion,"exact cases; a_P =",aP)

    # Three-edge path: cluster count K=4-number of open edges.
    # Choose e^g=t^3 so e^(kappa*g)=t is rational for k=2.
    t = Q(100001,100000)
    assert t ** 6 <= 1 + aP
    states = list(range(8))
    I = [[int(not (s & (1<<i)) and not(s & (1<<(i+1)))) for s in states] for i in (0,1)]
    base = [Q(2) ** (4-s.bit_count()) * Q(2) ** s.bit_count() for s in states]
    target = normalize([b*W_direct([i for i in range(3) if not(s & (1<<i))],4,(0,1),selector,eps) for s,b in zip(states,base)])
    comp = normalize([b*t**(3*(I[0][s]+I[1][s])) for s,b in zip(states,base)])
    shifted = normalize([b*t**(-sum((s>>i)&1 for i in (0,1))) for s,b in zip(states,base)])
    for s in states:
        for z in states:
            assert comp[s|z]*comp[s&z] >= comp[s]*comp[z]
    countU=0
    for U in upsets(3):
        f=[int(s in U) for s in states]
        assert sum(target[s] for s in U) <= sum(comp[s] for s in U)
        assert sum(comp[s] for s in U) <= sum(shifted[s] for s in U)
        for i in (0,1):
            edge=[(s>>i)&1 for s in states]
            assert cov(comp,f,I[i]) <= -Q(1,3)*cov(comp,f,edge)
        countU+=1
    assert countU==20
    print("PASS: comparator FKG, two stochastic dominations, covariance inequality for all 20 upsets")

    # False kappa=1 must fail on a triangle with a closed two-edge reward.
    # A path can be too symmetric to detect this; enumerate triangle states.
    def Ktriangle(s):
        if s.bit_count()==0: return 3
        if s.bit_count()==1: return 2
        return 1
    p=normalize([Q(2)**Ktriangle(s)*Q(2)**s.bit_count()*Q(3)**I[0][s] for s in states])
    violations=[cov(p,[int(s in U) for s in states],I[0]) +
                cov(p,[int(s in U) for s in states],[(s&1) for s in states]) for U in upsets(3)]
    assert max(violations)>0
    print("PASS: false covariance constant refuted; exact violation",max(violations))

    # Independent reset channel on each replica multiplies h by r^2.
    for q in (2,3,4):
        for r in (Q(1,7),Q(1,2),Q(1)):
            for a,b in product(range(q),repeat=2):
                T=lambda x,y:r*(x==y)+(1-r)/q
                h=sum(T(a,u)*T(b,v)*(q*(u==v)-1) for u,v in product(range(q),repeat=2))
                assert h == r*r*(q*(a==b)-1)
    print("PASS: independent output-reset scaling")

    # Hidden-phase counterexample: exact induced pair and field ratios.
    A={2:Q(54),0:Q(51),-2:Q(201,4)}
    assert A[2]*A[-2]/A[0]**2==Q(603,578)
    assert A[2]/A[-2]==Q(72,67)
    assert Q(104)*Q(401,4)/Q(101)**2==Q(10426,10201)
    assert Q(45*225,10201)<1
    assert 603**45>6*578**45
    assert 3**2>8
    assert Q(512,513)/(2*(1-Q(512,513)))==256
    assert 16>3+2*Q(3,2)  # sqrt(2)<3/2 implies e^(4 Kc)<6<16.
    print("PASS: both rational counterexample certificates (including the dimer contraction bound)")
    # Corrected coefficient is eight times smaller than the old coefficient.
    assert Q(4,1)/Q(1,2)==8

    # Exact Dobrushin row: binary CA F(X)_i=1{X_i=1,X_{i+1}=0}.
    # A hidden coordinate is the pair (X_i,X'_i); all factors touching 0
    # are centered at -1 and 0. Enumerate every external pair assignment,
    # every retained-factor subset, and every visible conditioning.
    alphabet=list(product((0,1),repeat=2))
    epsilon=Q(1,1800)  # exactly 1/[100*q*(m+1)^2], q=m=2
    def factor(vals,c):
        y=int(vals[c][0]==1 and vals[c+1][0]==0)
        yp=int(vals[c][1]==1 and vals[c+1][1]==0)
        return 1+epsilon**2*(2*(y==yp)-1)
    def conditional(ext,retained,spins=None,p=Q(2,3)):
        weights=[]
        for z in alphabet:
            vals=dict(ext);vals[0]=z
            weight=Q(1)
            for c in retained:
                wc=factor(vals,c)
                weight*=wc if spins is None else p*(spins[c]==spins[c+1])+(1-p)*wc
            weights.append(weight)
        return normalize(weights)
    rowmax=Q(0); configurations=0
    for retained in subsets((-1,0)):
        for spins in [None]+[dict(zip((-1,0,1),v)) for v in product((-1,1),repeat=3)]:
            for pe in (Q(2,3),Q(1,2)):
                row=Q(0)
                for j in (-1,1):
                    influence=Q(0)
                    other=-j
                    for other_value in alphabet:
                        laws=[conditional({other:other_value,j:v},retained,spins,pe) for v in alphabet]
                        for a,b in combinations(laws,2):
                            influence=max(influence,sum(abs(x-y) for x,y in zip(a,b))/2)
                    row+=influence
                rowmax=max(rowmax,row);configurations+=1
                # ell_w <= 2*q*epsilon^2; sum_j n_0j = m(m-1)=2.
                assert row <= 2*epsilon**2*2 < 1
    assert rowmax>0
    print("PASS: real exact Dobrushin row sums;",configurations,
          "retention/visible/parameter cases; max =",rowmax,
          "; rigorous bound =",4*epsilon**2)

    # 2x2 vertex box: four-cycle with two horizontal and two vertical edges.
    # The two horizontal centers are adjacent in the vertical CA direction.
    edges=((0,1),(2,3),(0,2),(1,3))
    def clusters(mask):
        parent=list(range(4))
        def find(x):
            while parent[x]!=x: x=parent[x]
            return x
        for e,(u,v) in enumerate(edges):
            if mask>>e&1: parent[find(u)]=find(v)
        return len({find(v) for v in range(4)})
    states4=list(range(16))
    assert clusters(15)==clusters(7)==1
    assert clusters(0)==4
    reward=[int((s&3)==0) for s in states4]
    base4=[Q(2)**clusters(s)*Q(2)**((s&3).bit_count()) for s in states4]
    # All-open cycle has an extra cluster weight relative to tree product.
    assert base4[15]/base4[7]==1
    target4=normalize([b*W_direct([i for i in (0,1) if not(s>>i&1)],
                         4,(0,1),selector,eps) for s,b in zip(states4,base4)])
    comp4=normalize([b*t**(3*reward[s]) for s,b in zip(states4,base4)])
    shifted4=normalize([b*t**(-(s&1)) for s,b in zip(states4,base4)])
    for a,b in product(states4,repeat=2):
        assert comp4[a|b]*comp4[a&b]>=comp4[a]*comp4[b]
    nU=0
    for U in upsets(4):
        f=[int(s in U) for s in states4]
        assert sum(target4[s] for s in U)<=sum(comp4[s] for s in U)
        assert sum(comp4[s] for s in U)<=sum(shifted4[s] for s in U)
        assert cov(comp4,f,reward)<=-Q(1,3)*cov(comp4,f,[s&1 for s in states4])
        nU+=1
    assert nU==168
    print("PASS: 2x2 cycle cluster-count FKG, both dominations and anchor covariance on all 168 upsets")

    # Exact binary non-attractiveness certificate used in the L+R discussion.
    binary=lambda a:int(a[0]==1 and a[1]==0)
    assert collision((0,),2,(0,1),binary)==Q(1,4)
    assert collision((0,1),2,(0,1),binary)==0
    micro=Q(1,7)
    assert W_direct((0,1),2,(0,1),binary,micro)-W_direct((0,),2,(0,1),binary,micro)**2==-micro**4/16
    print("PASS: L+R attractiveness counterexample -t^2/16, t=epsilon^2")

    # Alphabet reduction: exhaustive periodic finite simulation of two residue
    # classes. This checks the decoder identity, not infinite-shift surjectivity.
    decode=lambda a,b:min(a+2*b,2)
    for u in product((0,1),repeat=6):
        backgrounds=[[decode(u[(r+2*n)%6],u[(r+2*n+1)%6]) for n in range(3)] for r in range(2)]
        for v in product((0,1),repeat=6):
            output=[v[x] ^ (v[(x+2)%6] if decode(u[x],u[(x+1)%6])==1 else 0) for x in range(6)]
            for r in range(2):
                signals=[v[r+2*n] for n in range(3)]
                original=[signals[n] ^ (signals[(n+1)%3] if backgrounds[r][n]==1 else 0) for n in range(3)]
                assert output[r::2]==original
    assert 2*4**4==512
    print("PASS: exhaustive sliding-decoder/residue identity; physical dimension 512")
    # Finite diagonal KMS matrix-unit identity, including degenerate energies.
    # At beta=1 use rational Gibbs weights and alpha_i(E_kl)=w_k/w_l E_kl.
    weights=[Q(1),Q(1),Q(2),Q(3)]
    norm=sum(weights)
    for i,j,k,l in product(range(4),repeat=4):
        lhs=weights[i]/norm*weights[k]/weights[l] if j==k and l==i else Q(0)
        rhs=weights[k]/norm if l==i and j==k else Q(0)
        assert lhs==rhs
    print("PASS: 256 finite Gibbs trace algebra sanity identities; not a test of the infinite-volume KMS correspondence")
    print("All exact finite checks passed.")


if __name__ == "__main__":
    main()
