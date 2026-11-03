from fractions import Fraction as F
from math import isqrt

def log_interval(x, terms=120):
    # Positive rational x: range reduction then the atanh series with exact tail.
    assert x > 0
    power=0
    while x>=2: x/=2; power+=1
    while x<1: x*=2; power-=1
    def base(y):
        z=(y-1)/(y+1)
        lower=2*sum((z**(2*j+1)/F(2*j+1) for j in range(terms)),F(0))
        tail=2*z**(2*terms+1)/(F(2*terms+1)*(1-z*z))
        return lower,lower+tail
    lo,hi=base(x); l2,h2=base(F(2))
    return (lo+power*l2,hi+power*h2) if power>=0 else (lo+power*h2,hi+power*l2)

def mass_interval(v, terms=60):
    scale=10**35
    z=isqrt((v*v-4)*scale*scale)
    E0=F(v,2)+F(z,2*scale); E1=F(v,2)+F(z+1,2*scale)
    lo=log_interval(E0/4)[0]; hi=log_interval(E1/4)[1]
    # Each positive summand decreases in E. Use an even alternating truncation.
    for j in range(1,terms+1):
        q0=4/(F(j)*(E1**(2*j)+1));q1=4/(F(j)*(E0**(2*j)+1))
        if j%2: lo+=q0; hi+=q1
        else: lo-=q1; hi-=q0
    hi+=4/(F(terms+1)*(E0**(2*(terms+1))+1))
    return lo,hi

assert 257**2==66049 and 66049*4**4==16908544
assert 66045>65025 and 257**2-4==66045 and 255**2==65025
S_exact=4*F(1,32)/(1-F(1,32))**2
assert S_exact==F(128,961)
k_exact=2*S_exact+F(1,64)
assert k_exact==F(17345,61504)<F(1,3)
assert 2/(1-k_exact)==F(123008,44159)<3
assert 8*F(2,21)/(1-F(2,21))**2+F(1,64)<1
ml,mh=mass_interval(257)
assert F(41628271447,10**10)<ml<mh<F(41628271448,10**10)
assert ml>log_interval(F(64))[1]
c9lo,c9hi=mass_interval(3)
assert F(4745,100000)<c9lo<c9hi<F(4746,100000)
assert F(1,404)/F(4,101)==F(1,16)
print('Exact rational certificates: Q, dimensions, masses, susceptibility, kappa, prefactor, activation passed.')

# Portable review recomputation; exact assertions precede numerical diagnostics.
from fractions import Fraction as Fr
import math
from mpmath import mp, mpf, acosh, log, tanh, sinh, pi, sqrt, nsum, inf, exp

mp.dps = 50

def cQ_formula(sq):  # sq = sqrt(Q)
    lam = acosh(mpf(sq)/2)
    # absolutely convergent rewrite: lam - log4 + 4 sum (-1)^(j+1)/(j(e^{2 j lam}+1))
    s = nsum(lambda j: (-1)**(int(j)+1)/(j*(exp(2*j*lam)+1)), [1, inf])
    return lam, lam - log(4) + 4*s

def cQ_direct(sq, K=200000):
    lam = acosh(mpf(sq)/2)
    # direct (conditionally convergent) partial sums, averaged over two consecutive to accelerate
    tot = mpf(0); prev = None
    for k in range(1, K+1):
        tot += (-1)**k/mpf(k)*tanh(k*lam)
    tot2 = tot + (-1)**(K+1)/mpf(K+1)*tanh((K+1)*lam)
    return lam + 2*(tot+tot2)/2

def q4_series(sq):
    lam = acosh(mpf(sq)/2)
    return nsum(lambda k: 4/((2*k+1)*sinh(pi**2*(2*k+1)/(2*lam))), [0, inf])

print("== transcription check of DC-GHMT (1.2)/(1.3): two expressions should agree ==")
for q in [5, 6, 9, 16, 25]:
    sq = sqrt(q)
    lam, c = cQ_formula(sq)
    assert abs(c-q4_series(sq))<mpf("1e-40")
    print(f"q={q}: lam={float(lam):.10f}  formula={float(c):.12e}  q->4 series={float(q4_series(sq)):.12e}  direct={float(cQ_direct(sq,20000)):.12e}")

print("\n== sqrt(Q) = 257 ==")
lam, c = cQ_formula(257)
print("lambda =", lam)
print("c_Q    =", c)
print("log 64 =", log(64), " margin c_Q - log64 =", c - log(64))
print("lambda - log4 =", lam - log(4))
# exact check e^lambda > 256 : (257 + sqrt(66045))/2 > 256 <=> sqrt(66045) > 255 <=> 66045 > 65025
print("exact: 257^2-4 =", 257**2-4, "> 255^2 =", 255**2, ":", 257**2-4 > 255**2)

print("\n== S_Q(log 2) bound ==")
# sum_{n>=1} 4n 32^{-n} = 4*(1/32)/(1-1/32)^2
S = Fr(4)*Fr(1,32)/(1-Fr(1,32))**2
assert S==Fr(128,961)
print("sum 4n 32^-n =", S, " == 128/961 ?", S == Fr(128,961))
# also with the true c_Q (not just log 64)
Strue = nsum(lambda n: 4*n*exp((log(2)-c)*n), [1, inf])
print("with exact c_Q: S <=", Strue)

kappa = 2*Fr(128,961) + Fr(1,64)
assert kappa==Fr(17345,61504)<Fr(1,3)
print("kappa bound =", kappa, " == 17345/61504 ?", kappa == Fr(17345,61504), " <1/3 ?", kappa < Fr(1,3))
print("2/(1-kappa) =", 2/(1-kappa), "=", float(2/(1-kappa)), " <=3 ?", 2/(1-kappa) <= 3)

print("\n== epsilon bounds (2),(3) and 2 p_h J_N <= 1/64 over a grid ==")
bad = []
worst_hid = Fr(0); worst_dob = 0.0; worst_dob_paper = 0.0
for s in range(2, 17):
    for m in range(1, 41):
        kst = m + 2
        for R in range(1, 61):
            eps = min(Fr(1, 100*s*(m+1)**2), Fr(1, 16*s*kst*2**R))
            t = eps*eps
            ph = Fr(s)*t/(1+(s-1)*t)
            JN = 2*kst*(kst-1)*2**R
            hid = 2*ph*JN
            if hid > Fr(1,64): bad.append(("hid", s, m, R, float(hid)))
            worst_hid = max(worst_hid, hid)
            lw = math.log1p((s-1)*float(t))-math.log1p(-float(t))
            if lw > 2*s*float(t): bad.append(("lw", s, m, R))
            dob = 4*lw*m*(m-1)          # historical 4*l_w screening bound
            dobp = 0.5*lw*m*(m-1)       # paper's (eq:dob)
            worst_dob = max(worst_dob, dob); worst_dob_paper = max(worst_dob_paper, dobp)
            if dob >= 1: bad.append(("dob", s, m, R, dob))
            if t >= 1 or 1 - t <= 0: bad.append(("pos", s, m, R))
assert not bad, bad[:10]
print("violations:", bad[:10], "count", len(bad))
print("max 2 p_h J_N over grid =", float(worst_hid), "(<= 1/64 =", 1/64, ")")
print("max historical 4*l_w screening sum =", worst_dob, "; max paper Dobrushin sum =", worst_dob_paper)

print("\n== smallest perfect square Q for which the same union-bound method gives kappa<1 (hidden term -> 0) ==")
# need 2 * sum 4n r^n < 1 with r = e^{a - c_Q}, a>0 ; i.e. 8r/(1-r)^2 < 1  <=> r < 5 - sqrt(24)
rstar = 5 - sqrt(24)
print("r* =", rstar, " need c_Q >", -log(rstar))
for sq in range(3, 60):
    lam, cq = cQ_formula(sq)
    if cq > -log(rstar):
        # largest admissible a with margin for hidden 1/64: 2*4r/(1-r)^2 <= 1 - 1/64 - tiny
        print("first sqrt(Q) =", sq, " Q =", sq*sq, " c_Q =", float(cq))
        break
for sq in [3, 10, 20, 30, 40, 50, 100, 257]:
    lam, cq = cQ_formula(sq)
    print(f"sqrt(Q)={sq}: c_Q={float(cq):.6f}")
print("\nLocal state count at Q=66049 with 4-letter CA alphabet:", 66049*4**4)

# Independent exact check of the smaller-colour constants stated in the remark.
low41,high41=mass_interval(41)
low41=F((low41*10**12).numerator//(low41*10**12).denominator,10**12)
z41=low41-F(23,1000)
assert 0<z41<3
term41=F(1); sum41=term41
for i41 in range(1,100):
    term41*=z41/i41; sum41+=term41
r41=1/sum41
k41=8*r41/(1-r41)**2+F(1,64)
assert k41<F(999092,1000000) and 2/(1-k41)<2203
assert 1681*4**4==430336
print('Independent smaller-Q rational certificate passed: mass 23/1000, kappa<0.999092, prefactor<2203.')
