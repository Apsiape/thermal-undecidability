# Independent exact recomputation via rational inequalities and integral log bounds.
from fractions import Fraction as F
from math import isqrt

def log_bounds(y):
    # Integrate 1/x after a Mobius change: independent implementation and truncation.
    n=0
    while y>F(3,2): y/=F(3,2); n+=1
    def integrate(z):
        q=(z-1)/(z+1); power=q; total=F(0)
        for odd in range(1,401,2):
            total+=2*power/odd; power*=q*q
        remainder=2*abs(power)/(401*(1-q*q))
        return total-remainder,total+remainder
    lo,hi=integrate(y); l,h=integrate(F(3,2))
    return lo+n*l,hi+n*h

def mass_bounds(v):
    M=10**30; b=isqrt((v*v-4)*M*M)
    low=(F(v)+F(b,M))/2; high=(F(v)+F(b+1,M))/2
    L=log_bounds(low/4)[0];H=log_bounds(high/4)[1]
    # Two-term lower correction, three-term upper correction: alternating theorem.
    L+=4/(high**2+1)-2/(low**4+1)
    H+=4/(low**2+1)-2/(high**4+1)+F(4,3)/(low**6+1)
    return L,H

assert 257**2-4>255**2
assert 257**2*256==16908544 and 41**2*256==430336
S=F(4*32,31*31); k=2*S+F(1,64)
assert S==F(128,961) and k==F(17345,61504)
assert k<F(1,3) and 2/(1-k)==F(123008,44159)<3
L,H=mass_bounds(257)
assert F(4162827,10**6)<L<H<F(4162828,10**6)
assert L>log_bounds(F(64))[1]
assert 8*F(2,21)/(1-F(2,21))**2+F(1,64)<1
# A longer alternating certificate for the small c_9 diagnostic.
scale9=10**30; base9=isqrt(5*scale9*scale9)
e9lo=(F(3)+F(base9,scale9))/2; e9hi=(F(3)+F(base9+1,scale9))/2
c9L=log_bounds(e9lo/4)[0];c9H=log_bounds(e9hi/4)[1]
for j9 in range(1,21):
    l9=4/(j9*(e9hi**(2*j9)+1));h9=4/(j9*(e9lo**(2*j9)+1))
    if j9%2:c9L+=l9;c9H+=h9
    else:c9L-=h9;c9H-=l9
c9H+=4/(21*(e9lo**42+1))
assert F(4745,100000)<c9L<c9H<F(4746,100000)
assert 1-F(1,404)/F(4,101)==F(15,16)
# All parameter values: t <= 1/[10000*s^2*(m+1)^4] < 1/2.
# log(1+(s-1)t)-log(1-t) <= (s-1)t+t/(1-t) <= 2st.
# Then rho <= st*m(m-1) < 1; the second epsilon term bounds the hidden budget.
for alphabet in range(2,17):
    for size in range(1,41):
        for radius in range(1,61):
            K=size+2
            ep=min(F(1,100*alphabet*(size+1)**2),F(1,16*alphabet*K*2**radius))
            t_exact=ep*ep
            log_upper=(alphabet-1)*t_exact+t_exact/(1-t_exact)
            assert log_upper<=2*alphabet*t_exact
            rho=log_upper*size*(size-1)/2
            assert rho<1
            ph=alphabet*t_exact/(1+(alphabet-1)*t_exact)
            budget=4*ph*K*(K-1)*2**radius
            envelope=F(K-1,64*alphabet*K*2**radius)
            assert budget<=envelope<=F(1,64)
            assert 0<t_exact<1 and ph<=alphabet*t_exact
print('Independent exact certificates and 36,000-case rational parameter grid passed.')

from fractions import Fraction as Fr
from mpmath import mp, mpf, log
mp.dps = 80
bad = 0; worst = mpf(0)
for s in range(2, 17):
    for m in range(1, 41):
        kst = m + 2
        for R in range(1, 61):
            eps = min(Fr(1, 100*s*(m+1)**2), Fr(1, 16*s*kst*2**R))
            t = mpf(eps.numerator)**2/mpf(eps.denominator)**2
            lw = log((1+(s-1)*t)/(1-t))
            ratio = lw/(2*s*t)
            worst = max(worst, ratio)
            if ratio > 1: bad += 1
assert bad==0
print("violations of l_w <= 2 s t (80-digit arithmetic):", bad, " max l_w/(2st) =", float(worst))
# a-choices at smaller Q: largest a with 2*S_Q(a) + 1/64 < 1 using tau <= e^{-c||x||}
from mpmath import acosh, exp, nsum, inf
def cQ(sq):
    lam = acosh(mpf(sq)/2)
    return lam - log(4) + 4*nsum(lambda j: (-1)**(int(j)+1)/(j*(exp(2*j*lam)+1)), [1, inf])
for sq in [40, 41, 45, 50, 64, 100, 257]:
    c = cQ(sq)
    # 2*4r/(1-r)^2 <= 1 - 1/64  -> solve for r
    lo, hi = mpf(0), mpf('0.2')
    for _ in range(200):
        mid = (lo+hi)/2
        if 8*mid/(1-mid)**2 <= 1 - mpf(1)/64: lo = mid
        else: hi = mid
    a = c + log(lo)
    print(f"sqrt(Q)={sq} Q={sq*sq}: c_Q={float(c):.5f}, max admissible mass a = {float(a):.5f}")

# Independent exact check of the smaller-colour constants stated in the remark.
low41,high41=mass_bounds(41)
low41=F((low41*10**12).numerator//(low41*10**12).denominator,10**12)
z41=low41-F(23,1000)
assert 0<z41<3
term41=F(1); sum41=term41
for i41 in range(1,80):
    term41*=z41/i41; sum41+=term41
r41=1/sum41
k41=8*r41/(1-r41)**2+F(1,64)
assert k41<F(999092,1000000) and 2/(1-k41)<2203
assert 1681*4**4==430336
print('Independent smaller-Q rational certificate passed: mass 23/1000, kappa<0.999092, prefactor<2203.')
