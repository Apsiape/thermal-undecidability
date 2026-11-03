"""Exact rational certificate for Q=1681; no floating point or imported checker."""
from fractions import Fraction as F
from math import isqrt
v=41; a=F(23,1000)
scale=10**24; z=isqrt((v*v-4)*scale**2)
Elo=(F(v)+F(z,scale))/2; Ehi=(F(v)+F(z+1,scale))/2
# c > log(Elo/4) + b, the first two alternating correction terms.
b=4/(Ehi**2+1)-2/(Elo**4+1)
assert b>0
# r=exp(a-c) < (4/Elo)*exp(a-b). Bound exp by its rational Taylor sum and tail.
x=a-b
assert 0<x<1
term=F(1); total=term
for n in range(1,41):
    term*=x/n;total+=term
next_term=term*x/41
exp_upper=total+next_term/(1-x/42)
r=4/Elo*exp_upper
k=8*r/(1-r)**2+F(1,64)
assert 0<r<1 and k<F(999092,1000000)<1
assert 2/(1-k)<2203
assert v*v==1681 and v*v*4**4==430336
print('Q=1681; local states=430336; mass=23/1000; kappa<999092/1000000; covariance prefactor<2203.')
