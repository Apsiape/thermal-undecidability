"""Exact q=9 finite checks; Fraction and integer maximum flow, no float tolerance.

Independent spin/bond wired magnetization sums and two-orientation k=2 anchor
comparison on all configurations of a 3x2 grid. Domination is certified for ALL
increasing events by an integer-capacity Strassen coupling. Analytic interpolation
is also checked exactly at rational points along a nonconstant-odds path.
"""
from fractions import Fraction as F
from itertools import product
from math import lcm
import networkx as nx
import collision_checks as cc

Q=9

def roots(n,edges,mask,wired=()):
 p=list(range(n))
 def find(a):
  while p[a]!=a:
   p[a]=p[p[a]]; a=p[a]
  return a
 def join(a,b): p[find(a)]=find(b)
 for a in wired[1:]: join(wired[0],a)
 for j,(a,b) in enumerate(edges):
  if mask>>j&1: join(a,b)
 return [find(a) for a in range(n)]

def colour_boundary():
 # Four free vertices and a fixed colour-1 ghost, including parallel boundary edges.
 edges=[(0,1),(0,2),(1,3),(2,3),(0,4),(0,4),(1,4),(2,4),(3,4),(3,4)]
 Z=N=0
 for s in product(range(Q),repeat=4):
  spins=s+(0,); w=1
  for a,b in edges: w*=1+3*(spins[a]==spins[b])
  Z+=w; N+=w*(s[0]==0)
 den=num=0
 for mask in range(1<<len(edges)):
  r=roots(5,edges,mask); k=len(set(r[:4])-{r[4]})
  w=Q**k*3**mask.bit_count(); den+=w
  num+=w*(r[0]==r[4])
 assert Z==den
 assert (Q*F(N,Z)-1)/(Q-1)==F(num,den)
 print('PASS exact wired magnetization:',F(num,den),'Z =',Z,flush=True)

def integer_weights(w):
 d=lcm(*(v.denominator for v in w))
 return [int(v*d) for v in w]

def dominate(lo,hi):
 # Exact monotone coupling existence <=> every increasing-event inequality.
 a=integer_weights(lo); b=integer_weights(hi); A=sum(a); B=sum(b)
 total=A*B; G=nx.DiGraph(); source='s'; sink='t'; full=len(a)-1
 for x in range(len(a)):
  G.add_edge(source,('a',x),capacity=a[x]*B)
  G.add_edge(('b',x),sink,capacity=b[x]*A)
  remaining=full^x; sub=remaining
  while True:
   G.add_edge(('a',x),('b',x|sub),capacity=total+1)
   if sub==0: break
   sub=(sub-1)&remaining
 value,_=nx.maximum_flow(G,source,sink,flow_func=nx.algorithms.flow.preflow_push)
 assert value==total, 'Exact increasing-event domination failed'

def two_layer():
 V=[(x,y) for y in range(2) for x in range(3)]; vid={v:i for i,v in enumerate(V)}
 edges=[]; centers=[]; ors=[]
 for x,y in V:
  for o,(dx,dy) in [('H',(1,0)),('V',(0,1))]:
   if (x+dx,y+dy) in vid:
    edges.append((vid[x,y],vid[x+dx,y+dy])); centers.append((x,y)); ors.append(o)
 n=len(edges); assert n==7
 P=[(0,0),(1,0)]; k=2; kap=F(1,4); lam=F(1,2)
 ca=cc.make_ca(2,[(0,0),(1,0),(0,1)],lambda v: int(sum(v)>=2))
 cP=cc.c_T(ca,P); assert cP>0 and cc.c_T(ca,[P[0]])==0
 aP=lam**k*cP/(1+lam)**len(cc.D_of(P,ca['N']))
 # Use a slightly smaller valid reward to make the entire interpolation rational:
 # t^8 <= 1+aP; exp(g)=t^4, exp(-kap*g)=1/t.
 t=F(100001,100000); reward=t**4; assert t**8<=1+aP
 ts=[]; anchors=[]
 for o in 'HV':
  index={c:j for j,c in enumerate(centers) if ors[j]==o}
  for x,y in V:
   loc=[index.get((x+dx,y+dy)) for dx,dy in P]
   if all(j is not None for j in loc): ts.append(loc); anchors.append(loc[0])
 assert len(set(anchors))==len(anchors) and len(ts)==4
 assert {ors[a] for a in anchors}=={'H','V'}
 # Enumerate actual oriented edges and retained translates in a 9x9 vertex box.
 box={(x,y) for x in range(9) for y in range(9)}
 oriented={o:{(x,y) for x,y in box if (x+dx,y+dy) in box}
           for o,(dx,dy) in [('H',(1,0)),('V',(0,1))]}
 covered={}
 for o,index in oriented.items():
  retained=[tuple((x+dx,y+dy) for dx,dy in P) for x,y in box
            if all((x+dx,y+dy) in index for dx,dy in P)]
  actual_anchors={loc[0] for loc in retained}
  interior={(x,y) for x,y in index if 1<=x<=6 and 1<=y<=6}
  assert len(interior)==36 and interior<=actual_anchors
  covered[o]=len(interior)
 assert set(covered)=={'H','V'}
 cache={}
 def W(C):
  key=tuple(sorted(C))
  if key not in cache: cache[key]=cc.W_brute(ca,key,lam)
  return cache[key]
 I=[[int(all(not(mask>>j&1) for j in loc)) for loc in ts] for mask in range(1<<n)]
 for wired in [(),(0,2,3,5)]:
  base=[]; target=[]
  for mask in range(1<<n):
   r=roots(len(V),edges,mask,wired); K=len(set(r))-(1 if wired else 0)
   b=F(Q**K*3**mask.bit_count()); base.append(b)
   target.append(b*W([c for j,c in enumerate(centers) if ors[j]=='H' and not(mask>>j&1)])*W([c for j,c in enumerate(centers) if ors[j]=='V' and not(mask>>j&1)]))
  nu=[b*reward**sum(it) for b,it in zip(base,I)]
  shifted=[b/t**sum(mask>>a&1 for a in anchors) for mask,b in enumerate(base)]
  dominate(target,nu); dominate(nu,shifted)
  # Exact conditional closure bound and closure coefficient certificate.
  # At rational z between 1,t, exp(s)=z^4 and odds=3*z/t on anchors.
  for z in [F(1),(1+t)/2,t]:
   wt=[b*(z/t)**sum(mask>>a&1 for a in anchors)*z**(4*sum(I[mask])) for mask,b in enumerate(base)]
   for mask in range(1<<n):
    for e in range(n):
     if mask>>e&1: continue
     assert wt[mask|1<<e]<=3*wt[mask]
   for j,a in enumerate(anchors):
    den=sum(w for mask,w in enumerate(wt) if not(mask>>a&1))
    num=sum(w*I[mask][j] for mask,w in enumerate(wt))
    assert num/den>=kap
  print('PASS exact BOTH-layer anchor chain (all increasing events),', 'wired' if wired else 'free', 'k=2, kappa=1/4, translates=4',flush=True)
 print('PASS rational-path closure/anchor bounds and actual interior-anchor coverage: 36 H + 36 V edges in a 6x6 interior core of a 9x9 vertex box',flush=True)

if __name__=='__main__':
 colour_boundary(); two_layer(); print('ALL EXACT q=9 CHECKS PASSED',flush=True)