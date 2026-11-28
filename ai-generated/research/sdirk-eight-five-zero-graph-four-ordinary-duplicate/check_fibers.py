#!/usr/bin/env python3
from flint import fq_default_ctx,fq_default_poly_ctx,nmod_poly
from itertools import permutations
from math import lcm,isqrt
def peel(f,g):
 while f.degree()>0:
  h=f.gcd(g)
  if h.degree()<1:break
  f,r=divmod(f,h);assert r.is_zero()
 return f
for p in (37,269,379,397,487,69877):
 assert all(p%d for d in range(2,isqrt(p)+1))
 deg=lcm(*(f.degree() for f,m in nmod_poly([1,-20,90,-140,70],p).factor()[1]))
 F=fq_default_ctx(p,deg,'a');R=fq_default_poly_ctx(F);U=R.gen();O=F.one();Z=F.zero()
 gs=[x for x,k in (70*U**4-140*U**3+90*U**2-20*U+1).roots()]
 assert len(gs)==4 and all(x!=0 for x in gs)
 I0=lambda P,x:sum((c*x**j for j,c in enumerate(P)),R.zero())
 J=lambda P,k,x:sum((c*x**(j+k+1)/(j+k+1) for j,c in enumerate(P)),R.zero())
 total=0;both_live=one_live=0
 for x,y in permutations(gs,2):
  v=(y-x)/x
  ghost=None
  if p in (37,269,379):
   z=4*x-y
   if z not in gs or z in (x,y):continue
   late=[z,y,x]
   missed=next(t for t in gs if t not in late)
   triples=[]
   for a in gs:
    if a==missed:triples.append((a,z,y))
    else:triples.append((a,missed,next(t for t in late if t!=a)))
  else:
   if v**3-4*v*v-v+2!=0:continue
   z=2*y-x
   assert z not in gs
   ghost=(O-z)/x
   mid=[t for t in gs if t not in (x,y)]
   triples=[(a,b,c) for a in (x,y) for b,c in permutations(mid)]
   triples.extend((a,next(t for t in mid if t!=a),y) for a in mid)
  for a,b,c in triples:
   assert a!=b and a!=c and b!=c
   in_rear=a in (late if ghost is None else [x,y])
   order_count=2 if ghost is not None and not in_rear else 1
   a,b=[(O-t)/x for t in (a,b)]
   for ph in ('S','A'):
    total+=1
    both_live+=order_count
    one_live+=order_count*(1 if in_rear else 2)
    h=R.one() if ph=='S' else -2+U+4*U*U-U**3
    j=R.zero() if ph=='S' else 3*U-2
    k=1+2*U-U*U
    P=[-h+j*(1+U),2*h-j*(2+U),-h/2+j]
    assert 2*I0(P,O)==h and 2*I0(P,1+U)==k*h
    guard=h*U*k*I0(P,a)
    if ph=='S':
     assert 2*I0(P,3-U)==h*k
     guard*=(U-1)*(U-2)
    else:
     assert 2*I0(P,1+2*U)==h*(1+4*U-4*U*U)+4*U*U*j
     guard*=j*(h*(1+4*U-4*U*U)+4*U*U*j)
    if ghost is not None:guard*=I0(P,ghost)
    assert not guard.is_zero()
    ps=[-a*P[0],P[0]-a*P[1],P[1]-a*P[2],P[2]]
    E1=J(P,0,a)-I0(P,a)
    E2=J(ps,0,b)-I0(ps,b)
    G=E1.gcd(E2)
    assert not G.is_zero()
    G=peel(G,guard)
    assert G.degree()==0
 assert total==(16 if p in (37,269,379) else 12)
 assert (both_live,one_live)==(16,20 if p in (37,269,379) else 24)
 print(p,'complete duplicate/phase charts',total,'both/one live patterns',both_live,one_live,'guarded front gcds constant')
