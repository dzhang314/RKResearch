#!/usr/bin/env python3
from flint import nmod_poly,fq_default_ctx,fq_default_poly_ctx
from itertools import permutations,product,combinations
from math import lcm,isqrt
roots0=[1,-20,90,-140,70]
Q0=[2,3,-12,4]
for p in (37,269,379,397,487,69877):
 assert all(p%d for d in range(2,isqrt(p)+1))
 d=lcm(*(f.degree() for cs in (roots0,Q0) for f,m in nmod_poly(cs,p).factor()[1]))
 F=fq_default_ctx(p,d,'a');R=fq_default_poly_ctx(F);T=R.gen();Z=F.zero();O=F.one()
 gs=[x for x,m in (70*T**4-140*T**3+90*T*T-20*T+1).roots()]
 us=[u for u,m in (4*T**3-12*T*T+3*T+2).roots()]
 assert len(gs)==4 and len(us)==3
 J=lambda P:R([Z]+[c/(i+1) for i,c in enumerate(P.coeffs())])
 counts=[0,0,0,0,0];prod=O
 for x,y in permutations(gs,2): # reflected clocks of physical 10/9
  v=(y-x)/x
  if p in (37,269,379):
   z=4*x-y
   if z not in gs or z in (x,y):continue
   pre=[(O-w,O-z) for w in gs if w not in (x,y,z)]
  else:
   if v**3-4*v*v-v+2!=0:continue
   z=None
   pre=[(O-w,O-j) for w,j in permutations([z0 for z0 in gs if z0 not in (x,y)],2)]
  D=O/x
  I=lambda P:sum((c*D**i/(i+1) for i,c in enumerate(P.coeffs())),Z)
  L=70*T**4-140*D*T**3+90*D**2*T*T-20*D**3*T+D**4
  L3=T**3-3*D*T*T/2+3*D**2*T/5-D**3/20
  for u,(s,zp) in product(us,pre):
   if u==0 or 1+2*u-u*u==0:continue
   a=1+2*u;b=s/x
   assert L(a)!=0
   r0=(T-1)*(T-1-u)
   P0=2*T-1-T*T/2
   v0=(T-a)*P0;v1=(T-a)*r0
   e0=J(v0)(b)-v0(b);e1=J(v1)(b)-v1(b)
   assert e1!=0
   lam=-e0/e1
   r=P0+lam*r0
   if r(a)==0:
    counts[0]+=1;continue
   if z is None and r((O-(2*y-x))/x)==0:
    counts[1]+=1;continue
   if J(r)(a)!=r(a):
    counts[2]+=1;continue
   xs=[a,b,zp/x,(O-y)/x,(O-x)/x]
   assert all(x!=y for x,y in combinations(xs,2))
   c=xs[2]
   def prim(k,x):return J(T**k*r)(x)
   D1=b*b*r(b)+a*a*(prim(0,b)-r(b))-prim(2,b)
   D2=c*c*r(c)+(a+b)*(prim(1,c)-c*r(c))-a*b*(prim(0,c)-r(c))-prim(2,c)
   g=L3(b)*D2-L3(c)*D1
   assert g!=0
   prod*=g
   counts[3]+=1
 assert counts==[0,0,0,6,0]
 assert int(prod)=={37:9,269:148,379:343,397:88,487:336,69877:40048}[p]
 print(p,counts[3],"geometric controls, product of nonzero third-zero gate values",int(prod),flush=True)
