#!/usr/bin/env python3
from itertools import permutations
from flint import nmod_poly,fq_default_ctx,fq_default_poly_ctx
from math import lcm
def peel(G,D):
 while G.degree()>0:
  x=G.gcd(D)
  if x.degree()<=0:break
  G,r=divmod(G,x);assert r.is_zero()
 return G
for p in (13,17,103,131,7793):
 ds=lcm(*(f.degree() for P in ([3,0,-30,0,35],[-1,-2,1]) for f,e in nmod_poly(P,p).factor()[1]))
 F=fq_default_ctx(p,ds,'w');R=fq_default_poly_ctx(F);U=R.gen();O=F.one();Z=F.zero()
 gs=[x for x,e in (35*U**4-30*U**2+3).roots()]
 ks=[x for x,e in (U**2-2*U-1).roots()]
 val=lambda P,c:sum((r*c**i for i,r in enumerate(P)),R.zero())
 J=lambda P,c:sum((r*c**(i+1)/(i+1) for i,r in enumerate(P)),R.zero())
 N0=lambda P,c:sum((r*c**(i+2)/(i+2) for i,r in enumerate(P)),R.zero())
 nr=ct=0;outs=[]
 for y,z in permutations(gs,2):
  for v in ks:
   for ph,b in (('arith',1+2*v),('star',3-v)):
    if b*(1+y)!=(1+v)*(1+z):continue
    ga=(1+y)/(2*(1+v));dd=1-ga;x4=dd/ga
    nr+=1
    for aa in gs:
     if aa in (y,z):continue
     a=(1-aa)/(2*ga)
     k=1+2*U-U*U
     for mode in ('S','A'):
      if mode=='S':
       H=R.one();j=R.zero();Rgn=U*(U-1)*(U-2)*k
       xs=[R.one(),1+U,3-U]
      else:
       H=-2+U+4*U**2-U**3;j=3*U-2
       Rgn=U*k*H*j*(H*(1+4*U-4*U**2)+4*U**2*j)
       xs=[R.one(),1+U,1+2*U]
      P=[j*(1+U)-H,2*H-j*(2+U),-H/2+j]
      assert 2*val(P,xs[0])==H
      assert 2*val(P,xs[1])==H*k
      if mode=='S':assert 2*val(P,xs[2])==H*k
      else:assert 2*val(P,xs[2])==H*(1+4*U-4*U**2)+4*U**2*j
      r=[R.one()]
      for x in xs:r=[-x*r[0]]+[r[i-1]-x*r[i] for i in range(1,len(r))]+[r[-1]]
      DD=val(P,a)-J(P,a);NN=a*val(P,a)-N0(P,a)
      rho=val(P,x4)-J(P,x4)
      sig=-3*H*(x4-1)+3*k*P[1]+(4*k+2*(k+1)*(x4-1))*P[2]
      B=J(r,a)-val(r,a)
      E=x4*DD-NN
      G=B*(3*k*H*rho-sig*val(P,x4))-DD*val(r,x4)*sig
      C=E.gcd(G);assert not C.is_zero()
      S=peel(C,Rgn)
      ct+=1
      if S.degree()>0:outs.append((p,ph,mode,a,E,G,C,S))
 assert not outs and nr==(2 if p in (13,131) else 1) and ct==4*nr
 print(p,nr,ct,flush=True)
