#!/usr/bin/env python3
from itertools import permutations
from flint import nmod_poly,fq_default_ctx,fq_default_poly_ctx
from math import lcm
ps=(13,17,103,131,7793)
for p in ps:
 ds=lcm(*(f.degree() for P in ([3,0,-30,0,35],[-1,-2,1]) for f,e in nmod_poly(P,p).factor()[1]))
 F=fq_default_ctx(p,ds,'w');R=fq_default_poly_ctx(F);X=R.gen();O=F.one();Z=F.zero()
 J=lambda P:R([Z]+[a/(j+1) for j,a in enumerate(P.coeffs())])
 gs=[x for x,e in (35*X**4-30*X**2+3).roots()]
 ks=[x for x,e in (X**2-2*X-1).roots()]
 counts=[0,0,0,0,0];survive=[]
 for y,z in permutations(gs,2):
  for v in ks:
   for ph,b in (('arith',1+2*v),('star',3-v)):
    if b*(1+y)!=(1+v)*(1+z):continue
    ga=(1+y)/(2*(1+v));dd=1-ga
    xd=dd/ga;h=xd-1
    for u,w,style in ((h,2-h,'S'),(h,2*h,'A'),(2-h,h,'S'),(h/2,h,'A')):
     k=1+2*u-u*u
     if u==0 or k==0:continue
     if style=='S':
      if u in (O,2*O):continue
      r=Z
     else:
      H=-2+u+4*u*u-u**3
      if H==0 or 3*u==2:continue
      r=2*u*(3*u-2)/H
     xs=[O,1+u,1+w];zs=[O/2,k/2,(1+2*w-w*w+2*r*u)/2]
     if zs[2]==0:continue
     P=R.zero();T=R.one()
     for i,t in enumerate(xs):
      L=R.one();T*=X-t
      for j,s in enumerate(xs):
       if j!=i:L=L*(X-s)/(t-s)
      P+=zs[i]*L
     for aa in gs:
      if aa in (y,z):continue
      a=(1-aa)/(2*ga)
      D=P(a)-J(P)(a);N=a*P(a)-J(P*X)(a)
      counts[0]+=1
      if D==0:
       if N==0:survive.append(('D=N=0',ga,a,u,style))
       else:counts[1]+=1
       continue
      x4=N/D
      l=4*O/3+2*(k+1)*(x4-1)/(3*k)
      c=P.coeffs()+[Z]*3
      s=-(x4-1)/k+c[1]+c[2]*l
      B=J(T)(a)-T(a)
      rho=P(x4)-J(P)(x4)
      G=B*(rho-s*P(x4))-D*T(x4)*s
      if G!=0:counts[2]+=1;continue
      if s==0:
       counts[3]+=1
       if rho==0:survive.append(('s=rho=0',ga,a,u,style))
       continue
      g4=rho/s
      if g4==0 or g4==P(x4):counts[4]+=1;continue
      survive.append(('normal',ga,a,u,style,x4,g4))
 assert not survive and counts==([16,0,16,0,0] if p==131 else [8,0,8,0,0])
 print(p,counts,flush=True)
