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
def check(F,R,U,ps,mode,a,b):
 O=F.one();Z=F.zero()
 val=lambda P,c:sum((r*c**i for i,r in enumerate(P)),R.zero())
 J=lambda P,c:sum((r*c**(i+1)/(i+1) for i,r in enumerate(P)),R.zero())
 IJ=lambda P,c:sum((r*c**(i+2)/(i+2) for i,r in enumerate(P)),R.zero())
 homog=lambda P,m,N,D:sum((r*N**i*D**(m-i) for i,r in enumerate(P)),R.zero())
 k=1+2*U-U*U
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
 D=val(P,a)-J(P,a);N=a*val(P,a)-IJ(P,a)
 C=D.gcd(N)
 assert not C.is_zero()
 C=peel(C,Rgn)
 if C.degree()>0:return ('singular',C)
 if D.is_zero():return None
 rho=[P[0],P[1]-P[0],P[2]-P[1]/2,-P[2]/3]
 sig=-3*H*(N-D)+3*k*P[1]*D+(4*k*D+2*(k+1)*(N-D))*P[2]
 B=J(r,a)-val(r,a)
 G=B*(3*k*H*homog(rho,3,N,D)-sig*homog(P,2,N,D))-homog(r,3,N,D)*sig
 r1=[D*x+B*y for x,y in zip(r,P+[R.zero()])]
 r2=[N*P[0],N*P[1]-D*P[0],N*P[2]-D*P[1],-D*P[2]]
 C=val(r2,a)*(J(r1,b)-val(r1,b))-val(r1,a)*(J(r2,b)-val(r2,b))
 CH=G.gcd(C)
 assert not CH.is_zero()
 E=peel(CH,Rgn*D)
 if E.degree()>0:return ('regular',E)
 return None

for p in (13,17,103,131,7793,397,487,69877):
 ds=lcm(*(f.degree() for P in ([3,0,-30,0,35],[-1,-2,1]) for f,e in nmod_poly(P,p).factor()[1]))
 F=fq_default_ctx(p,ds,'w');R=fq_default_poly_ctx(F);U=R.gen();O=F.one();Z=F.zero()
 gs=[x for x,e in (35*U**4-30*U**2+3).roots()]
 ks=[x for x,e in (U**2-2*U-1).roots()]
 data=[]
 if p in (397,487,69877):
  for y,z in permutations(gs,2):
   g=(1+y)/2;v=(z-y)/(1+y)
   H=-2+v+4*v*v-v**3
   if H==0:data.append((y,z,g))
 else:
  for y,z in permutations(gs,2):
   for v in ks:
    for ph,b in (('arith',1+2*v),('star',3-v)):
     if b*(1+y)==(1+v)*(1+z):
      g=(1+y)/(2*(1+v));data.append((y,z,g))
 cc=0;outs=[]
 for y,z,ga in data:
  for aa,bb in permutations((x for x in gs if x not in (y,z)),2):
   a=(1-aa)/(2*ga); b=(1-bb)/(2*ga)
   for mode in ('S','A'):
    o=check(F,R,U,p,mode,a,b);cc+=1
    if o is not None:outs.append((p,y,z,ga,aa,bb,mode,o))
 assert not outs and len(data)==(2 if p in (13,131) else 1) and cc==4*len(data)
 print(p,len(data),cc,flush=True)
