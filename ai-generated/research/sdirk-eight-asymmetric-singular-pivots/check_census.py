#!/usr/bin/env python3
from flint import nmod_poly,fq_default_ctx,fq_default_poly_ctx
from math import lcm,isqrt
from itertools import permutations
J=[-36,-360,-1212,-480,9639,25230,24640,9450,1225]
def field(p,d):
 F=fq_default_ctx(p,d,'w')
 return F,fq_default_poly_ctx(F)
def ratio(q):
 D=175*q**4+588*q**3+279*q*q+72*q+6
 N=(35*q*q+30*q+3)*(35*q**4+140*q**3+131*q*q+40*q+6)
 if D==0:return None
 return N/(5*D)
def cubic(R,k,q):
 x=k*k
 T=-105*x*q-15*x+175*q**3+255*q*q+105*q+9
 p0=3*k*(-21*x+35*q*q+42*q+15)/7
 p1=-3*(-175*x*q-21*x+245*q**3+385*q*q+171*q+15)/7
 p2=-3*k*(-5*x+15*q*q+10*q+3)
 if T==0 or p0==0:return None
 P=R([p0,p1,p2,T])
 if P.gcd(P.derivative()).degree()!=0:return None
 if P.gcd(R([q,k,1])).degree()!=0:return None
 return P
def candidate(p,qf,xv=None):
 c=list(map(int,qf.coeffs()))
 d=qf.degree()
 def roots(d):
  F,R=field(p,d);X=R.gen()
  q=R(c).roots()[0][0]
  x=F(xv) if xv is not None else ratio(q)
  if x is None or x==0:return F,R,q,[]
  return F,R,q,[k for k,e in (X*X-x).roots()]
 F,R,q,ks=roots(d)
 if not ks:
  x=F(xv) if xv is not None else ratio(q)
  if x is None or x==0:return
  d*=2
  F,R,q,ks=roots(d)
 assert len(ks)==2
 dY=lcm(*(f.degree() for k in ks if (v:=cubic(R,k,q)) is not None for f,e in v.factor()[1]))
 if dY>1:
  d*=dY
  F,R,q,ks=roots(d)
 print('p,fiber,total splitting degree',p,qf,d,flush=True)
 etc=[]
 for k in ks:
  P=cubic(R,k,q)
  if P is None:continue
  ys=[y for y,e in P.roots()]
  assert len(ys)==3
  r=lambda z:z*z+k*z+q
  j=lambda z:(z**3+1)/6+k*(z*z-1)/4+q*(z+1)/2
  I=q+F.one()/3
  for a,b in permutations(ys,2):
   g=j(a)/r(a)
   if g==0 or I-j(b)!=g*r(b):continue
   def phase(k,a):
    r=lambda y:y*y+k*y+q
    R=r(2*g-1);D=R+4*g*g;U=2*R-2*g*(4*g-2+k)
    if R==0 or D==0:return []
    u=U/D
    if u==0 or 1+2*u-u*u==0:return []
    H=-2+u+4*u*u-u**3
    if H==0:return []
    t=2*u*(3*u-2)/H
    if t==0:return []
    Q=1+4*u-4*u*u+2*u*t;y3=2*g*(1+2*u)-1
    if Q==0:return [('Z',u)] if y3==a else []
    return [('A',u)] if r(y3)==R*Q else []
   A=phase(k,a);B=phase(-k,-b)
   etc.append((k,q,g,a,b,A,B))
   print('actual anchors',etc[-1],flush=True)
 assert not etc
 return etc
for p in (11,59,6359):
 assert all(p%d for d in range(2,isqrt(p)+1))
 for qf,e in nmod_poly(J,p).factor()[1]:
  candidate(p,qf)
for p,q,x in [(59,9,50),(6359,2219,3726)]:
 candidate(p,nmod_poly([-q,1],p),x)
