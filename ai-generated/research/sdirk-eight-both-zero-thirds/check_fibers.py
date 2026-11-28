#!/usr/bin/env python3
"""Exact k², free-k, or free-diagonal fibers once the ordered gaps split."""
from flint import nmod_poly,fq_default_ctx,fq_default_poly_ctx
from itertools import permutations
from math import lcm
from prime_certificates import certify
# A, B and P evaluate over a scalar or one polynomial coordinate, with a common denominator D.
def terms(k,q,D):
 x=k*k
 T=-105*x*q-15*x*D+175*q**3+255*q*q*D+105*q*D*D+9*D**3
 p0=3*k*(-21*x+35*q*q+42*q*D+15*D*D)/7
 p1=-3*(-175*x*q-21*x*D+245*q**3+385*q*q*D+171*q*D*D+15*D**3)/7
 p2=-3*k*(-5*x+15*q*q+10*q*D+3*D*D)
 A=-63*x*x*q+21*x*x*D-70*x*q**3-210*x*q*q*D-138*x*q*D*D-30*x*D**3+245*q**5+805*q**4*D+986*q**3*D*D+546*q*q*D**3+129*q*D**4+9*D**5
 B=-525*x*x*q+525*x*x*D-1750*x*q**3-5670*x*q*q*D-3150*x*q*D*D-630*x*D**3+3675*q**5+13825*q**4*D+17970*q**3*D*D+9990*q*q*D**3+2259*q*D**4+153*D**5
 return T,p0,p1,p2,A,B
def clean(ps,G,R):
    if G.is_zero():return R.one()
    out=R.zero()
    for p in ps:out=out.gcd(p)
    assert not out.is_zero()
    while out.degree()>0:
      dd=out.gcd(G)
      if dd.degree()<=0:break
      out,rem=divmod(out,dd)
      assert rem.is_zero()
    return out
def bank(p):
 f=nmod_poly([2,3,-12,4],p)
 fac=f.factor()[1]
 F=fq_default_ctx(p,lcm(*(a.degree() for a,e in fac)),'u')
 R=fq_default_poly_ctx(F)
 W=R.gen()
 Z=[a for a,e in (4*W**3-12*W*W+3*W+2).roots()]
 assert len(Z)==3
 return F,R,W,Z
def general(R,u,v,s,k,q,D):
 T,p0,p1,p2,A,B=terms(k,q,D)
 a=(s+1)*(1+2*u)-1
 b=1-(s+1)*(1+2*v)
 P=lambda z:T*z**3+p2*z*z+p1*z+p0
 H=lambda k,z:2*D*z**3+(3*k-6*(s+1)*D)*z*z+(6*q-6*(s+1)*k)*z+2*D-3*k+6*q-6*(s+1)*q
 RR=s*s*D+k*s+q
 SS=s*s*D-k*s+q
 G=(s+1)*k*D*T*p0*RR*SS*(RR+(s+1)**2*D)*(SS+(s+1)**2*D)*a*b*(a-b)
 return clean([P(a),P(b),90*(s+1)*A-B,H(k,a),H(-k,-b)],G,R)
def unequal(p):
 F,R,s,Z=bank(p);C=lambda c:R([F(c)])
 got=[]
 for u,v in permutations(Z,2):
  A=u+v;B=u*v
  D=(4-3*A+2*B)*s-(4-A)
  k=2*(u-v)*(s+1)*(2*s+1)
  q=(s*(A-2*B)-A)*(2*s*s+2*s+1)+2*s*(s*(2-A)-2)
  f=general(R,u,v,s,k,q,D)
  if f.degree()>0:got.append((u,v,f))
 print('unequal regular',p,'surviving fibers',got,flush=True)
 return got
def exceptional(p):
 F,R,k,Z=bank(p)
 s=R([-F.one()/2]);D=R.one()
 out=[];count=0
 for u,v in permutations(Z,2):
  if 12-5*(u+v)+2*u*v!=0:continue
  count+=1
  q=(u*(2*s*s+2*s+1)+2*s-(s*(1-u)-1)*k)/(2-u)
  f=general(R,u,v,s,k,q,D)
  print('unequal singular',p,u,v,f,flush=True)
  if f.degree()>0:out.append((u,v,f))
 assert count==2
 return out
def equal(p):
 F,R,x,Z=bank(p)
 out=[]
 for u in Z:
  s=1/(1-u)
  q=(u*(2*s*s+2*s+1)+2*s)/(2-u)
  z=(s+1)*(1+2*u)-1
  T=-105*x*q-15*x+175*q**3+255*q*q+105*q+9
  p1=-3*(-175*x*q-21*x+245*q**3+385*q*q+171*q+15)/7
  pr0=3*(-21*x+35*q*q+42*q+15)/7
  pr2=-3*(-5*x+15*q*q+10*q+3)
  A=-63*x*x*q+21*x*x-70*x*q**3-210*x*q*q-138*x*q-30*x+245*q**5+805*q**4+986*q**3+546*q*q+129*q+9
  B=-525*x*x*q+525*x*x-1750*x*q**3-5670*x*q*q-3150*x*q-630*x+3675*q**5+13825*q**4+17970*q**3+9990*q*q+2259*q+153
  r0=(s*s+q)**2-x*s*s
  G=x*T*pr0*r0*((s*s+q+(s+1)**2)**2-x*s*s)*z*z*(s+1)
  g=clean([p1+T*z*z,pr0+pr2*z*z,90*(s+1)*A-B],G,R)
  if g.degree()>0:out.append((u,g))
 print('equal',p,'surviving fibers',out,flush=True)
 return out
if __name__=='__main__':
 assert all(certify(p) for p in (13,59,79,83,107,1129,6011194025914915991))
 assert not exceptional(107)
 for p in (79,83):assert not equal(p)
 for p in (13,59,107,1129,6011194025914915991):assert not unequal(p)
