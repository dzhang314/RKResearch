#!/usr/bin/env python3
from flint import fq_default_ctx,fq_default_poly_ctx

class Engine:
  def __init__(self,p,d=24):
    self.p=p
    self.F=fq_default_ctx(p,d,'z')
    self.Q=fq_default_poly_ctx(self.F)
    self.x=self.Q.gen()
    self.K=self.F.one()
  def setup(self,a):
    x=self.x;K=self.K
    g=(4+35*a*(1-a))/72
    c=(1+x)*g
    P=c**3+c*c*(a-2)+c*(a*a-2*a+9*K/7)+(a**3-2*a*a+9*a/7-2*K/7)
    return g,P,P[2]+P[0]+2*P[3]
  def br(self,P,star_allowed,slope=None):
    x=self.x
    p,d1,d2,d3=[P[j] for j in range(4)]
    k=1+2*x-x*x
    K=d1-2*p+x*(d2+p)+d3*x*x
    Q=2*(d2+2*d3+p)*x**3+(3*d1-4*d2+7*d3-10*p)*x*x+(-8*d1+5*d2-6*d3+15*p)*x+4*d1-2*d2-6*p
    for fn in (0,1):
      if not fn and not star_allowed:continue
      if not fn and slope is None:
        raise ValueError('unexpected undetermined scalar face')
      eq=Q if fn else K-k*slope
      if not eq:
        raise ValueError('unexpected undetermined scalar face')
      for u,e in eq.roots():
        kg=k(u)
        if u==0 or kg==0: continue
        if fn:
          w=2*u
          H=-2+u+4*u*u-u**3
          if H==0:continue
          r=2*u*(3*u-2)/H
          if r==0:continue
        else:
          if u==1 or u==2:continue
          w=2-u;r=self.F.zero()
        q=1+2*w-w*w+2*r*u
        if q==0:continue
        l=K(u)/kg
        if slope is not None and l!=slope:continue
        if P(w)!=q*(p+w*l):continue
        yield fn,u,w,kg,q,l
  def fronts(self,a):
    g,P,s=self.setup(a)
    gg,Q,t=self.setup(1-a)
    assert g==gg and g!=0
    L=1/g-2
    p,pR=P[0],Q[0]
    rev=False
    if s==0:
      if t==0:
        raise ValueError('unexpected simultaneous star freedom')
      P,Q=Q,P;s,t=t,s;p,pR=pR,p;rev=True
    out=[]
    for A in self.br(P,s==0):
      l=A[-1];dp=p+L*l
      if dp!=0:
        if pR==0:continue
        tau=-pR/dp
        want=-pR*l/dp
      else:
        if pR!=0:continue
        tau=None;want=None
      for B in self.br(Q,t==0,want):
        j=B[-1]
        if tau is not None:
          if j!=tau*l:continue
          u=tau
        elif l!=0:
          u=j/l
          if u==0:continue
        else:
          if j!=0:continue
          raise ValueError('unexpected projective graph freedom')
        if rev:out.append((B,A,1/u))
        else:out.append((A,B,u))
    return out

def degree(a,p):
 for d in (1,2,3,4,6,8,12,24):
    if a**(p**d)==a:return d
 return 24
