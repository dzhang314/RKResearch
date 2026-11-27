"""Exact two-tail projection for eight distinct active zero clocks."""
from equal_detected import ends
from variable_gamma import K,Lf,JJ,G
from sympy.polys.rings import ring
from itertools import product
R,u,g=ring('u g',K)

def raw(front,rear):
 A,B,r=ends(front,1);ha,hb=(A-1)/2,(B-1-r)/2
 A0=Lf(g*A);B0=Lf(g*B)
 Q0=g*(B*hb*A0-A*ha*B0);Q1=ha*B0-hb*A0
 Q=lambda z:Q0+Q1*z
 x=1-g;k=1+2*u-u*u
 c=x-g*u
 D9=(x-g)*Lf(c)*Q(x)-k*(c-g)*Lf(x)*Q(c)
 F9=D9.exquo(u)
 if rear is None:D8=2*(g-x)-g*k*(u-2)
 else:
  d=x-g*(2-u if rear else 2*u)
  H=R(1) if rear else -2+u+4*u**2-u**3
  q3=k if rear else (1+4*u-4*u*u)*H+4*u*u*(3*u-2)
  D8=(x-g)*Lf(d)*Q(x)*H-q3*(d-g)*Lf(x)*Q(d)
 Guards=g*(2*g-1)*Lf(g)*A0*B0*Q(x)
 return F9,D8,JJ(Q0.drop(u)),JJ(Q1.drop(u)),JJ(Guards.drop(u))

def proj(front,rear):
 A,B,_,_,Gd=raw(front,rear)
 print('start resultant',front,rear,A.degree(u),B.degree(u),flush=True)
 S=JJ(A.resultant(B))
 print('raw resultant degree',front,rear,S.degree(),flush=True)
 assert S
 while True:
  f=S.gcd(Gd)
  if f.degree()==0:break
  S=S.exquo(f)
 S=S.exquo(S.gcd(S.diff(G))).monic()
 F=S.factor_list()[1]
 print('guarded projection',front,rear,S.degree(),[(R.degree(),e) for R,e in F],flush=True)
 return S,F
if __name__=='__main__':
 for a,b in product((True,False),(None,True,False)):proj(a,b)
