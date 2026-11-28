#!/usr/bin/env python3
"""Exact global asymmetric Z/Z support with both actual third stages quadratic-zero."""
import sympy as S
from sympy import QQ,CRootOf,ring
from math import gcd,lcm
X=S.Symbol('X');Q=lambda u:4*u**3-12*u*u+3*u+2
p=Q(X)
U=CRootOf(p,0);V=CRootOf(p,1)
K=QQ.algebraic_field(U,V)
u=K.from_sympy(U);v=K.from_sympy(V);o=K.one
r,s=ring('S',K)
rr,t=ring('T',QQ)
def prim(f):
 return sum((rr(c)*t**j for j,c in enumerate(f.to_list()[::-1])),start=rr.zero)
M=sum((rr(c)*t**j for j,c in enumerate(K.mod.to_list()[::-1])),start=rr.zero)
def norm(f):return abs(int(M.resultant(prim(f)).numerator))
bad=1
def guard(P):
 global bad
 for a in P.values():
  for c in a.to_list():
   bad=lcm(bad,int(c.denominator))
def stop(n):
 for p in (2,3,5,7):
  while n and n%p==0:n//=p
 return n

# The primitive-coordinate equations hold in the full ordered-pair algebra, not
# only for the chosen real roots defining the degree-six rational model.
x,y=S.symbols('x y')
Qy=S.div(Q(y)-Q(x),y-x,y)[0]
assert S.Poly((y-x)*Qy-(Q(y)-Q(x)),y,x).is_zero
GB=S.groebner([Q(x),Qy],y,x,domain=QQ)
def guard_expr(f):
 for c in S.Poly(f,y,x,domain=QQ).coeffs():
  assert stop(int(S.denom(c)))==1
for f in GB.polys:guard_expr(f.as_expr())
for f,h in [(prim(u),x),(prim(v),y),(M,0)]:
 src=f.as_expr().subs(S.Symbol('T'),x+2*y)-h
 guard_expr(src)
 quo,rem=GB.reduce(src)
 assert rem==0
 for qj in quo:guard_expr(qj)
assert M.degree()==6
def C(u):return u*(2*s*s+2*s+1)+2*s
S0=u+v;P0=u*v
D=(4-3*S0+2*P0)*s-(4-S0)
k=2*(u-v)*(s+1)*(2*s+1)
q=(s*(S0-2*P0)-S0)*(2*s*s+2*s+1)+2*s*(s*(2-S0)-2)
assert stop(norm(12*o-5*S0+2*P0))==107**2
print('unequal singular determinant support',107**2)
def T_(k,q,D):
 return -105*k*k*q-15*k*k*D+175*q**3+255*q*q*D+105*q*D*D+9*D**3
def pp1(k,q,D):return -3*(-175*k*k*q-21*k*k*D+245*q**3+385*q*q*D+171*q*D*D+15*D**3)/7
def pp2(k,q,D):return -3*k*(-5*k*k+15*q*q+10*q*D+3*D*D)
def pp0(k,q,D):return 3*k*(-21*k*k+35*q*q+42*q*D+15*D*D)/7
def ab(k,q,D):
 x=k*k
 A=-63*x*x*q+21*x*x*D-70*x*q**3-210*x*q*q*D-138*x*q*D*D-30*x*D**3+245*q**5+805*q**4*D+986*q**3*D*D+546*q*q*D**3+129*q*D**4+9*D**5
 B=-525*x*x*q+525*x*x*D-1750*x*q**3-5670*x*q*q*D-3150*x*q*D*D-630*x*D**3+3675*q**5+13825*q**4*D+17970*q**3*D*D+9990*q*q*D**3+2259*q*D**4+153*D**5
 return A,B
T=T_(k,q,D);p1=pp1(k,q,D);p2=pp2(k,q,D);p0=pp0(k,q,D)
z1=(s+1)*(1+2*u)-1;z2=1-(s+1)*(1+2*v)
pf=T*z1**3+p2*z1*z1+p1*z1+p0
pr=T*z2**3+p2*z2*z2+p1*z2+p0
A,B=ab(k,q,D)
diag=90*(s+1)*A-B
R=s*s*D+k*s+q;RR=s*s*D-k*s+q
G=(s+1)*D*k*T*p0*R*RR*(R+(s+1)**2*D)*(RR+(s+1)**2*D)*z1*z2*(z1-z2)
for z in (s*u,s*v,D,k,q,pf,pr,diag,G,r.one):guard(z)
def trim(P):
 while P:
  g=P.gcd(G)
  if g.degree()==0:break
  guard(g);guard(G.exquo(g))
  P=P.exquo(g);guard(P)
 return P
P=[trim(w) for w in (pf,pr,diag)]
assert [a.degree() for a in P]==[12,12,16]
ns=[]
for a,b in ((0,1),(0,2),(1,2)):
 z=P[a].resultant(P[b])
 guard(r(z));ns.append(norm(z))
out=stop(gcd(*ns))
assert out==13**6*59**2*107**18*1129**2*6011194025914915991**2
print('unequal regular norm support',out)
# Equal gaps: solve q,s from the single literal second-gap equation and use the two
# symmetric outer-clock conditions p1+T*z^2=0, p0/k+(p2/k)*z^2=0.
R,x=ring('x',K)
s0=o/(o-u)
q0=(u*(2*s0*s0+2*s0+o)+2*s0)/(2*o-u)
z=(s0+o)*(o+2*u)-o
tt=-105*x*q0-15*x+175*q0**3+255*q0*q0+105*q0+9
f= -3*(-175*x*q0-21*x+245*q0**3+385*q0*q0+171*q0+15)/7+tt*z*z
h= 3*(-21*x+35*q0*q0+42*q0+15)/7-3*(-5*x+15*q0*q0+10*q0+3)*z*z
n=stop(norm(f.resultant(h)))
for f0 in (f,h,r(s0),r(q0),r(z),r(f.resultant(h))):guard(f0)
assert n==79**2*83**2 and stop(bad)==1
print('equal-gap linear-pin norm',n)
print('paid rational coefficient denominators verified')
