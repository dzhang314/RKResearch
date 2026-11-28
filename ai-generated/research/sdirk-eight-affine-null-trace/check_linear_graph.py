#!/usr/bin/env python3
import sympy as S
from math import gcd
from itertools import permutations
u,v,x=S.symbols('u v x')
Q=lambda u:4*u**3-12*u*u+3*u+2
Qv=S.div(Q(v)-Q(u),v-u,v)[0]
assert S.expand(Qv*(v-u))==S.expand(Q(v)-Q(u))
assert S.discriminant(Q(u),u)==7776
def det(M):
  return S.expand(sum((-1)**sum(p[i]>p[j] for i in range(3) for j in range(i+1,3))*M[0][p[0]]*M[1][p[1]]*M[2][p[2]] for p in permutations(range(3))))
def point(D,T,A):
  m=[D*S.Rational(1,i+2)-T*S.Rational(1,i+1) for i in range(6)]
  M=[[m[i+j] for j in range(3)] for i in range(3)]
  p=[det([[-m[i+3] if j==k else M[i][j] for j in range(3)] for i in range(3)]) for k in range(3)]
  return det(M)*A**3+p[2]*A*A*D+p[1]*A*D*D+p[0]*D**3
# A then Z: root t=0, gamma=(2-u)/(1-u).
D=1-u;G=2-u
def anorm(f):
  e=S.resultant(Q(u),S.Poly(f,u),u)
  return abs(int(e.as_numer_denom()[0]))
af=point(D,0,2*G)
ab=point(D,0,D-G*(1+2*u))
nsA=[anorm(af),anorm(ab)]
assert nsA==[590713,2195891] and gcd(*nsA)==1
print('AZ norm numerators',nsA,'gcd',gcd(*nsA))
# Z then Z: u and v are distinct roots of Q, D = sum of the two affine anchors.
D=4-3*(u+v)+2*u*v
G=(2-u)*(2-v);T=(1-u)*(2-v)
def norm(f):
  parts=S.resultant(Qv,S.Poly(f,u,v),v)
  res=S.resultant(Q(u),parts,u)
  return abs(int(res.as_numer_denom()[0]))
fa=point(D,T,G*(1+2*u));fb=point(D,T,D-G*(1+2*v))
nsZ=[]
GB=S.groebner([Qv,Q(u)],v,u,domain=S.QQ)
def guard_poly(expr):
  for c in S.Poly(expr,v,u,domain=S.QQ).coeffs():
    d=int(S.denom(c))
    for p in (2,3,5,7):
      while d%p==0:d//=p
    assert d==1
for b in GB.polys:guard_poly(b.as_expr())
for f in [fa,fa+fb,fa-fb]:
  z=S.Poly(f,v,u,domain=S.QQ)
  guard_poly(z.as_expr())
  qs,rem=GB.reduce(z.as_expr())
  for q in (*qs,rem):guard_poly(q)
  nsZ.append(norm(rem))
assert nsZ==[442659953786344729677,2426138581130786239123999329,21483260063623790691729363]
assert gcd(*nsZ)==81
print('ZZ norm numerators',nsZ,'gcd',gcd(*nsZ))
