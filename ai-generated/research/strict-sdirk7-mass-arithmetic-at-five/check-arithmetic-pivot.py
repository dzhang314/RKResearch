#!/usr/bin/env python3
from flint import fmpz_mpoly_ctx,fmpz_poly,nmod_poly
from sympy import primerange
from math import prod
from fractions import Fraction
C=fmpz_mpoly_ctx.get(('u','e'),'lex');u,e=C.gens()
A=35*e*(5*e**2-3)
B=15*(3*e**2-1)-3*A
D=-15*e*(7*e**2-5)-2*15*(3*e**2-1)+3*A
E=9-15*e**2-15*e*(5-7*e**2)+15*(3*e**2-1)-A
const=lambda n:C.constant(n)
squares=[u-1,u-2,u-3,A,B]
def sat(F,den):
  if not F:return F
  for q in den:
    assert q
    while (p:=F.gcd(q)).total_degree()>0:
      F,r=divmod(F,p)
      assert not r
  return F
K=(u-3)*(u-2)**2
L=(u-3)*(u-1)*(2*u-3)
V=(u-2)*(u-1)**2
q3,q2,q1,q0=2*K,-6*(K+L),12*(V+L),-12*V
p1=sat(D*A*q2*q2-B*B*q3*q1,squares)
p2=sat(E*A*A*q2**3-B**3*q3*q3*q0,squares)
print('exceptional equations',p1.degrees(),p2.degrees(),flush=True)
r=p1.resultant(p2,1)
print('raw resultant',r.degrees(),flush=True)
r=sat(r,squares[:3])
t=r.to_dict()
P=fmpz_poly([int(t.get((i,0),0)) for i in range(r.degrees()[0]+1)])
k,fs=P.factor()
assert P==k*prod(f**m for f,m in fs)
def rootless(f):
 for p in primerange(2,1000):
   c=nmod_poly(f.coeffs(),p)
   if c.degree()==f.degree() and not c.roots():return p
 return None
assert sorted((f.degree(),i,rootless(f)) for f,i in fs)==[(2,18,2),(27,1,23)]
print("global noncentered arithmetic fourth-slope exception excluded")
