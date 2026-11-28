#!/usr/bin/env python3
"""All denominated scalar norm guards in the pure polynomial four-zero chart."""
import sympy as S
from math import gcd
u,v,y,s=S.symbols('u v y s')
Q=4*u**3-12*u*u+3*u+2
K=1+2*v-v*v
L=lambda Y,D:35*Y**4-30*Y*Y*D*D+3*D**4
def strip(x):
 for p in (2,3,5,7):
  while x and x%p==0:x//=p
 return x
def N(Q,H,x):return abs(int(S.resultant(Q,H,x).as_numer_denom()[0]))
assert Q.subs(u,2)==-8 and Q.subs(u,-2)==-84
assert strip(N(Q,L(3*u,u+2),u))==103
assert strip(N(Q,L(2*u,1),u))==267613
assert strip(N(K,L(v,1),v))==71
n_d=N(Q,L(u,u+2),u)
n_b=N(Q,S.resultant(K,L(u-2*v,u+2),v),u)
assert strip(gcd(n_d,n_b))==1
print('four-site Gaussian norm supports verified')
def I(f):return sum(c/S.Integer(j+1) for (j,),c in S.Poly(f,y).terms() if j%2==0)
def det(G):
    m=[I(G*y**j) for j in range(5)]
    return S.factor(S.Matrix(3,3,lambda i,j:m[i+j]).det())
g=det((y-s)*(y*y-9*s*s))
assert S.expand(g-4*s*(21*s**4-14*s*s+1)*(945*s**4-90*s*s+1)/3675)==0
S0=S.cancel(g.subs(s,-u/(u+2))).as_numer_denom()[0]
assert strip(N(Q,S0,u))==103*149
print('two-live 5-site support',103*149)
for name,G,p in [('midpoint',y*(y-2*u)*(y+v),770514337),
                  ('other',((u+2)*y-u)*((u+2)*y-3*u)*((u+2)*y-u+2*v),26254266039604698273071)]:
    H=det(G)
    for c in S.Poly(H,u,v).coeffs():assert strip(int(S.denom(c)))==1
    nn=N(Q,S.resultant(K,H,v),u)
    assert strip(nn)==p
    print('one-live 5-site support',name,p)
