#!/usr/bin/env python3
"""Five true forward zeros: exact old-cubic affine curvature projection."""
from functools import reduce
from math import lcm
import sympy as S
X,a,b,c0,c1,c2=S.symbols('X a b c0 c1 c2')
r3=X**3+c2*X**2+c1*X+c0
J4=lambda x:42*x**4-84*x**3+56*x*x-14*x+1
J5=lambda x:(2*x-1)*(66*x**4-132*x**3+84*x*x-18*x+1)
H=X*J4(X)
def prim(p,x=X):
    return S.Poly(p,x).integrate().as_expr()
def vec(p):
    r=S.Poly(S.rem(p,r3,X),X)
    return S.Matrix([r.nth(i)for i in range(3)])
J=prim(X*r3);Fb=prim(X*(X-b)*r3)
K=Fb*H.subs(X,b)-Fb.subs(X,b)*H
D=S.factor(S.det(S.Matrix.hstack(vec(J),vec(X*J),vec(K))))
print('curvature factorization',S.factor_list(D)[0],[(S.Poly(f,b,c0,c1,c2).total_degree(),k)for f,k in S.factor_list(D)[1]],flush=True)
co,fac=S.factor_list(D)
# Branch through every actual possible factor except b=0, which is forbidden.
assert {(f,k) for f,k in fac if f in (b,c0)}=={(b,1),(c0,1)}
clock_factors=[f for f,k in fac if f not in (b,c0)]
T5raw=J5(X)*J4(a)-J5(a)*J4(X)
T4raw=S.Poly(T5raw,X).exquo(S.Poly(X-a,X))
L=T4raw.LC()
Y4=S.Poly(T4raw.as_expr().subs(X,b),b)
C2=T4raw.nth(3)+L*b
C1=T4raw.nth(2)+b*C2
C0=T4raw.nth(1)+b*C1
projections=[]
for F in clock_factors:
    Fr = S.Poly(F,c0,c1,c2)
    d=max(i+j+k for (i,j,k),w in Fr.terms())
    G=sum(w*C0**i*C1**j*C2**k*L**(d-i-j-k)
          for (i,j,k),w in Fr.terms())
    G = S.Poly(S.expand(G),b).prem(Y4)
    assert G!=0
    co,g=G.primitive()
    print('relative degree',g.degree(),S.degree(g.as_expr(),a),'removed',S.factor(co),flush=True)
    FF=S.Poly(S.resultant(Y4,g,b),a)
    assert not FF.is_zero
    factors=S.factor_list(FF)[1]
    print('exact projection degrees',[(f.degree(),i)for f,i in factors],flush=True)
    projections.append((F,g,co,FF,factors))
