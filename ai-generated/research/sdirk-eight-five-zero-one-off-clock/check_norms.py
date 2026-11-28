#!/usr/bin/env python3
import sympy as S
X,u=S.symbols('X u')
Q=u*u-2*u-1
half=S.Rational(1,2)
J=lambda P:sum(c/S.Integer(i+1) for (i,),c in S.Poly(P,X).terms())
for phase in ('SS','SA','AS','AA'):
 for rev in ('equal','complement'):
    v=u if rev=='equal' else 2-u
    a=(1+u)/2;b=(3-u)/2 if phase[0]=='S' else (1+2*u)/2
    c=(1-v)/2
    d=(v-1)/2 if phase[1]=='S' else (1-2*v)/2
    P=(X-half)*(X-a)*(X-b)*(X-c)*(X-d)
    M=[S.rem(J(P*X**i),Q,u) for i in range(3)]
    H=S.rem(M[0]*M[2]-M[1]**2,Q,u)
    nn=S.resultant(H,Q,u)
    expect = {
       ('SS','equal'): (19**4,7965941760000),
       ('SS','complement'): (19**4,7965941760000),
       ('SA','equal'): (19**2*23,637275340800),
       ('SA','complement'): (19**2*23,637275340800),
       ('AS','equal'): (19**2*23,637275340800),
       ('AS','complement'): (19**2*23,637275340800),
       ('AA','equal'): (23**2,50982027264),
       ('AA','complement'): (2281**2,31863767040000)}[phase,rev]
    assert nn == S.Rational(*expect)
    for r in [*M,H,nn]:
        for cf in S.Poly(r,u).coeffs():
            b = int(S.denom(cf))
            for p in (2,3,5,7):
                while b%p==0:b//=p
            assert b==1
    print(phase,rev,'moments',M,'H=',H,'norm',nn,flush=True)
