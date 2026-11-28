"""Exactly six physical zeros, one canceled off clock: fixed anchors."""
from itertools import product
import sympy as S
from sympy.polys.rings import ring
u=S.symbols("u")
f=S.Poly(u*u-2*u-1,u)
assert f.is_irreducible
K=S.QQ.algebraic_field((f,u));U=K.unit
C=lambda a,b=1:K.convert(S.Rational(a,b))
R,X=ring('X',K)
def I(P):
    return sum((q*2**k*C(1,k+1) for (k,),q in P.items()),K.zero)
# None of the first ordinary zero's clocks can be one of four Gauss
# labels under total ordinary support four.
L=lambda q:70*q**4-280*q**3+360*q*q-160*q+16
assert L(1+U)
for rel,front,rear in product((0,1),("star","arith"),("star","arith")):
    V=U if rel==0 else 2-U
    Wf=2*U if front=="arith" else 2-U
    Wr=2*V if rear=="arith" else 2-V
    a,b,s,t=1+U,1+Wf,1-Wr,1-V # rows 2,3,8,9
    assert len({a,b,s,t,K.one})==5
    P=(X-a)*(X-b)*(X-s)*(X-t)
    m=[I(P*X**i) for i in range(4)]
    m0,m1,m2,m3=m
    Delta=m0*m2-m1*m1
    print(rel,front,rear,'pivot',bool(Delta),flush=True)
    assert Delta
    q0=(m1*m3-m2*m2)/Delta
    q1=(m1*m2-m0*m3)/Delta
    assert not (m0*q0+m1*q1+m2) and not (m1*q0+m2*q1+m3)
    F=X**2+q1*X+q0
    nodes=P*F
    ir8=I(nodes//(X-s));ir9=I(nodes//(X-t))
    p=(2*Wr*V+1+2*Wr-Wr*Wr)/(2*V)
    proof=p*ir8-V*ir9
    print('reverse tap integral obstruction',bool(proof),flush=True)
    assert proof
