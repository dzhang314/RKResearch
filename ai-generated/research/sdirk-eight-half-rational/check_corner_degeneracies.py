"""Exact front/rear rank checks for the linear and quadratic corner systems."""
from itertools import product
import sympy as S
t,A,B,v = S.symbols('t A B v')
Q=t*t-S.Rational(1,2)
red=lambda f:S.rem(S.expand(f),Q,t)
def inv(f):
    z=S.invert(red(f),Q,t)
    assert red(f*z)==1
    return z
def vals(z):
    return S.Matrix([red(S.legendre(j,2*z-1)) for j in (3,4,5)])
def corner(e,star):
    u=1+2*e*t; w=2-u if star else 2*u
    r=0 if star else 3*u/2-1
    return tuple(map(red,((1+u)/2,(1+w)/2,u/16,(w-r)/16)))
def ev(M,p):
    return red((M.T*p)[0])
for front,rear,sign in product((True,False),(True,False),(1,-1)):
    a,b,ha,hb=corner(1,front)
    c,d,hc,hd=corner(sign,rear); c,d=red(1-c),red(1-d)
    Va,Vb,Vc,Vd=map(vals,(a,b,c,d))
    N=Va.cross(Vb).applyfunc(red)
    x,y=ev(Vc,N),ev(Vd,N)
    inv(x); inv(y)
    P=S.Matrix([[Va[0],Va[1],0],[Vb[0],Vb[1],0],[0,0,1]])
    m=inv(P.det())
    def p0(q):
        return (P.adjugate()*S.Matrix([ha*q(a),hb*q(b),0])).applyfunc(lambda f:red(m*f))
    def rear_eq(q,p):
        return red(hd*q(d)*ev(Vc,p)-hc*q(c)*ev(Vd,p))
    # The singular line-pole corner matrix is inconsistent in every phase.
    q=lambda z:z-v
    dl=rear_eq(q,N)
    pole=red(-dl.subs(v,0)*inv(S.Poly(dl,v).LC()))
    qe=lambda z:z-pole
    inv(rear_eq(qe,p0(qe)))
    # At the singular quadratic rank there are at most two denominator choices.
    q=lambda z:z*z+A*z+B
    dq=rear_eq(q,N)
    beta=red(-dq.subs(B,0)*inv(S.Poly(dq,B).LC()))
    qe=lambda z:red(z*z+A*z+beta)
    small=rear_eq(qe,p0(qe))
    assert S.degree(small,A)==2
    print(front,rear,sign,"line rank loss impossible; quadratic rank loss finite")
