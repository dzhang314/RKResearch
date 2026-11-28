#!/usr/bin/env python3
"""Exact scalar and polynomial stage-read identities for the half-clock chart."""
import sympy as S


def eq(f,g=0):
    assert S.cancel(f-g)==0, S.factor(f-g)


def J(f,T):
    p=S.Poly(f,T)
    return sum(p.nth(j)*T**(j+1)/(j+1) for j in range(p.degree()+1))


def main():
    T,x,y,a=S.symbols("T x y a")
    I=lambda f:J(f,T).subs(T,1)
    H=T*T-S.Rational(6,5)*T+S.Rational(3,10)
    D3=(T-1)*(T*T-T+S.Rational(1,5))
    inv=10*(30*T*T-40*T+11)
    eq(S.rem(inv*H,D3,T),1)
    assert [S.Poly(S.rem(inv*T**(k-1),D3,T),T).nth(2) for k in range(1,7)]==[300,200,150,120,100,86]
    print("six exact physical ordinary ghost moments from the first-root cubic hull")
    Qx=T*(T-1)*(T-x)
    X=S.Rational(1,2)
    Qb=Qx.subs(x,X)
    B=[Qb,T*Qb,T*T*Qb]
    eq(S.Matrix([[I(Qx),I(T*Qx)],[I(T*Qx),I(T*T*Qx)]]).det(),
       (5*x*x-5*x+1)/3600)
    r,k,e=S.Rational(23,16),S.Rational(-15,8),S.Rational(-1,5040)
    K=lambda f:I(T*f)-e*S.Poly(f,T).nth(5)
    for f in B: eq(J(f,T).subs(T,X),r*I(f)+k*K(f))
    W=T*T*(T-1)**2*(T-X)
    eq(W.subs(T,X)); eq(S.diff(W,T).subs(T,X),S.Rational(1,16))
    print("literal half-clock scalar nodal solve and zero second diagonal")
    P0=Qb*(T-y); D=6*y*y-6*y+1
    mat=S.Matrix([[I(f),K(f)] for f in (P0,T*P0)])
    rhs=S.Matrix([J(f,T).subs(T,y) for f in (P0,T*P0)])
    eq(mat.det(),-D/86400)
    eq((mat.adjugate()*rhs)[1],y**3*(y-1)**3/1440)
    ry=-y**3*(24*y**4-114*y**3+204*y**2-165*y+50)/D
    ky=-60*y**3*(y-1)**3/D
    for f in (P0,T*P0):eq(J(f,T).subs(T,y),ry*I(f)+ky*K(f))
    om=y*(y-1)*(2*y-1)/(2*D)
    eq(J(Qb,T).subs(T,y)-ry*I(Qb)-ky*K(Qb),om*Qb.subs(T,y))
    eq(om*(W+(T-X)*S.diff(W,T)).subs(T,y),(T-X).subs(T,y)*W.subs(T,y))
    L=S.diff(S.legendre(6,2*T-1),T)
    L6=lambda c:L.subs(T,c)
    Y=D*L6(a*y)-16*y*y*(y-1)**3*L6(a/2)
    eq(Y.subs(y,1),L6(a));eq(Y.subs(y,X))
    eq(S.Poly(Y,y).LC(),6*5544*a**5)
    print("two authentic third-row scalar reads, pivot, diagonal, inadmissible factors and leading coefficient")


if __name__=="__main__":
    main()
