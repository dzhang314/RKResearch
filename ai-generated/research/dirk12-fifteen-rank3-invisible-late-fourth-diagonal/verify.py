#!/usr/bin/env python3
"""Exact moments, Möbius fourth clock, and zero-diagonal mode elimination."""
import sympy as S


def eq(f,g=0):
    assert S.cancel(f-g)==0,S.factor(f-g)


def J(f,T):
    p=S.Poly(f,T)
    return sum(p.nth(j)*T**(j+1)/(j+1) for j in range(p.degree()+1))


def main():
    T,x,y,t,z=S.symbols('T x y t z')
    P=10*T*T-12*T+3
    N=T*(T-1)*(5*T-3)/2
    Q=S.Rational(64,3)-40*T
    E=(30*T*T-28*T+1)/3
    Z=x*(5*x-2)/(3*(2*x-1));m=(4*x-3)/x
    A=(z-1)*P.subs(T,z)-m*N.subs(T,z)
    sig=(z-1)*Q.subs(T,z)+m*E.subs(T,z)
    ms=[S.factor((sig/A).subs(z,Z))]
    for h in [4,S.Rational(8,3),2,S.Rational(8,5)]:
        ms.append(S.factor(Z*ms[-1]+h))
    def M(f):
        p=S.Poly(f,T)
        return S.factor(sum(p.nth(j)*v for j,v in enumerate(ms,1)))
    I=lambda f:J(f,T).subs(T,1)
    F=T*(T-1)*(T-x)*(T-y)
    N0,N1=M(F),M(T*F)
    eq(N0,2*(2*x-1)*(2*x*y-x-y)/(5*x*(x-1)))
    eq(N1,2*(2*x-1)*(y-1)/(5*(x-1)))
    phi=S.factor(N1/N0)
    eq(phi,x*(y-1)/(2*x*y-x-y))
    eq(M(F*(T-t)),N1-t*N0)
    eq(phi.subs(y,phi),y)
    eq(y*phi/((1-y)*(1-phi)),x/(1-x))
    print('true ghost moment factors and Möbius fourth-clock relation')
    I0,I1=I(F),I(T*F)
    D=2*x*y-x-3*y*y+2*y
    dd=S.factor(I0*N1-I1*N0)
    eq(dd,(2*x-1)**2*D/(150*x*(x-1)))
    eq(I(F*(T-phi)),-dd/N0)
    f0,f1=S.symbols('f0 f1')
    d=I0*N1-I1*N0
    Rt=(f0*N1-f1*N0)/d
    B=(I0*f1-I1*f0)/d
    eq(I0*Rt+N0*B,f0);eq(I1*Rt+N1*B,f1)
    print('nonzero physical two-by-two determinant and exact no-diagonal mode solve')


if __name__=='__main__':
    main()
