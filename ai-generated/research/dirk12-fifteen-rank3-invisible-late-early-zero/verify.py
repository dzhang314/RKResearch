#!/usr/bin/env python3
"""Exact genuine bare-cubic late-ghost residue identities and grade-five checks."""
import sympy as S


def eq(f,g=0):
    assert S.cancel(f-g)==0, S.factor(f-g)


def main():
    T,x,z,m,H,w=S.symbols('T x z m H w')
    P=10*T*T-12*T+3
    N=T*(T-1)*(5*T-3)/2
    Q=S.Rational(64,3)-40*T
    E=(30*T*T-28*T+1)/3
    Z=x*(5*x-2)/(3*(2*x-1));M=(4*x-3)/x
    pz=P.subs(T,z);nz=N.subs(T,z)
    T0=(z-1)*pz-m*nz
    sig=(z-1)*Q.subs(T,z)+m*E.subs(T,z)
    eq(Q*N+E*P,1)
    eq(T0.subs({z:Z,m:M}),(Z-1)*5*x*(x-1)**2/(6*(2*x-1)**2))
    eq(m+Q.subs(T,z)*T0,pz*sig)
    eq((z-1)*z*pz-m*(z*nz-z*H),z*(T0+m*H))
    Hs=-T0/m
    Ws=z*(z-1)*pz/m
    eq(Ws,z*(nz-Hs))
    eq(10*(1/Hs-Q.subs(T,z))/pz,-10*sig/T0)
    eq(Ws*Hs, -z*(z-1)*pz*T0/m**2)
    print('bare cubic primitive, exact late amplitude and residue without early-zero input')
    b=[4,S.Rational(8,3),2,S.Rational(8,5),S.Rational(33,25)]
    eq(S.series((-Q/P).subs(T,1/w),w,0,6).removeO(),
       sum(q*w**j for j,q in enumerate(b,1)))
    for j,c in enumerate(b[:4],1):eq(c/8 if not isinstance(c,int) else S.Rational(c,8),S.Rational(1,j+1))
    eq(b[-1]/8+S.Rational(1,600),S.Rational(1,6))
    eq(S.integrate(T**3*P,(T,0,1)),S.Rational(1,60))
    l=x**3*(x-1)**2/2
    qb=l/Ws
    eq(-qb*Hs*z*pz,l*T0/(z-1))
    print('identical geometry-free moments, degree-six cancellation and physical B(x) scale')
    J=T**3*(T-1)*(2*T-1)/10
    eq(S.diff(J,T),T*T*P/10)
    L=(1-4*T)/25
    eq(S.rem(5*(5*T-3)*L+T*(2*T-1),P,T))
    d=x-z;u=Ws-d*z*pz
    R=(u+d*z*z*pz)/10-J.subs(T,z)-Hs*z*L.subs(T,z)
    eq(R,z*(z-1)*pz*(5*m*x-4*m*z-8*z+7)/(50*m))
    eq(R.subs({z:Z,m:M}))
    n=-3*(3*T-2)/20
    eq(S.rem(N,P,T),n)
    n0=S.Poly(n,T).nth(0);n1=S.Poly(n,T).nth(1)
    L2=-(5*T-3)/5
    eq(S.rem(L2*N-(n1*T*T/3+n0*T/2),P,T))
    R2=n1*z**3/3+n0*z*z/2-u*n.subs(T,1)+d*z*(Hs-n.subs(T,z))-Hs*z*L2.subs(T,z)
    eq(R2,z*(z-1)*pz*(m*x-4*x+3)/(4*m))
    eq(R2.subs({z:Z,m:M}))
    print('both genuine late grade-five physical-row residuals are already paid identities')


if __name__=='__main__':
    main()
