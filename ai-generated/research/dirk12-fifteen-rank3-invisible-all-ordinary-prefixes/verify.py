#!/usr/bin/env python3
"""Exact all-geometry scalar operator identities and universal fourth split."""
import sympy as S


def eq(f,g=0):
    assert S.cancel(f-g)==0,S.factor(f-g)


def main():
    T,x,y,z,m,a=S.symbols('T x y z m a')
    Qx=T*(T-1)*(T-x)
    def J(F):
        p=S.Poly(F,T)
        return sum(p.nth(k)*T**(k+1)/(k+1) for k in range(p.degree()+1))
    def I(F):
        return J(F).subs(T,1)
    rho=x**4*(2*x*x-6*x+5)/(2*x-1)
    def Df(F):
        return S.factor(J(F).subs(T,x)-rho*I(F))
    eq(Df(Qx),-x**3*(x-1)**3/6)
    D=2*x*y-x-3*y*y+2*y
    Pxy=-10*x*x+(20*x*x+5*x)*y+(-18*x*x-6*x)*y*y+(6*x*x+8*x-3)*y**3+(2-4*x)*y**4
    Ry=-y**3*Pxy/((2*x-1)*D)
    om=y*(x-y)*(y-1)/(2*D)
    theta=(J(Qx).subs(T,y)-Ry*I(Qx)-om*Qx.subs(T,y))/Df(Qx)
    eq(theta,-y**3*(y-1)**3*(3*x*x-2*x*y-2*x+y)/(x**3*(x-1)**3*D))
    print('true third row cardinal and exact nonzero scalar divisor')
    P=10*T*T-12*T+3
    N=T*(T-1)*(5*T-3)/2
    Q=S.Rational(64,3)-40*T;E=(30*T*T-28*T+1)/3
    Z=x*(5*x-2)/(3*(2*x-1)); m=(4*x-3)/x
    T0=(z-1)*P.subs(T,z)-m*N.subs(T,z)
    sig=Q.subs(T,z)*(z-1)+m*E.subs(T,z)
    ms=[S.factor((sig/T0).subs(z,Z))]
    for b in [4,S.Rational(8,3),2,S.Rational(8,5)]:
        ms.append(S.factor(Z*ms[-1]+b))
    B=5*x**4*(x-1)**4/(12*(2*x-1)**2)
    for i in range(1,5):
        eq(Df(T**i*(T-1)),B*(ms[i]-ms[i-1]))
    W=T*T*(T-1)**2*(T-x)
    eq(Df(W));eq(Df(S.diff(W,T)))
    print('entire restricted scalar operator agrees with archived coefficient-prime model')
    F=Qx*(T-y)
    I0,I1=I(F),I(T*F)
    d0,d1=map(Df,[F,T*F])
    eq(d0,x**3*(x-1)**3*(2*x*y-x-y)/(6*(2*x-1)))
    eq(d1,x**4*(x-1)**3*(y-1)/(6*(2*x-1)))
    eq(d1/d0,x*(y-1)/(2*x*y-x-y))
    eq(I0*d1-I1*d0,x**3*(x-1)**3*D/360)
    print('universal fourth Möbius diagonal and true nodal moment determinant')
    L={n:S.diff(S.legendre(n,2*T-1),T) for n in (5,6,7)}
    q,r,u=S.symbols('q r u')
    assert len(S.solve(S.Poly(T*L[6]-q*L[5]-r*L[6]-u*L[7],T).all_coeffs(),
                       (q,r,u),dict=True))==1
    eq(S.det(S.Matrix([[L[n].subs(T,0) for n in (5,6)],
                       [a*S.diff(L[n],T).subs(T,0) for n in (5,6)]])),7560*a)
    print('neighboring modes and exact degree-five two-jet guard')


if __name__=='__main__':
    main()
