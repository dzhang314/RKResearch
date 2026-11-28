#!/usr/bin/env python3
"""Exact structural double root and uniform reflected collision arithmetic."""
import sympy as S


def eq(a,b=0):
    assert S.cancel(a-b)==0,S.factor(a-b)


def main():
    X,s,Q,la=S.symbols('X s Q la')
    A=la*(X-s)*Q
    W=(X+la*s)*A/(1+la)
    eq(X*A-W-la*(W-s*A))
    eq(W-X*A,-la**2/(1+la)*(X-s)**2*Q)
    print("literal commute-and-shift factor gives an exact fifth double root")
    for j in range(6):
        for k in range(4):
            n=S.Rational(1,(j+1)*(j+2))*S.beta(j+3,k+2).expand(func=True)
            r=S.beta(j+1,k+4).expand(func=True)/((k+2)*(k+3))
            eq(n,r)
    print("all monomial coefficients in the paid twofold primitive integral")
    w,c=S.symbols('w c')
    N=S.symbols('N0:7')
    m=[N[j+1]-w*N[j] for j in range(6)]
    p=[c*(m[k+1]-w*m[k])+N[k+2]/S.Integer((k+2)*(k+3)) for k in range(4)]
    for k in range(3):
        r=((k+4)+1/(c*(k+3)))*m[k+2]-(2*k+6)*w*m[k+1]+(k+2)*w*w*m[k]
        eq((k+4)*p[k+1]-(k+2)*w*p[k],c*r)
    print("adjacent primitive equations give the three exact paid moment recurrences")
    q,z,C=S.symbols('q z C')
    ms=[1,S.Rational(2,3),4*q/9,16*q*q/(27*(3-q)),160*q**3/(81*(3-q)*(9-4*q))]
    E=[((k+4)+C/S.Integer(k+3))*ms[k+2]-(2*k+6)*z*ms[k+1]+(k+2)*z*z*ms[k]
       for k in range(3)]
    C0=-3*(8*q+9*z*z-18*z)/(2*q)
    eq(E[0].subs(C,C0))
    F=6*q*z+2*q-9*z
    A=-8*q+9*z
    B=2*q*z+6*q-9*z
    f0,f1=[S.factor(c.subs(C,C0)).as_numer_denom()[0] for c in E[1:]]
    eq(f0,2*A*F);eq(f1,16*q*B*F)
    eq(9*B-(2*q-9)*A,2*q*(8*q-9))
    eq(F.subs({q:S.Rational(9,8),z:1}))
    L=4*q/(9-4*q)
    eq(F.subs(z,-L/(L-2)))
    print("guarded factors force the fifth reflected label to be the remaining reverse u")


if __name__=='__main__':
    main()
