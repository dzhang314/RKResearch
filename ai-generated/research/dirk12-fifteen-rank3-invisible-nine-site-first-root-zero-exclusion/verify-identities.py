#!/usr/bin/env python3
"""Exact first-root zero moment solve and coefficient guards."""
import sympy as S


def eq(a,b=0):
    assert S.cancel(a-b)==0,S.factor(a-b)


def main():
    T,a,h,l,q=S.symbols('T a h l q')
    A=T*(T-1)*(T-(1-a))
    Is=[S.integrate(T**i*A,(T,0,1)).factor() for i in range(8)]
    for i,v in enumerate(Is):
        eq(v,S.Rational(1,i+4)-(2-a)/S.Integer(i+3)+(1-a)/S.Integer(i+2))
    M=S.Matrix([[Is[i+j] for j in range(3)] for i in (1,2,3)])
    D=42*a**3-56*a*a+21*a-2
    eq(M.det(),-D/889056000)
    cn=M.inv()*S.Matrix([-Is[j+3] for j in (1,2,3)])
    jn=M.inv()*S.Matrix([1,S.Rational(2,3)*h,h*h/4])
    N0=S.factor(Is[3]+sum(v*c for v,c in zip(cn,Is[:3])))
    N4=S.factor(Is[7]+sum(v*c for v,c in zip(cn,Is[4:7])))
    C0=42*a**4-84*a**3+56*a*a-14*a+1
    eq(N0,C0/(2520*D))
    B0=S.Rational(31,12)+h*sum(v*c for v,c in zip(jn,Is[:3]))
    B4=-h**3/13+sum(v*c for v,c in zip(jn,Is[4:7]))
    H=S.cancel(B0*N4-h*N0*B4)
    eq(S.Poly(H,h).LC(),N0/13)
    eq(H.subs(a,S.Rational(1,2)),(792*h**4-5148*h**3+8736*h*h-2808*h-403)/(-51891840))
    cert=[[-26598,48360,-29016,6448,-403],
          [-144144,271440,-168480,38688,-2496],
          [384384,-742560,474240,-112320,7488],
          [-216216,425880,-278460,67860,-4680],
          [33264,-66528,44352,-11088,792]]
    num=sum(sum(v*a**(4-j) for j,v in enumerate(row))*h**i for i,row in enumerate(cert))
    eq(H*25945920*D,num)
    L=S.diff(S.legendre(6,2*T-1),T).subs(T,a)
    assert S.gcd(D,L)==1 and S.gcd(C0,L)==1
    print("exact cubic coefficient solve, quartic h coefficients and both leading guards")
    q=S.Rational(9,16)
    eq((4*q-3)*(5-2*q)/(3*q),S.Rational(-31,18))
    ms=[-31*l/(12*h),l,2*h*l/3,h*h*l/4,h**3*l/13]
    n0,n1,n2,n3=ms[1:]
    eq(n0*n2/n1**2,q)
    eq((3*n1*n1-n0*n2)*n3,2*n1*n2*n2)
    eq(3*ms[0]*n2*n1**3,n0*(4*n0*n2-3*n1*n1)*(5*n1*n1-2*n0*n2))
    print("all five actual moment ratios at the reflected-zero q=9/16 gate")


if __name__=='__main__':
    main()
