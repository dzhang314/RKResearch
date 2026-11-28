#!/usr/bin/env python3
"""Exact arithmetic and real-root replay for the ordinary fourth-ghost chart."""
import sympy as S

a,b,x,z,X=S.symbols("a b x z X")
R=S.Rational
cubic=lambda a,x:x*(10*x*x-12*a*x+3*a*a)
j=lambda a,x:x*x*(x-a)*(5*x-3*a)/2
ell=lambda a,x:x**3*(x-a)**2/2
f=lambda a,x:x*x*(x-a)**2*(4*x-3*a)/2
k=lambda a,x:5*x**6/3-12*a*x**5/5+3*a*a*x**4/4
L=lambda x:-42+840*x-5040*x*x+12600*x**3-13860*x**4+5544*x**5


def eq(p,q):
    assert S.cancel(p-q)==0


def J(p,u):
    return sum(c*u**(q[0]+1)/(q[0]+1) for q,c in S.Poly(p,X).terms())


def main():
    V=cubic(a,X)
    eq(J(V,x),j(a,x))
    eq(J(j(a,X),x),ell(a,x))
    eq(J((X-a)*V,x),f(a,x))
    eq(J(X**2*V,x),k(a,x))
    eq(f(a,b)*j(a,b)-ell(a,b)*(b-a)*cubic(a,b),
       -3*a*b**4*(a-b)**4/4)
    clock=(z-a-(b-z))*ell(a,b)-(b-z)*f(a,b)
    eq(clock,b*b*(b-a)**2*((6*b-3*a)*z-b*(5*b-2*a))/2)
    print("ordinary primitive determinant and exact clock relation")

    zz=x*(5*x-2)/(3*(2*x-1))
    eq(60*(2*x-1)*(k(1,x)-j(1,x)-(zz+1)*f(1,x)),
        x**4*(2*x*x-6*x+5))
    mm=(4*x-3)/x
    eq((zz-1)*cubic(1,zz)-mm*j(1,zz),
       5*x*x*(x-1)**3*(5*x-3)*(5*x-2)/(54*(2*x-1)**4))
    eq((x**3*(2*x*x-6*x+5)/(2*x-1)).subs(x,R(2,5)),-R(584,625))
    print("grade-six Legendre factor and exact late-amplitude factor")

    P=129888*a**5-330000*a**4+312000*a**3-136800*a*a+27800*a-2015
    eq(625*L(R(2,5)*a)+584*L(a), R(126,5)*P)
    pp=S.Poly(P,a,domain="QQ")
    assert pp.count_roots(-S.oo,S.oo)==3
    intervals=[(1579,1580),(7132,7133),(9321,9322)]
    for lo,hi in intervals:
        lo,hi=R(lo,10000),R(hi,10000)
        assert pp.eval(lo) and pp.eval(hi) and pp.count_roots(lo,hi)==1
    assert S.gcd(pp,S.Poly(L(a),a,domain="QQ")).degree()==0
    print("late numerical-zero quintic: exactly three real roots, each isolated")


if __name__=="__main__":
    main()
