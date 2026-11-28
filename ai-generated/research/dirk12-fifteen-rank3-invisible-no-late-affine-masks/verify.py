#!/usr/bin/env python3
"""Exact scalar and real-root replay for the no-late affine-mask charts."""
import sympy as S

x,d,p,c1,c2,c3,X=S.symbols("x d p c1 c2 c3 X")
R=S.Rational
J=lambda x:c1*x*x/2+c2*x**3/3+c3*x**4/4
JX=lambda x:c1*x**3/3+c2*x**4/4+c3*x**5/5
G=(2*x*x-2*x+3)*c1+(x*x+2*x)*c2+3*x*x*c3
D=20*(x-1)**2*d*d+(-12*x*x+24*x-9)*d+(2*x*x-3*x+1)
V=8*x**3+12*x*x-30*x+1


def eq(a,b):
    assert S.cancel(a-b)==0


def prim(f,z):
    return sum(c*z**(k[0]+1)/(k[0]+1) for k,c in S.Poly(f,X).terms())


def main():
    W=X*X*(X-1)**2*(X-x)
    eq(prim(W,1),-(2*x-1)/60)
    eq(prim(W,x),-x**4*(2*x*x-6*x+5)/60)
    B=X*X*(X-1)**2
    eq(prim(B,1),R(1,30))
    eq(prim(B*(X-R(1,2)),1),0)
    print("exact first-two primitive integrals and half-clock mask")

    eq(6*(2*x-1)*(J(x)-JX(x))-6*x**4*(2*x*x-6*x+5)*(J(1)-JX(1)),
       -x*x*(x-1)**2*G)
    eq(2*(5*x-3)*J(x)+x**4*((6*x-10)*J(1)-x+1),
        (x-1)*x*x*G+(x-1)*x**4*(c1+c2+c3-1))
    R_com=(2*x-1)*(x-1-d)*p+d*d*x**4*(2*x*x-6*x+5)
    R_tap=2*(5*x-3)*p+x**4*((6*x-10)*d-x+1)
    eq(2*(5*x-3)*R_com-(2*x-1)*(x-1-d)*R_tap,x**4*(x-1)*D)
    eq(D.subs(d,0),(x-1)*(2*x-1))
    eq(R_tap.subs(x,R(3,5)),R(162,3125)*(1-16*d))
    M=S.Matrix([[1,1,1],[R(1,2),R(1,3),R(1,4)],
                [x*x/2,x**3/3,x**4/4]])
    eq(M.det(),-x*x*(x-1)**2/24)
    print("guarded first-diagonal eliminant, exceptional 3/5, and cubic uniqueness")

    eq(S.discriminant(D,d),-(2*x-1)*V)
    poly=S.Poly(V,x,domain="QQ")
    assert poly.count_roots(-S.oo,S.oo)==3
    for lo,hi in [(-2838,-2837),(33,34),(1303,1304)]:
        lo,hi=R(lo,1000),R(hi,1000)
        assert poly.eval(lo) and poly.eval(hi) and poly.count_roots(lo,hi)==1
    print("exact discriminant and three Sturm-isolated interval endpoints")


if __name__=="__main__":
    main()
