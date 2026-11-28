#!/usr/bin/env python3
"""Exact scalar replay for the unified third ordinary live clock."""
import sympy as S
x,y,X,a=S.symbols("x y X a")
R=S.Rational
D=2*x*y-x-3*y*y+2*y
P=(6*x*x*y**3-18*x*x*y*y+20*x*x*y-10*x*x
   -4*x*y**4+8*x*y**3-6*x*y*y+5*x*y+2*y**4-3*y**3)
W=X*X*(X-1)**2*(X-x)
omega=y*(x-y)*(y-1)/(2*D)
L=lambda t:-42+840*t-5040*t*t+12600*t**3-13860*t**4+5544*t**5


def eq(p,q):
    assert S.cancel(p-q)==0


def J(p,z):
    return sum(c*z**(k[0]+1)/(k[0]+1) for k,c in S.Poly(p,X).terms())


def main():
    Wy=W.subs(X,y)
    Wpy=S.diff(W,X).subs(X,y)
    eq(Wy+(y-x)*Wpy, -2*D*Wy/(y*(y-1)))
    eq(omega*(Wy+(y-x)*Wpy),(y-x)*Wy)
    eq(J(W,1),-(2*x-1)/60)
    Q=S.factor((J(W,y)-omega*Wy)/(y*J(W,1)))
    eq(Q, -y*y*P/((2*x-1)*D))
    eq(Q.subs(y,1),1)
    eq(Q.subs(y,x),x**3*(2*x*x-6*x+5)/(2*x-1))
    cleared=S.Poly((2*x-1)*D*L(a*y)+y*y*P*L(a),y)
    assert cleared.degree()==7
    eq(cleared.LC(),-3*(2*x-1)*5544*a**5)
    print("third live equation: exact nonzero diagonal, degree seven, and both known roots")

    S0=X*(10*X*X-12*X+3)
    F=J((X-1)*S0,X)
    j=J(S0,X)
    l=J(j,X)
    eq(F-(4*x-3)/x*l,3*W/(2*x))
    p=(Wy-omega*Wpy)/S.diff(W,X).subs(X,x)
    eq(p,y**3*(x-y)*(y-1)**3/(2*x*x*(x-1)**2*D))
    theta=S.factor((l.subs(X,y)-p*j.subs(X,x)-omega*j.subs(X,y))/l.subs(X,x))
    eq(theta, -y**3*(y-1)**3*(3*x*x-2*x*y-2*x+y)/(x**3*(x-1)**3*D))
    print("late common ghost mask and actual third tap ratio")


if __name__=="__main__":
    main()
