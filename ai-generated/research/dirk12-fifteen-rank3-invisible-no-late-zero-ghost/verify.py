#!/usr/bin/env python3
"""Exact projection replay for the no-late numerical-zero ghost."""
import sympy as S

r,x,v,m,X=S.symbols("r x v m X")
R=S.Rational
D=r*r-4*r+1
t=-r*(r+1)/D
h=[R(1,6),-r*r*(r-2)/(6*(2*r-1)),
   -r*r*(r-2)*(r+1)*(5*r*r-14*r+5)/(6*D**3)]
p=2*x*x-2*x+3
E1=m*v*(7-4*m)/((m-1)*(2-m))
E2=-6*m*v*v/(2-m)
E3=-3*m*m*v**3/((m-1)*(2-m))


def eq(a,b):
    assert S.cancel(a-b)==0


def main():
    nodes=[S.Integer(1),r,t]
    I=sum(h[i]*S.prod(X-z for j,z in enumerate(nodes) if i!=j)/
                 S.prod(y-z for j,z in enumerate(nodes) if i!=j)
          for i,y in enumerate(nodes))
    eq(I, (-(r+1)*(r*r-r+1)*X*X+6*r*(r*r-r+1)*X-3*r*r*(r+1))/
            (6*(2*r-1)*D))
    mm=(r+1)**2/(r*r-r+1)
    uu=v*(r+1)/r
    eq(E1.subs(m,mm),(1+r+t)*uu)
    eq(E2.subs(m,mm),(r+t+r*t)*uu**2)
    eq(E3.subs(m,mm),r*t*uu**3)
    print("actual three nonzero ghost amplitudes and symmetric hull projection")

    B=5*E1-4*(2+x)
    M=(2*v*x*(x+2)-x*x)/(v*v*p)
    Q=v*v*p*(1-M)
    g1=(3*(1+2*x)-5*E2+6*v*B).subs(m,M)
    g2=(-2*x+5*E3-3*m*v*v*B).subs(m,M)
    A1=(4*x+3)*v-x
    A2=(6*x*x+24*x+9)*v-4*x*x-3*x
    E=4*(x+2)**2*v*v-(4*x*x+16*x+1)*v+x*(2*x+1)
    eq(g1,-3*A1*E/Q)
    eq(g2,2*x*A2*E/(p*Q))
    eq((4*x+3)*A2-(6*x*x+24*x+9)*A1,-10*x**3)
    eq(E.subs(x,-2),15*v+6)
    print("exact compatibility factors, including all vanishing-pivot guards")

    pp=[E1,E2,E3]
    assert [S.factor(z.subs({v:R(1,5),m:R(5,2)})) for z in pp]==[2,R(6,5),R(1,5)]
    eq(X**3-2*X**2+R(6,5)*X-R(1,5),(X-1)*(X**2-X+R(1,5)))
    # Under m=5/2, r²-3r+1=0, so t=r+1 and u*t=1 exactly.
    rp=r*r-3*r+1
    for k in [t-(r+1),(r+1)**2/(5*r)-1]:
        n,d=S.cancel(k).as_numer_denom()
        assert S.rem(n,rp,r)==0 and S.gcd(d,rp,r)==1
    print("first Legendre-root branch: exact Lobatto-four donor clocks")


if __name__=="__main__":
    main()
