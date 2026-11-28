#!/usr/bin/env python3
"""Exact rational inputs for the no-late numerical-zero three-fifths chart."""
import sympy as S


def eq(f,g=0):
    assert S.cancel(f-g)==0,S.factor(f-g)


def main():
    T,w,a,y=S.symbols('T w a y')
    x=S.Rational(3,5);v=S.Rational(33,169);delta=S.Rational(1,16)
    E=4*(x+2)**2*w*w-(4*x*x+16*x+1)*w+x*(2*x+1)
    gm=(2*w*x*(x+2)-x*x)/(w*w*(2*x*x-2*x+3))
    eq(E,(4*w-1)*(169*w-33)/25)
    eq(gm.subs(w,S.Rational(1,4)),S.Rational(8,3))
    eq((1-6*w+3*gm*w*w).subs(w,S.Rational(1,4)))
    mu=gm.subs(w,v);eq(mu,S.Rational(2197,847))
    E1=mu*v*(7-4*mu)/((mu-1)*(2-mu))
    E2=-6*mu*v*v/(2-mu)
    E3=-3*mu*mu*v**3/((mu-1)*(2-mu))
    H=T*T-6*v*T+3*mu*v*v
    D3=T**3-E1*T*T+E2*T-E3
    eq(H,T*T-S.Rational(198,169)*T+S.Rational(27,91))
    eq(D3,T**3-S.Rational(136279,75450)*T*T+S.Rational(6534,6539)*T-S.Rational(3993,25150))
    eq(S.integrate(T*H,(T,0,1)),delta*H.subs(T,1))
    inv=S.invert(H,D3,T);eq(S.rem(inv*H,D3,T),1)
    ms=[S.Poly(S.rem(T**(k-1)*inv,D3,T),T).nth(2) for k in range(1,7)]
    assert ms==[S.Rational(n,d) for n,d in [(16437785,19092),(5920915,9546),
        (2998905,6364),(585585,1591),(1860859,6364),(14115683582,60020475)]]
    print("invalid v root, surviving cubic and hull, normalized physical diagonal, exact moments")
    r,k,e=S.Rational(43,23660),S.Rational(-43,23660),S.Rational(301847,3244350)
    assert ms[0]*ms[2]-ms[1]**2
    for j in range(1,6):
        eq(S.Rational(1,j+1)-r*ms[j-1]-k*(ms[j]-(e if j==5 else 0)),delta)
    M=lambda F:sum(S.Poly(F,T).nth(j)*z for j,z in enumerate(ms,1))
    Q=T*(T-1)*(T-x)
    eq(M(Q),S.Rational(-1183,258));eq(M(T*Q),S.Rational(-1183,86))
    print("nonzero actual first mode pivot, exact quintic correction, chronological Q ratios")
    L=S.diff(S.legendre(6,2*T-1),T)
    L6=lambda z:L.subs(T,z)
    A=(2*x-1)*L6(a*x)-x**3*(2*x*x-6*x+5)*L6(a)
    eq(A,-S.Rational(84,15625)*(456192*a**5-1113750*a**4+972000*a**3-361800*a*a+52800*a-2015))
    D=2*x*y-x-3*y*y+2*y
    P=-10*x*x+(20*x*x+5*x)*y+(-18*x*x-6*x)*y*y+(6*x*x+8*x-3)*y**3+(2-4*x)*y**4
    Y=(2*x-1)*D*L6(a*y)+y*y*P*L6(a)
    eq(Y.subs(y,1));eq(Y.subs(y,x),D.subs(y,x)*A)
    eq(S.Poly(Y,y).LC(),-3*(2*x-1)*5544*a**5)
    print("exact first scalar quintic and two inadmissible third-clock factors")


if __name__=='__main__':
    main()
