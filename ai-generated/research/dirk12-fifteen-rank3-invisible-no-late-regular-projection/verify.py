#!/usr/bin/env python3
"""Exact discriminant, chosen coefficient guards, and Legendre jet identities."""
import sympy as S


def eq(f,g=0):
    assert S.cancel(f-g)==0,S.factor(f-g)


def main():
    T,x,v,a=S.symbols("T x v a")
    E=4*(x+2)**2*v*v-(4*x*x+16*x+1)*v+x*(2*x+1)
    disc=8*x**3+12*x*x-30*x+1
    eq(S.discriminant(E,v),-(2*x-1)*disc)
    eq(disc.subs(x,S.Rational(1,2)),-10)
    eq(E.subs(x,-2),15*v+6)
    assert S.gcd_list(S.Poly(E,v).all_coeffs())==1
    x0=S.Rational(3,5);v0=S.Rational(33,169)
    eq(E.subs({x:x0,v:v0}))
    assert S.diff(E,v).subs({x:x0,v:v0})
    print("primitive irreducible generic v quadratic and nondegenerate selected residue")
    P=1399
    def unit(q):
        u,w=map(int,S.fraction(S.cancel(q)))
        assert (u%P) and (w%P),(u,w)
    mu=(2*v*x*(x+2)-x*x)/(v*v*(2*x*x-2*x+3))
    mu=mu.subs({x:x0,v:v0});eq(mu,S.Rational(2197,847))
    for q in (x0,x0+2,x0-1,2*x0-1,v0,mu-1,mu-2,2*x0*x0-2*x0+3,
              S.diff(E,v).subs({x:x0,v:v0})):unit(q)
    H=T*T-6*v0*T+3*mu*v0*v0
    D3=T**3-mu*v0*(7-4*mu)/((mu-1)*(2-mu))*T*T \
           -6*mu*v0*v0/(2-mu)*T+3*mu*mu*v0**3/((mu-1)*(2-mu))
    for q in (H.subs(T,1),S.resultant(D3,H,T),S.discriminant(D3,T),D3.subs(T,0)):unit(q)
    inv=S.invert(H,D3,T)
    ms=[S.Poly(S.rem(T**(j-1)*inv,D3,T),T).nth(2) for j in range(1,7)]
    det=ms[0]*ms[2]-ms[1]**2
    unit(det)
    unit(-S.Rational(43,23660))
    unit(ms[2]-(1+x0)*ms[1]+x0*ms[0])
    assert all(int(S.denom(q))%P for q in ms)
    print("all special-point ghost geometry, first live pivot, and cardinal guards are 1399-units")
    L={n:S.diff(S.legendre(n,2*T-1),T) for n in (5,6,7)}
    c,d,e=S.symbols("c d e")
    assert len(S.solve(S.Poly(T*L[6]-c*L[5]-d*L[6]-e*L[7],T).all_coeffs(),
                       (c,d,e),dict=True))==1
    eq(S.det(S.Matrix([[L[n].subs(T,0) for n in (5,6)],
                       [a*S.diff(L[n],T).subs(T,0) for n in (5,6)]])),7560*a)
    print("neighboring modes and exact degree-five two-jet guard")


if __name__=='__main__':
    main()
