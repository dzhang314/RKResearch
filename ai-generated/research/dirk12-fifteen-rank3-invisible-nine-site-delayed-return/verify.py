#!/usr/bin/env python3
"""Exact scalar replay of the delayed nine-site pair chronology."""
import sympy as S

r,t,w,z,X,h=S.symbols("r t w z X h")
R=S.Rational
lam=3*(r-1)*(r-2)
sig=R(1,6)
Q=r*r-4*r*t+t*t
P=r*r-3*r*t+t*t
hr=r**3/(36*(r-1))
ht=t**3*(2*r-t)/(36*(r-1)*(2*t-r))
ar=r/2-6*hr/r


def J(poly,x):
    return sum(c*x**(k[0]+1)/(k[0]+1)
               for k,c in S.Poly(poly,X).terms())


def row(nodes,x,hx,err):
    arr=[]
    for i,y in enumerate(nodes):
        rest=[u for j,u in enumerate(nodes) if i!=j]
        p=X*S.prod(X-u for u in rest)
        den=y*S.prod(y-u for u in rest)
        arr.append(S.factor((J(p,x)+err(rest)*hx)/den))
    return arr


def eq(a,b):
    assert S.cancel(a-b)==0


td,tr,tt=row([S.Integer(1),r,t],t,ht,lambda _:lam)
phir=(6*hr+ar*r**4-r**5/5)/hr
phit=(1+r+t)*lam-J(X*(X-1)*(X-r)*(X-t),t)/ht
psir=ar
psit=tt+hr*tr/ht
phi=lambda x:S.factor(phir+(phit-phir)*(x-r)/(t-r))
psi=lambda x:S.factor(psir+(psit-psir)*(x-r)/(t-r))


def main():
    eq(ht,sig*td)
    eq(6*(1-r)*(1-t)-lam,3*(r-1)*(2*t-r))
    td4,tr4,tt4,tw4=row([S.Integer(1),r,t,w],w,h,
                        lambda rest:phi(w)-lam*sum(rest))
    q=S.Poly(S.expand((tw4-psi(w))*h+hr*tr4+ht*tt4),h)
    e=S.Poly(S.expand(h-sig*td4),h)
    a,b=[S.factor(c) for c in e.all_coeffs()]
    q2,q1,q0=[S.factor(c) for c in q.all_coeffs()]
    eq(q2*b*b-q1*a*b+q0*a*a,
       w**3*(r-w)*(t-w)*(Q*w+r*t*(r+t))**2/
          (1200*(r-1)*(r-2*t)*(2*r-t)**2*(t-1)**2*(w-1)**2))
    wn=-r*t*(r+t)/Q
    hw=-r**3*t**3*(r+t)**2*(2*r-t)*(5*r*r-14*r*t+5*t*t)/(36*(r-1)*Q**4)
    eq(a.subs(w,wn),-3*r*t*(r+t)*P/
                      (10*(2*r-t)*(t-1)*(Q+r*t*(r+t))))
    eq((a*h+b).subs({w:wn,h:hw}),0)
    eq(tw4.subs({w:wn,h:hw}),0)
    print("exact delayed fourth: guarded resultant and ordinary pivot")

    # For P=0, preserve r as a symbolic coefficient. Nonzero denominators
    # are the original literal factors, not a formal specialization of r.
    p=z*z-3*z+1
    sub=lambda x:S.cancel(x.subs(t,r*z).subs(w,r*(1+z)))
    for expr in [a,b,q1+2*q2*hw,q0-q2*hw*hw,tw4.subs(h,hw)]:
        num,den=sub(expr).as_numer_denom()
        assert S.rem(num,p,z)==0 and S.gcd(den,p,z)==1
    den5=5*r*r*z*(z-2)*(z+1)*(r*z+r-1)
    eq(S.rem(S.cancel(den5*sub(q2)),p,z),
       -15*(r-1)*(4*r*z-r-z))
    assert S.rem(4*r*z-r-z-z*(r*(z+1)-1),p,z)==0
    print("exact delayed fourth: double-root exception with literal w−1 guard")

    gap=(phi(1)-lam*(r+t+w)-6*(1-r)*(1-t)*(1-w)).subs(w,wn)
    eq(gap.subs(t,r*z),
       (9*(r-1)*r**4/(5*(2*r-t)*Q)).subs(t,r*z)*
       (r*z*(z+1)*(3*z*z-7*z+3)+2*(z-1)**2*(z*z-4*z+1)))
    print("exact zero-mass return after fourth: one linear scale-ratio gate")


if __name__=="__main__":
    main()
