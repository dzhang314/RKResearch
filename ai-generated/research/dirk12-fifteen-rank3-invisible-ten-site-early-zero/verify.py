#!/usr/bin/env python3
"""Exact actual weighted scalar replay for the ten-site early-zero branch."""
import sympy as S

r,t,w,h,X = S.symbols("r t w h X")
R=S.Rational
f=S.factor
sigma=R(1,6)
g=-r*r*(r-2)/(6*(2*r-1))
p1=r*r*(r+1)/(3*(2*r-1))
pr=r*(4*r-5)/(6*(2*r-1))
D=r*r-4*r+1
P=r*r-3*r+1
W=5*r*r-14*r+5


def J(poly,x):
    return sum(c*x**(k[0]+1)/(k[0]+1) for k,c in S.Poly(poly,X).terms())


def eq(a,b):
    assert S.cancel(a-b)==0


def modzero(a):
    n,d=S.cancel(a).as_numer_denom()
    assert S.rem(n,P,r)==0 and S.gcd(d,P,r)==1


def interpolate(nodes,values,x):
    return f(sum(values[i]*S.prod(x-z for j,z in enumerate(nodes) if i!=j)/
                 S.prod(y-z for j,z in enumerate(nodes) if i!=j)
                 for i,y in enumerate(nodes)))


def phi(x):
    return r+1+(R(1,2)-r)*x


def chi(x):
    return interpolate([S.Integer(0),S.Integer(1),r],
        [r*r+r+1,R(9,5),(p1+r**4*pr-r**5/5)/g],x)


def psi(x):
    return interpolate([S.Integer(0),S.Integer(1),r],
        [(g-sigma)/(r-1),R(1,2),(sigma*p1+r*g*pr)/g],x)


def row(nodes,x,hx,mode):
    ans=[]
    for i,y in enumerate(nodes):
        rest=[z for j,z in enumerate(nodes) if i!=j]
        rr=(phi(x)-sum(rest))
        if mode=='quartic':
            rr=chi(x)-sum(rest)*phi(x)+sum(a*b for i,a in enumerate(rest)
                                                       for b in rest[i+1:])
        polis=X*S.prod(X-z for z in rest)
        den=y*S.prod(y-z for z in rest)
        ans.append(f((J(polis,x)+rr*hx)/den))
    return ans


def eliminant(E,F):
    a,b=S.Poly(S.expand(E),h).all_coeffs()
    q2,q1,q0=S.Poly(S.expand(F),h).all_coeffs()
    return q2*b*b-q1*a*b+q0*a*a,(a,b,q2,q1,q0)


def main():
    v=S.symbols("v")
    raw1=(r**3/6-v)/(r-1)
    rawr=r/2-raw1/r
    eq(raw1+r**3*rawr-r**4/4-phi(r)*v,
       r*(6*(2*r-1)*v+r*r*(r-2))/12)
    eq(raw1.subs(v,g),p1)
    eq(rawr.subs(v,g),pr)
    t1,tr,tt=row([S.Integer(1),r,t],t,h,'cubic')
    E=J(X*(X-1)*(X-r)*(X-t),t)+(chi(t)-(1+r+t)*phi(t)+(r+t+r*t))*h
    F=sigma*t1+r*g*tr+t*h*tt-psi(t)*h
    res,(a,b,q2,q1,q0)=eliminant(E,F)
    eq(res,t**5*(r-t)*(t-1)*(D*t+r*(r+1))**2/(200*(r-2)**2*(2*r-1)))
    tn=-r*(r+1)/D
    hn=-r*r*(r-2)*(r+1)*W/(6*D**3)
    eq(a.subs(t,tn),3*r*r*(r+1)**2*P/(10*(r-2)*D**2))
    eq(E.subs({t:tn,h:hn}),0)
    eq(tt.subs({t:tn,h:hn}),0)
    modzero(tn-(r+1))
    for val in [a,b,q1+2*q2*hn,q0-q2*hn*hn,tt.subs(h,hn)]:
        modzero(val.subs(t,r+1))
    eq(q2,(R(1,2)-r)*t/((t-1)*(t-r)))
    print("ten-site third: exact ratio and genuine zero diagonal, including double root")

    t1n,trn=[f(v.subs({t:tn,h:hn})) for v in [t1,tr]]
    z3=interpolate([S.Integer(0),S.Integer(1),r,tn],
       [(r*g-sigma)/(r-1),R(1,2),(sigma*p1+r*r*g*pr)/g,
        (sigma*t1n+r*r*g*trn)/hn],w)
    s1,sr,st,sw=row([S.Integer(1),r,tn,w],w,h,'quartic')
    F4=sigma*s1+r*g*sr+tn*hn*st+w*h*sw-psi(w)*h
    E4=(1-w)*sigma*s1+r*(r-w)*g*sr+tn*(tn-w)*hn*st-(z3-w*psi(w))*h
    res,_=eliminant(E4,F4)
    eq(res,r*w**5*(r+1)*(r-w)*(w-1)*(r*r-r+1)*(D*w+r*(r+1))**3/
       (200*(r-2)*(2*r-1)**2*D**2*W**2))
    print("ten-site fourth: exact nonzero fourth divided difference eliminant")


if __name__=="__main__":
    main()
