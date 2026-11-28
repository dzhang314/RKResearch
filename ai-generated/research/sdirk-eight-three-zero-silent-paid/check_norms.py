#!/usr/bin/env python3
from pair_field import K,a,b,o,normnum,minp,as_poly
from math import gcd,prod
import sympy as S

def strip(x):
    assert x
    for p in (2,3,5,7,13):
        while x%p==0:x//=p
    return x

def guard(obj):
    for c in obj.to_list():assert strip(int(c.denominator))==1

def chart(a,b):
    k=a+b-2;q=(a+b)*k-a*b+9*o/7
    r=lambda x:x*x+k*x+q
    j=lambda x:x**3/3+k*x*x/2+q*x
    jx=lambda x:x**4/4+k*x**3/3+q*x*x/2
    G=(j(o)-j(b))/r(b)
    D=j(a)-G*r(a);N=jx(a)-G*a*r(a)
    # Homogeneous earliest-silent anchor in P1.
    h=N**3/3+k*N*N*D/2+q*N*D*D-G*(N*N*D+k*N*D*D+q*D**3)
    def both(R,k,q):
        d=R+G*G;n=2*R-G*(2*G+k)
        x=G*(3*d-n)
        sg=R*(d*d+2*n*d-n*n)-(x*x+k*x*d+q*d*d)
        x=G*(d+2*n)
        tg=(R*(d*d+4*n*d-4*n*n)-(x*x+k*x*d+q*d*d))*(-2*d**3+n*d*d+4*n*n*d-n**3)+4*R*n*n*(3*n-2*d)*d*d
        qg=4*n**3-12*n*n*d+3*n*d*d+2*d**3
        return d,n,sg,tg,qg,x
    f0,f1,fs,ft,fq,fx=both(r(G),k,q)
    r0,r1,rs,rt,rq,rx=both(r(1-G),-2-k,1+k+q)
    pf=f0*N-fx*D;pr=(1-b)*r0-rx
    for v in (a,b,o/r(b),G,D,N,h,f0,f1,fs,ft,fq,pf,r0,r1,rs,rt,rq,pr):guard(v)
    n=normnum
    f=n(fs)*n(ft)*gcd(n(fq),n(pf))*gcd(n(f0),n(f1))
    rr=n(rs)*n(rt)*gcd(n(rq),n(pr))*gcd(n(r0),n(r1))
    return D,N,f,rr,h

x,y=S.symbols('x y')
P=x**4-2*x**3+S.Rational(9,7)*x*x-S.Rational(2,7)*x+S.Rational(1,70)
Q=y*y-y+x*x-x+S.Rational(2,7)
assert S.Poly(P.subs(x,y)-P-(y-x)*(y+x-1)*Q,x,y).is_zero
def guard_poly(expr):
    for coeff in S.Poly(expr,y,x,domain=S.QQ).coeffs():
        assert strip(int(S.denom(coeff)))==1
for c in minp.values():assert strip(int(c.denominator))==1
gb=S.groebner([P,Q],y,x,domain=S.QQ)
for basis in gb.polys:guard_poly(basis.as_expr())
for z,target in [(as_poly(a),x),(as_poly(b),y),(minp,0)]:
    test=z.as_expr().subs(S.Symbol('T'),x+2*y)-target
    qs,rem=gb.reduce(test)
    assert rem==0
    for q in qs:guard_poly(q)
D,N,f,r,h=chart(a,b)
assert D!=K.zero
assert strip(gcd(normnum(D),normnum(N)))==1
assert strip(gcd(f,r,normnum(h)))==1
D,N,f,r,h=chart(a,1-a)
assert D==K.zero
assert strip(gcd(r,normnum(N)))==19**2
print("nonmirror simultaneous supports absent; coordinate exception 13; mirror only 19")
