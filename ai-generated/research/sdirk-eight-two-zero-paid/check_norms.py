#!/usr/bin/env python3
from pair_field import K,a,b,o,minp,as_poly,normnum
from math import gcd,prod
import sympy as S

def guard(obj):
    for c in obj.to_list():
        d=int(c.denominator)
        for p in (2,3,5,7,13):
            while d%p==0:d//=p
        assert d==1,(c,d)
for v in (a,b):guard(v)

def chart(a,b):
    k=a+b-2;q=(a+b)*k-a*b+9*o/7
    r=lambda x:x*x+k*x+q
    j=lambda x:x**3/3+k*x*x/2+q*x
    jx=lambda x:x**4/4+k*x**3/3+q*x*x/2
    G=(j(o)-j(b))/r(b)
    D=j(a)-G*r(a);N=jx(a)-G*a*r(a)
    R=r(G);RR=r(1-G);kf=-2-k;qf=1+k+q
    fd=R+G*G;fn=2*R-G*(2*G+k)
    rd=RR+G*G;rn=2*RR-G*(2*G+kf)
    a0=N-G*D;b0=G*D
    kap=lambda u,d:d*d+2*u*d-u*u
    H=lambda u,d:-2*d**3+u*d*d+4*u*u*d-u**3
    def rst(x,d,k,q):return x*x+k*x*d+q*d*d
    def Sg(u,d,R,k,q):return R*kap(u,d)-rst(G*(3*d-u),d,k,q)
    def Tg(u,d,R,k,q):return (R*kap(2*u,d)-rst(G*(d+2*u),d,k,q))*H(u,d)+4*R*u*u*(3*u-2*d)*d*d
    fs=[a0,Sg(a0,b0,R,k,q),Tg(a0,b0,R,k,q),a0*fd-b0*(2*fd-fn),a0*fd-2*b0*fn,
        Sg(fn,fd,R,k,q),Tg(fn,fd,R,k,q)]
    rs=[Sg(rn,rd,RR,kf,qf),Tg(rn,rd,RR,kf,qf),(1-b)*rd-G*(rd+2*rn)]
    for e in (G,D,N,R,RR,fd,fn,rd,rn,*fs,*rs):guard(e)
    return D,N,fd,fn,rd,rn,fs,rs
if __name__=='__main__':
    x,y=S.symbols('x y')
    P=x**4-2*x**3+S.Rational(9,7)*x*x-S.Rational(2,7)*x+S.Rational(1,70)
    Q=y*y-y+x*x-x+S.Rational(2,7)
    mod=S.groebner([P,Q],y,x,domain=S.QQ)
    for z,R in [(a,x),(b,y)]:
        test=as_poly(z).as_expr().subs(S.Symbol('T'),x+2*y)-R
        assert mod.reduce(test)[1]==0
    assert mod.reduce(minp.as_expr().subs(S.Symbol('T'),x+2*y))[1]==0
    D,N,fd,fn,rd,rn,fs,rs=chart(a,b)
    nf=prod(normnum(f) for f in fs)*gcd(normnum(fd),normnum(fn))
    nr=prod(normnum(f) for f in rs)*gcd(normnum(rd),normnum(rn))
    rem=gcd(nf,nr)
    bad=gcd(normnum(D),normnum(N))
    def strip(x,pr):
        assert x
        for y in pr:
            while x%y==0:x//=y
        return x
    allowed=(2,3,5,7,13)
    assert strip(rem,allowed+(107,137,997,3137))==1
    assert strip(bad,allowed)==1
    d,n,*_=chart(a,1-a)
    assert d==K.zero
    n=normnum(n)
    assert strip(n,allowed+(19,137))==1
    print('all paid-characteristic candidates: 13,19,107,137,997,3137')
