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

def chart(a,b):
    k=a+b-2;q=(a+b)*k-a*b+9*o/7
    r=lambda x:x*x+k*x+q
    j=lambda x:x**3/3+k*x*x/2+q*x
    G=j(a)/r(a)
    Jr=j(o)
    la=2*j(a)-Jr
    lb=j(a)*r(b)+(j(b)-Jr)*r(a)
    def common(R,k,q):
        fd=R+G*G;fn=2*R-G*(2*G+k)
        x=G*(3*fd-fn)
        Sg=R*(fd*fd+2*fn*fd-fn*fn)-(x*x+k*x*fd+q*fd*fd)
        x=G*(fd+2*fn)
        Tg=(R*(fd*fd+4*fn*fd-4*fn*fn)-(x*x+k*x*fd+q*fd*fd))*(-2*fd**3+fn*fd*fd+4*fn*fn*fd-fn**3)+4*R*fn*fn*(3*fn-2*fd)*fd*fd
        Qg=4*fn**3-12*fn*fn*fd+3*fn*fd*fd+2*fd**3
        return fd,fn,Sg,Tg,Qg
    F=common(r(G),k,q)
    R=common(r(1-G),-2-k,1+k+q)
    f0,f1,fs,ft,fq=F
    r0,r1,rs,rt,rq=R
    pfa=a*f0-G*(f0+2*f1)
    pra=(1-a)*r0-G*(r0+2*r1)
    prb=(1-b)*r0-G*(r0+2*r1)
    rv0=r1-2*r0
    for v in (a,b,r(a),o/r(a),G,la,lb,*F,*R,pfa,pra,prb,rv0):guard(v)
    n=normnum
    return [n(fs),n(ft),gcd(n(fq),n(pfa)),gcd(n(f0),n(f1))], [n(la),n(lb)], [n(rs),n(rt),gcd(n(rq),n(pra)),gcd(n(rq),n(prb)),gcd(n(r0),n(r1)),n(rv0)]

def strip(x,pr=(2,3,5,7,13)):
    assert x
    for p in pr:
        while x%p==0:x//=p
    return x

if __name__=='__main__':
    x,y=S.symbols('x y')
    P=x**4-2*x**3+S.Rational(9,7)*x*x-S.Rational(2,7)*x+S.Rational(1,70)
    Q=y*y-y+x*x-x+S.Rational(2,7)
    assert S.Poly(P.subs(x,y)-P-(y-x)*(y+x-1)*Q,x,y).is_zero
    def guard_poly(expr):
        for coeff in S.Poly(expr,y,x,domain=S.QQ).coeffs():
            assert strip(int(S.denom(coeff)))==1
    for c in minp.values():assert strip(int(c.denominator))==1
    mod=S.groebner([P,Q],y,x,domain=S.QQ)
    for basis in mod.polys:guard_poly(basis.as_expr())
    for z,R in [(as_poly(a),x),(as_poly(b),y),(minp,0)]:
        test=z.as_expr().subs(S.Symbol('T'),x+2*y)-R
        quot,rem=mod.reduce(test)
        assert rem==0
        for mul in quot:guard_poly(mul)
    factors={19:4,139:2,227:2,233:4,241:2,509:2,739:2,10067:4,
             234847:4,1207117:4,1352963:2,127835437:2,3716728837183:2}
    assert all(S.isprime(p) for p in factors)
    assert S.isprime(107)
    for name,Y in [('mixed',b),('mirror',1-a)]:
        f,l,r=chart(a,Y)
        both=gcd(prod(f),prod(r))
        bothl=gcd(both,prod(l))
        rem=strip(bothl)
        assert rem==(107**2 if name=='mixed' else prod(p**e for p,e in factors.items()))
        print(name,'support',({107:2} if name=='mixed' else factors),flush=True)
    print('plus directly checked primitive-coordinate exception 13')
