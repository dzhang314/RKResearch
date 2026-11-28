#!/usr/bin/env python3
"""Exact clock field and finite-free all-branch gates for slope different from −1."""
import argparse
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
from runpy import run_path
import sympy as S

X,z,s,c0,c1,c2=S.symbols('X z s c0 c1 c2')
J4=lambda x:42*x**4-84*x**3+56*x*x-14*x+1
J5=lambda x:(2*x-1)*(66*x**4-132*x**3+84*x*x-18*x+1)
def rat(q):
    q=S.Rational(q); return Fraction(int(q.p),int(q.q))
def zp(p): return S.Poly(p,z,domain=S.QQ)
def ip(q):
    return S.Add(*(a*X**(i+1)/S.Integer(i+1) for (i,),a in S.Poly(q,X).terms()))
def ev(poly,x):
    a=x.r.to(0)
    for c in reversed(poly): a=a*x+c
    return a
def pm(q,A):
    if not isinstance(q,S.Poly): q=zp(q)
    return [A.to(rat(q.nth(i))) for i in range(q.degree()+1)] if not q.is_zero else [A.to(0)]
def prim(f): return [f[0].r.to(0)]+[a/(i+1) for i,a in enumerate(f)]
def mul(f,g):
    k=f[0].r; a=[k.to(0)]*(len(f)+len(g)-1)
    for i,b in enumerate(f):
        for j,c in enumerate(g): a[i+j]+=b*c
    return a
def scale(p,c): return [a*c for a in p]
def sumdiff(f,g,sign):
    k=f[0].r; o=k.to(0)
    return [(f[i] if i<len(f) else o)+sign*(g[i] if i<len(g) else o)
            for i in range(max(len(f),len(g)))]
def add(f,g): return sumdiff(f,g,1)
def sub(f,g): return sumdiff(f,g,-1)

def exact():
    m=X*X-(S.Rational(3,5)+2*s)*X+s
    F=S.cancel(ip(X*m)/X)
    T=S.cancel(ip(ip(X*m))/(X*(X-1)))
    A=S.Poly(S.rem(F,m,X),X); B=S.Poly(S.rem(T,m,X),X)
    assert S.expand(A.nth(1)*B.nth(0)-A.nth(0)*B.nth(1)-s*s*(5*s-1)/200)==0
    m=X*X-X+S.Rational(1,5)
    F=S.cancel(ip(X*m)/X)
    assert S.rem(F,m,X)==S.Rational(1,60)-X/30
    R=X**3+c2*X*X+c1*X+c0
    ar=S.Poly(S.rem(R,m,X),X)
    assert S.expand(5*(ar.nth(1)+2*ar.nth(0))-(2+3*c2+5*c1+10*c0))==0

    H,rem=S.div(J5(z*X)*J4(z)-J4(z*X)*J5(z),X-1,X)
    assert rem==0
    H=S.Poly(H,X,domain=S.QQ[z]); h=H.LC()
    assert S.expand(h-132*z**5*J4(z))==0
    d2=H.nth(3)+h*X; d1=H.nth(2)+X*d2; d0=H.nth(1)+X*d1
    G=S.Poly(2*h+3*d2+5*d1+10*d0,X,domain=S.QQ[z])
    D=zp(H.resultant(G))
    fac=D.factor_list()[1]
    assert sorted((p.degree(),n) for p,n in fac)==[(1,23),(4,4),(24,1)]
    assert next(p for p,n in fac if p.degree()==1).monic()==zp(z)
    assert next(p for p,n in fac if p.degree()==4).monic()==zp(J4(z)).monic()
    F24=next(p for p,n in fac if p.degree()==24)
    assert F24.is_irreducible and F24.LC()==170400029184
    f,g=H,G
    for j in (2,1):
        a,b=f.pdiv(g)
        assert f*g.LC()**(f.degree()-g.degree()+1)==a*g+b and b.degree()==j
        f,g=g,b
    g0,g1=(zp(g.nth(i)).rem(F24) for i in (0,1))
    assert S.gcd(g1,F24).is_one
    print("nonminus clock projection: normalized cubic pin, one exact degree24, normalized B unique linear ratio",flush=True)
    return H,G,F24,g0,g1

def run(research,prime,data):
    assert S.isprime(prime) and prime>11
    helper=research/'dirk11-thirteen-invisible-six-constant-exclusion'/'replay.py'
    assert sha256(helper.read_bytes()).hexdigest()==Path(__file__).with_name('ring.sha256').read_text().strip()
    lib=run_path(str(helper)); Ring,det=lib['Ring'],lib['det']
    H,G,F24,g0,g1=data
    F=Ring('prime field',prime=prime)
    F.to(rat(F24.LC())).inv()
    A=Ring('ordinary V degree-24',F,pm(F24.monic(),F)[:-1]); Z=A.gen()
    def pe(f): return ev(pm(f,A),Z)
    B=-pe(g0)/pe(g1)
    coeff=[pe(H.nth(i))/pe(H.LC()) for i in range(5)]
    assert ev(coeff,B)==ev([pe(G.nth(i)) for i in range(4)],B)==0
    d2=coeff[3]+B; d1=coeff[2]+B*d2; d0=coeff[1]+B*d1
    assert 2+3*d2+5*d1+10*d0==0
    de=1/(60*(d0-(1+d2)/5))
    lam=A.to(Fraction(1,4))-de; e=lam-5*de*d0; D=de/e
    de.inv(); (1+lam).inv()
    one,zero=A.to(1),A.to(0)
    m=[one/5,-one,one]; P=[zero,*m]; P0=[zero,d0,d1,d2,one]; P5=mul([-one,one],P0)
    old=Ring('any old label',A,P0[1:-1]); Y=old.gen()
    def oe(f): return ev(list(map(old.to,f)),Y)
    IP,IP0=prim(P),prim(P0)
    inv=oe(m).inv()
    W0=(oe(IP0[1:])*inv).v
    assert ev(W0,one)==-e*e/de
    K=add([e-lam,lam],scale(W0,D))
    ph=add(P,scale(P0,D)); iph=add(IP,scale(IP0,D))

    for name,x in [('any old completion or old slack',Y),('origin-clock slack',1/Z),('fifth-clock slack',B)]:
        q=lambda p:ev(list(map(x.r.to,p)),x)
        (x-1).inv()
        ((x-1)**2*q(W0)-x.r.to(ev(W0,one))*q(K)**2).inv()
        print(f"F{prime}: immediate {name} excluded by full scalar unit",flush=True)

    # The fourth numeric return has already paid Q5(1)=0 and its H coefficient.
    ZH=[zero,one,-14*Z,56*Z*Z,-84*Z**3,42*Z**4]
    I5=prim(P5); th=ev(I5,one)/ev(ZH,one)
    E=sub(I5,scale(ZH,th))
    assert ev(E,one)==0
    Qold=(oe(E[1:])*inv/(Y-1)).v
    QB=(B-1)*ev(Qold,B)
    t=B-1
    f=[-ev(ph,B),one]; g=[-ev(iph,B),ev(K,B)]; h=[ev(IP0,B),-ev(W0,B)]
    d1=[ev(E,B),-QB]
    # Fixed quadratic coefficient vectors in k_B, no nonzero diagonal assumed.
    A0=add(sub(scale(mul(f,h),t*t),scale(g,t*t*ev(P0,B))),
           scale(mul(g,g),ev(W0,one)))
    B0=sub(mul(d1,add(scale(f,t),g)),scale(g,t*ev(P5,B)))
    assert len(A0)==len(B0)==3
    mat=[[A0[0],zero,B0[0],zero],[A0[1],A0[0],B0[1],B0[0]],
         [A0[2],A0[1],B0[2],B0[1]],[zero,A0[2],zero,B0[2]]]
    det(mat).inv()
    print(f"F{prime}: consecutive fifth excluded by full fixed quadratic/quintic determinant",flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--research',type=Path,default=Path(__file__).resolve().parent.parent)
    p.add_argument('--prime',type=int,action='append')
    a=p.parse_args()
    data=exact()
    for prime in a.prime or [101]:
        run(a.research,prime,data)
