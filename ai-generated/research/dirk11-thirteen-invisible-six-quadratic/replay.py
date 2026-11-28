#!/usr/bin/env python3
"""Exact arithmetic for the no-gap-four quadratic profile cases."""
import argparse, itertools
from math import isqrt
from fractions import Fraction as Q
from pathlib import Path
from runpy import run_path
import sympy as S

b,t,q,s,x=S.symbols("b t q s x")
U=x*x+s*x+t
H=x*(42*x**4-84*x**3+56*x*x-14*x+1)
ell=S.Rational(1,5)-q
mu=q/(42*b*t)
J4=lambda x:42*x**4-84*x**3+56*x*x-14*x+1
J5=lambda x:(2*x-1)*(66*x**4-132*x**3+84*x*x-18*x+1)
If=lambda f:S.integrate(f,x)-S.integrate(f,x).subs(x,0)
G=S.Poly(If(x*(x-b)*U)-(q/42)*H-x*(x-b)*U*(ell*x+mu),x)
SS=42*b*t*t*(S.Rational(3,10)+q)/q-14*t+t/b
assert S.cancel(G.nth(2).subs(s,SS))==0
assert G.nth(5)==G.nth(1)==G.nth(0)==0
pols=[S.Poly(S.cancel(G.nth(j).subs(s,SS)).as_numer_denom()[0],t).primitive()[1].as_expr() for j in (4,3)]
PB=S.Poly(J5(b),b,domain=S.QQ)
js=[[int(S.Poly(Jn(x),x).nth(i)) for i in range(6)] for Jn in (J4,J5)]
QE=-S.Rational(3,10)
exps=[S.Poly(f.subs(q,QE),t).clear_denoms()[1].primitive()[1].as_expr() for f in pols]
expseq=S.subresultants(*exps,t)
be=S.Poly(expseq[-1],b).clear_denoms()[1].primitive()[1]
assert be.degree()==9
assert be.eval(S.Rational(1,14))!=0
assert S.gcd(be,PB).degree()==0
lex=S.Poly(expseq[-2],t)
assert lex.degree()==1
seq=S.subresultants(*pols,t)
coef,fac=S.factor_list(seq[-1],q)
[(RG,mult)]=[(f,m) for f,m in fac if S.degree(f,q)==6]
assert mult==1
# Recompute the exact factor identity rather than relying on reported multiplicities.
assert S.cancel(seq[-1]/(b**4*q**5*(10*q+3)*RG)).is_number
ls=S.Poly(seq[-2],t)
assert ls.degree()==1
assert S.Poly(RG,q).nth(0)==111132*b**12
assert S.Poly(pols[0],t).nth(0)==-50*q**2
midfactor=900000*q**5+1350000*q**4-2801250*q**3+961625*q*q-53900*q-12348
assert S.expand(RG.subs(b,S.Rational(1,2))-(20*q-9)*midfactor/4096)==0
vals={b:S.Rational(1,2),q:S.Rational(9,20)}
tv=S.cancel(-ls.nth(0).subs(vals)/ls.nth(1).subs(vals))
assert ls.nth(1).subs(vals)!=0 and tv==S.Rational(1,7)
assert S.cancel(SS.subs(vals).subs(t,tv))==-1
assert S.Poly(midfactor,q).eval(S.Rational(9,20))!=0

def rat(c):
    n,d=S.Rational(c).as_numer_denom()
    return Q(int(n),int(d))

def peval(poly,v):
    z=v.r.to(0)
    for c in poly.all_coeffs():
        z=z*v+rat(c)
    return z

def take(f, ss, pp):
    p=S.Poly(f,b,q)
    return sum(ss**i*pp**j*rat(c) for (i,j),c in p.terms())

def marked(v,u,w,a,polyU,la,mu):
    ring=v.r
    rr=[v,u,w]
    h=lambda y:y*J4(y)
    yU=lambda y:polyU(1-y)
    scalar=v**3*yU(v)/(6*h(v))
    ks=[scalar*h(y)/yU(y) for y in rr+[a]]
    kv,ku,kw,ka=ks
    IP=lambda y:y**4/4-(u+v)*y**3/3+u*v*y*y/2
    aff=lambda y,l,r:((u-y)*l+(y-v)*r)/(u-v)
    m1,lm2=u*u/2,u**3/3+ku
    lv=(u*m1-lm2)/(v*(u-v))
    lu=(lm2-v*m1)/(u*(u-v))
    L=lambda y:u+v-aff(y,IP(v)/kv,IP(u)/ku)
    Lam=lambda y:aff(y,v/2,(lv*kv+lu*ku)/ku)
    mr=[w*w/2,w**3/3+kw,w**4/4+L(w)*kw]
    def lagrange_taps(nodes,m):
        out=[]
        for i,y in enumerate(nodes):
            zs=[r for j,r in enumerate(nodes) if i!=j]
            c=[ring.to(1)]; d=y
            for r in zs:
                c=[-r*c[0], *(c[j-1]-r*c[j] for j in range(1,len(c))), c[-1]]
                d=d*(y-r)
            out.append(sum(c0*m0 for c0,m0 in zip(c,m))/d)
        return out
    lw=lagrange_taps(rr,mr)
    vr=[v/2,ring.to(0),ring.to(0)]
    ur=[lv,lu,ring.to(0)]
    r3=sum(z*k for z,k in zip(lw,ks)) - Lam(w)*kw
    def quad(a,cs):
        return sum(f*(a-x)*(a-y)/((z-x)*(z-y)) for (z,x,y),f in
                   zip(((v,u,w),(u,v,w),(w,v,u)),cs))
    Q4=[(sum(z*r**4 for z,r in zip(row,rr))-c**5/5)/k
        for row,c,k in zip((vr,ur,lw),rr,ks)]
    M2=[sum(z*r*k for z,r,k in zip(row,rr,ks))/j for row,j in zip((vr,ur,lw),ks)]
    ma=[a*a/2,a**3/3+ka,a**4/4+L(a)*ka,a**5/5+quad(a,Q4)*ka]
    laa=lagrange_taps(rr+[a],ma)
    R=[laa[-1]-la*(1-a)-mu,r3,
       sum(z*k for z,k in zip(laa,ks))-Lam(a)*ka,
       sum(z*k*r for z,k,r in zip(laa,ks,rr+[a]))-quad(a,M2)*ka]
    return R

def terminal_remainder(a,b,s,t):
    R=a.r
    def mul(p,q):
        out=[R.to(0)]*(len(p)+len(q)-1)
        for i,x in enumerate(p):
            for j,y in enumerate(q):out[i+j]=out[i+j]+x*y
        return out
    def ev(p,z):
        r=z.r.to(0)
        for c in reversed(p):r=r*z+c
        return r
    def rem(p):
        p=list(p)
        for i in range(len(p)-1,1,-1):
            p[i-1]=p[i-1]-s*p[i]
            p[i-2]=p[i-2]-t*p[i]
        return p[:2]
    U=[t,s,R.to(1)]; Fa=mul([0,1],mul([-a,1],mul([-b,1],U)))
    Fa=[R.to(0),*(z/(i+1) for i,z in enumerate(Fa))]
    H=[R.to(j) for j in (0,1,-14,56,-84,42)]
    A,B=ev(Fa,a)/ev(H,a),ev(Fa,b)/ev(H,b)
    slope=(A-B)/(a-b)
    W=mul(H,[A-a*slope,slope])
    lam=-J5(b)/J4(b)
    P=[R.to(0),*[(R.to(j5)+lam*j4)/132 for j4,j5 in zip(*js)]]
    f0,f1=rem([i-j for i,j in zip(Fa,W)])
    q0,q1=rem(P)
    return f0*q1-f1*q0


def trailing_coeffs(base,bb):
    l=-J5(bb)/J4(bb)
    pl=[(base.to(J5c)+l*J4c)/132 for J4c,J5c in zip(*js)]
    return quot(pl,bb)

def example_exception(prime):
    r=Ring("F",prime=prime)
    m=r.to(int(be.LC())).inv()
    B=Ring("First forward clean",r,[int(be.nth(i))*m for i in range(9)])
    bb=B.gen()
    tt=-peval(S.Poly(lex.nth(0),b),bb)/peval(S.Poly(lex.nth(1),b),bb)
    qq=B.to(rat(QE))
    tt.inv();bb.inv()
    ss=tt/bb-14*tt
    ll=B.to(Q(1,2))
    mu=qq/(42*bb*tt)
    p4=trailing_coeffs(B,bb)
    V=Ring("v forward",B,p4[:-1])
    cv=V.gen()
    p3=quot([V.to(u) for u in p4],cv)
    X=Ring("u forward",V,p3[:-1])
    cu=X.gen()
    p2=quot([X.to(u) for u in p3],cu)
    W=Ring("w forward",X,p2[:-1])
    cw=W.gen()
    aa=-W.to(p4[-2])-W.to(cv)-W.to(cu)-cw
    ss,tt,ll,mu=W.to(ss),W.to(tt),W.to(ll),W.to(mu)
    v,u,w,a=[W.to(1)-W.to(y) for y in (cv,cu,cw,aa)]
    R=marked(v,u,w,a,lambda y:y*y+ss*y+tt,ll,mu)
    coefficients=(1,2,3,7)
    sum(e*i for e,i in zip(R,coefficients)).inv()
    print(f"q=-3/10: ranks 9,36,108,216 over p={prime}; verified inverse counts",
        [o.invs for o in (r,B,V,X,W)])

def example_lobatto(prime,generic=False):
    r=Ring("F",prime=prime)
    nodes=[j for j in range(prime) if J5(j)%prime==0]
    assert len(nodes)==5 and all(j not in (0,1) for j in nodes)
    if generic:
        assert prime==43 and 2 in nodes
        nodes_b=[2]
    else:
        assert prime==181
        nodes_b=nodes
        qb0=(Q(9,20).numerator*pow(Q(9,20).denominator,-1,prime))%prime
        qmod=S.Poly(midfactor,q,modulus=prime)
        assert qmod.eval(qb0)!=0
    for b0 in nodes_b:
        GQ=S.Poly(RG.subs(b,b0),q,domain=S.QQ)
        assert GQ.degree()==6
        lead=r.to(rat(GQ.LC())).inv()
        B=Ring("gamma coefficient",r,[lead*rat(GQ.nth(i)) for i in range(6)])
        qb=B.gen(); bb=B.to(b0)
        qb.inv();(10*qb+3).inv()
        tt=-take(ls.nth(0),bb,qb)/take(ls.nth(1),bb,qb)
        tt.inv()
        ss=42*bb*tt*tt*(Q(3,10)+qb)/qb-14*tt+tt/bb
        ll=Q(1,5)-qb
        mu=qb/(42*bb*tt)
        bad=0
        for vf,uf,wf,af in itertools.permutations(j for j in nodes if j!=b0):
            v,u,w,a=[B.to(1-y) for y in (vf,uf,wf,af)]
            Rs=marked(v,u,w,a,lambda y:y*y+ss*y+tt,ll,mu)
            Rs.append(terminal_remainder(1-a,bb,ss,tt))
            mod=S.Poly.from_list([1]+list(reversed([c.v for c in B.mod])),x,modulus=prime)
            for e in Rs:
                raw=S.Poly.from_list(list(reversed([c.v for c in e.v])),x,modulus=prime)
                g=S.gcd(mod,raw)
                mod=g
            if not generic and (2*b0-1)%prime==0:
                assert mod.monic()==S.Poly(x-qb0,x,modulus=prime)
                bad+=1
            else:
                assert mod.degree()==0
        print(f"p={prime}, b component {b0}: 24 orders, "
              f"{B.invs} distinct inverse checks, "
              f"{bad} rational-degree-one-only midpoint residues",flush=True)

if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("--mode",choices=["all","exceptional","generic","lobatto"],default="all")
    ap.add_argument("--arithmetic",type=Path,
        default=Path(__file__).resolve().parent.parent /
            "dirk11-thirteen-invisible-six-constant-exclusion" / "replay.py")
    args=ap.parse_args()
    for prime in (43,101,181):
        assert all(prime%d for d in range(2,isqrt(prime)+1))
    mod=run_path(str(args.arithmetic))
    Ring,quot=(mod[n] for n in ("Ring","quot"))
    print("Exact degrees 9 (exceptional b) and (12,6) (regular b,q).",flush=True)
    if args.mode in ("exceptional","all"): example_exception(101)
    if args.mode in ("generic","all"): example_lobatto(43,True)
    if args.mode in ("lobatto","all"): example_lobatto(181)
