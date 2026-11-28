#!/usr/bin/env python3
"""Exact clock projection and fixed-B unit exclusion of the simultaneous affine pivot loss."""
from argparse import ArgumentParser
from pathlib import Path
from runpy import run_path
from fractions import Fraction as Qf
import sympy as S

HERE=Path(__file__).resolve().parent
cli=ArgumentParser()
cli.add_argument("--project",type=Path,default=HERE.parent/"dirk11-thirteen-invisible-six-cubic-live-fourth/project.py")
cli.add_argument("--arithmetic",type=Path,default=HERE.parent/"dirk11-thirteen-invisible-six-constant-exclusion/replay.py")
cli.add_argument("--old-pair",type=Path,default=HERE.parent/"dirk11-thirteen-invisible-six-cubic-zero-five/replay.py")
cli.add_argument("--old-mark",type=Path,default=HERE.parent/"dirk11-thirteen-invisible-six-cubic-zero-two/replay.py")
ns=cli.parse_args()
P=run_path(str(ns.project))
CD,Old5,Old2=(run_path(str(x))for x in (ns.arithmetic,ns.old_pair,ns.old_mark))
Ring,quot,det=(CD[x]for x in ('Ring','quot','det'))
ev,cof,refl,j4,j5=(Old5[x]for x in ('ev','linear_cofactor','refl','J4','J5'))
ringpoly=Old2['ringpoly']
B,V,c0,c1,c2,s,r=(P[k]for k in ('B','V','c0','c1','c2','s','r'))
D,F1,F2,F3=(P[k]for k in ('D','F1','F2','F3'))
T4,lead,C0,C1,C2=(P[k]for k in ('T4','lead','C0','C1','C2'))
aa=S.Poly(S.cancel(120*c0*P['A']),r)
A0,A1=aa.nth(0),aa.nth(1)

def cases():
    gg=S.factor_list(S.resultant(A0,A1,s),(V,c0,c1,c2))[1]
    assert sorted((S.degree(f,V),S.Poly(f,c0,c1,c2).total_degree(),k)for f,k in gg)==[
      (0,1,5),(0,3,1),(1,0,1),(1,2,1),(3,4,1),(3,4,1)]
    assert ((c0,5) in gg) and ((V,1) in gg)
    h36=next(f for f,k in gg if S.degree(f,V)==0 and f!=c0)
    h28=next(f for f,k in gg if S.degree(f,V)==1 and f!=V)
    h60=[f for f,k in gg if S.degree(f,V)==3]
    factors=lambda f:[q for q,m in S.factor_list(S.resultant(f,A1,s),(V,c0,c1,c2))[1]]
    hc=next(f for f in h60 if f in factors(F2))
    hm=next(f for f in h60 if f in factors(F1))
    assert hc!=hm
    for name,guard,degree,powC,powJ in (
      ('unit-F3',h36,36,3,6),('quadratic-r',h28,28,1,2),
      ('contact',hc,60,5,4),('old-slope',hm,60,6,4)):
        p=S.Poly(guard,c0,c1,c2);de=p.total_degree()
        q=S.Poly(sum(v*lead**(de-i-j-k)*C0**i*C1**j*C2**k
               for (i,j,k),v in p.terms()),V).prem(T4)
        cnt,q=q.primitive()
        assert 1<=q.degree()<=3
        bp=lambda t:S.Poly(t,B,domain=S.QQ).monic()
        assert bp(cnt)==bp(j4(B)**powC)
        ff=S.factor_list(S.resultant(T4.as_expr(),q.as_expr(),V),B)[1]
        assert sorted((S.degree(f,B),m)for f,m in ff)==[(4,powJ),(degree,1)]
        assert bp(next(f for f,k in ff if S.degree(f,B)==4))==bp(j4(B))
        yield name,q.as_expr(),bp(next(f for f,k in ff if S.degree(f,B)==degree))

def rat(c):
    a,b=S.Rational(c).as_numer_denom()
    return Qf(int(a),int(b))
def eval1(p,x,var):
    z=x.r.to(0)
    for c in S.Poly(p,var).all_coeffs():z=z*x+rat(c)
    return z
def evalmult(p,x):
    K=x[0].r; ans=K.to(0)
    for deg,c in p.terms():
        v=K.to(rat(c))
        for t,b in zip(deg,x):v*=b**t
        ans+=v
    return ans

def monic_rem(p,q):
    assert q[-1]==1
    p=list(p);n=len(q)-1
    for j in range(len(p)-1,n-1,-1):
        for i,c in enumerate(q[:-1]):p[j-n+i]-=p[j]*c
        p[j]=p[j].r.to(0)
    return p[:n]

def gaps(K,vv,ss,rr,T,R3):
    C=Ring('old',K,R3[:-1]); YY=C.gen()
    m=YY**2+C.to(rr)*YY+C.to(ss)
    kk=YY*m;kInv=kk.inv()
    print('old fitted k unit',flush=True)
    add,scale,mul,prim=ringpoly(K)
    zero,one=K.to(0),K.to(1)
    P=[zero,ss,rr,one];P0=[zero,*R3]
    I=prim(P);IP0=prim(P0)
    kV=ev(I,vv)/ev((ev(I,YY)*kInv).v,vv)
    h=lambda x:x*j4(x)
    U=(h(YY)*kInv).v
    U=add(U,scale(R3,(h(vv)/kV-ev(U,vv))/ev(R3,vv)))
    assert len(U)==4
    print('U reconstruction',flush=True)
    Ulead=U[-1].inv()
    Q=Ring('cubic carrier',K,[d*Ulead for d in U[:-1]])
    y=Q.gen();x=1-y
    Jrev=refl(prim([zero,*refl(U)]))
    J=ev(Jrev,y)
    C6=ev([zero,*refl(T)],x)
    dg=det(list(zip(J.v,(J*x).v,C6.v)))
    dg.inv()
    print('gamma5 prefix unit',flush=True)
    def fit(deg):
        k=[zero,*(YY**deg*m).v]
        k=add(k,scale(P0,(vv**deg*kV-ev(k,vv))/ev(P0,vv)))
        return(ev(prim(k),YY)*kInv).v
    m0,m1=fit(0),fit(1)
    A=[m1[0],m1[1]-m0[0],m1[2]-m0[1],-m0[2]]
    ai=A[-1].inv()
    R=Ring('first gap ghost',K,[d*ai for d in A[:-1]])
    z=R.gen()
    c11=R.to(m1[1])-z*R.to(m0[1]); c22=R.to(m1[2])-z*R.to(m0[2])
    w=-c11/c22-z
    print('first second ghost pivots',flush=True)
    IP5=prim(mul([-vv,one],P0))
    tw=(ev(IP5,YY)*kInv).v
    Teff=add(tw,scale(R3,(ev(IP5,vv)/kV-ev(tw,vv))/ev(R3,vv)))
    g0=ev(Teff,w)*ev(U,z)-ev(Teff,z)*ev(U,w)
    g0.inv()
    print('gamma3 and gamma4 crossing unit',flush=True)

def test(name,q,fp):
    F=Ring('prime',prime=101)
    d=fp.degree()
    K=Ring('B fixed algebra',F,[F.to(rat(fp.nth(i)))for i in range(d)])
    bb=K.gen()
    pv=lambda h,n:[eval1(S.Poly(h,V).nth(i),bb,B)for i in range(n+1)]
    m,n=cof(pv(T4.as_expr(),4),pv(q,3),det)
    vv=-m/n
    lam=-j5(bb)/j4(bb)
    T5=[(K.to(i)+lam*j)/132 for i,j in zip((-1,20,-120,300,-330,132),(1,-14,56,-84,42,0))]
    R3=quot(quot(T5,bb),vv)
    coords=(vv,*R3[:3])
    cps=lambda t,n:[evalmult(S.Poly(S.Poly(t,s).nth(i),V,c0,c1,c2),coords)
                    for i in range(n+1)]
    a,b=cps(A0,4),cps(A1,4)
    b=[u/b[-1]for u in b]
    m,n=cof(b,monic_rem(a,b),det)
    ss=-m/n
    print('fixed B,V,s pivots:',name,d,flush=True)
    if name=='unit-F3':
        ev(cps(F3,3),ss).inv()
        print('necessary F3 is a unit',flush=True)
        return
    if name=='quadratic-r':
        DD=S.Poly(D,r)
        K2=Ring('r quadratic',K,[ev(cps(DD.nth(i),2),ss)/R3[0]for i in range(2)])
        gaps(K2,K2.to(vv),K2.to(ss),K2.gen(),[K2.to(x)for x in T5],[K2.to(x)for x in R3])
        return
    bad=R3[2]-R3[0]/ss
    if name=='old-slope':bad=bad*Qf(15,16)
    rr=ss*(2*ss+R3[1])/R3[0]-bad
    gaps(K,vv,ss,rr,T5,R3)

for spec in cases():test(*spec)
