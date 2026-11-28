#!/usr/bin/env python3
"""Exact fixed-clock exclusion of the first-gap cubic degree loss."""
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
    print('gamma5 prefix unit, rank 60',flush=True)
    def fit(deg):
        k=[zero,*(YY**deg*m).v]
        k=add(k,scale(P0,(vv**deg*kV-ev(k,vv))/ev(P0,vv)))
        return(ev(prim(k),YY)*kInv).v
    m0,m1=fit(0),fit(1)
    A=[m1[0],m1[1]-m0[0],m1[2]-m0[1],-m0[2]]
    # The cubic coefficient is zero from the true chart, not inferred from this residue.
    assert A[-1]==0
    A=A[:3]
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
    print('gamma3/gamma4 crossing unit, rank 120',flush=True)

num=6*V*(c2*s-c0)
den=(c2+8*V)*s-c0
E=S.expand(4*c1*s*den-num*(3*c0+c2*s))
G=S.expand(c0*num**2-(2*s*s+c1*s)*num*den+(3*c2*s*s-3*c0*s)*den**2)
Q=S.Poly(G,s).exquo(S.Poly(3*(c2*s-c0),s)).as_expr()
assert S.degree(E,s)==2 and S.degree(Q,s)==3
rr=S.factor_list(S.resultant(E,Q,s),(V,c0,c1,c2))[1]
assert len(rr)==3 and (c0,4) in rr and (V,4) in rr
K0=next(f for f,m in rr if f not in (c0,V))
assert S.degree(K0,V)==3
pk=S.Poly(K0,c0,c1,c2)
deg=pk.total_degree()
raw=S.Poly(sum(d*lead**(deg-i-j-k)*C0**i*C1**j*C2**k
              for (i,j,k),d in pk.terms()),V).prem(T4)
g,raw=raw.primitive()
assert 1<=raw.degree()<=3
bp=lambda h:S.Poly(h,B,domain=S.QQ).monic()
assert bp(g)==bp(j4(B)**6)
ff=S.factor_list(S.resultant(T4.as_expr(),raw.as_expr(),V),B)[1]
assert sorted((S.degree(f,B),k)for f,k in ff)==[(4,4),(60,1)]
assert bp(next(f for f,m in ff if m==4))==bp(j4(B))
fp=bp(next(f for f,m in ff if m==1))
print('Exact first-gap leader-loss projection: degree 60 after the live Jacobi factor',flush=True)

F=Ring('prime',prime=101)
K=Ring('fixed degree-60 clock',F,[F.to(rat(fp.nth(i)))for i in range(60)])
bb=K.gen()
pv=lambda h,n:[eval1(S.Poly(h,V).nth(i),bb,B)for i in range(n+1)]
a,b=cof(pv(T4.as_expr(),4),pv(raw.as_expr(),3),det)
vv=-a/b
lam=-j5(bb)/j4(bb)
T5=[(K.to(i)+lam*j)/132 for i,j in zip((-1,20,-120,300,-330,132),(1,-14,56,-84,42,0))]
R3=quot(quot(T5,bb),vv)
coords=(vv,*R3[:3])
cps=lambda t,n:[evalmult(S.Poly(S.Poly(t,s).nth(i),V,c0,c1,c2),coords)
                for i in range(n+1)]
a,b=cof(cps(Q,3),cps(E,2),det)
ss=-a/b
rr=ev(cps(num,1),ss)/ev(cps(den,1),ss)
print('V, s linear cofactor leaders and the Phi pivot are units',flush=True)
gaps(K,vv,ss,rr,T5,R3)
