#!/usr/bin/env python3
"""Exact leading-drop clock projection and finite-free unit replay."""
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
B,V,c0,c1,c2,s,r=(P[i]for i in ('B','V','c0','c1','c2','s','r'))
T4=P['T4'];lead=P['lead']; C2=P['C2'];g=(4*V*lead+C2)
R=S.factor_list(S.resultant(T4.as_expr(),g,V),B)[1]
print('exact norm factors',[(S.degree(t,B),n)for t,n in R],flush=True)
assert sorted((S.degree(t,B),n)for t,n in R)==[(4,1),(16,1)]
guard=next(t for t,n in R if S.degree(t,B)==4)
assert S.Poly(guard,B,domain=S.QQ).monic()==S.Poly(P['j4'](B),B,domain=S.QQ).monic()
f16=S.Poly(next(t for t,n in R if S.degree(t,B)==16),B,domain=S.QQ).monic()
G0=S.Poly(S.cancel(P['A']*c0),r)

CD,Zero5,Zero2=(run_path(str(p))for p in (ns.arithmetic,ns.old_pair,ns.old_mark))
ringpoly=Zero2['ringpoly']; Ring,quot,det=CD['Ring'],CD['quot'],CD['det']
ev,cof,refl,j4,j5=tuple(Zero5[k]for k in ('ev','linear_cofactor','refl','J4','J5'))
def rational(c):
    n,d=S.Rational(c).as_numer_denom()
    return Qf(int(n),int(d))
def eval1(P,v,var):
    acc=v.r.to(0)
    for c in S.Poly(P,var).all_coeffs():acc=acc*v+rational(c)
    return acc
def evalmult(poly,coords):
    T=coords[0].r
    out=T.to(0)
    for ds,co in poly.terms():
        v=T.to(rational(co))
        for e,x in zip(ds,coords):v*=x**e
        out+=v
    return out
def reconstruct(BB, v):
    K=BB.r
    lam=-j5(BB)/j4(BB)
    J4=(1,-14,56,-84,42,0); J5=(-1,20,-120,300,-330,132)
    T=[(K.to(c)+lam*d)/132 for c,d in zip(J5,J4)]
    R3=quot(quot(T,BB),v); c=R3[:3]
    assert v*4+c[2]==0
    f=S.Poly(P['F3'],s)
    if evalmult(S.Poly(f.nth(3),V,c0,c1,c2),(v,*c))!=0:raise RuntimeError("specialized cubic leader")
    coeff=[evalmult(S.Poly(f.nth(i),V,c0,c1,c2),(v,*c))for i in range(3)]
    red=coeff[2].inv()
    J=Ring('quadratic s',K,[h*red for h in coeff[:2]])
    ss=J.gen();v=J.to(v);vls=(v,*(J.to(z)for z in c),ss)
    den=evalmult(S.Poly(G0.nth(1),V,c0,c1,c2,s),vls)
    rr=-evalmult(S.Poly(G0.nth(0),V,c0,c1,c2,s),vls)/den
    print('quadratic s and live profile pivot',flush=True)
    return J,v,ss,rr,[J.to(i)for i in T],[J.to(i)for i in R3]
def run(prime):
    F=Ring('prime',prime=prime)
    K=Ring('B degree16',F,[F.to(rational(f16.nth(i)))for i in range(16)])
    bb=K.gen()
    vv=-eval1(T4.nth(3),bb,B)/(5*eval1(lead,bb,B))
    K,vv,ss,rr,T,R3=reconstruct(bb,vv)
    probe(K,vv,ss,rr,T,R3)

def probe(K,vv,ss,rr,T,R3):
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
    print('Exact gamma5 determinant is a unit, rank 32',flush=True)
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
    print('Exact gamma3/gamma4 crossing is a unit, rank 96',flush=True)

run(103)
