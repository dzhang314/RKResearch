#!/usr/bin/env python3
"""Finite-free characteristic-zero unit closures for actual affine slope minus one."""
from argparse import ArgumentParser
from pathlib import Path
from runpy import run_path
from fractions import Fraction as Qf
import sympy as S

HERE=Path(__file__).resolve().parent
parser=ArgumentParser()
parser.add_argument("--arithmetic",type=Path,default=HERE.parent/"dirk11-thirteen-invisible-six-constant-exclusion/replay.py")
parser.add_argument("--old-pair",type=Path,default=HERE.parent/"dirk11-thirteen-invisible-six-cubic-zero-five/replay.py")
parser.add_argument("--old-mark",type=Path,default=HERE.parent/"dirk11-thirteen-invisible-six-cubic-zero-two/replay.py")
ns=parser.parse_args()
P=run_path(str(HERE/'project.py'))
B,V,c0,c1,c2,s=(P[k]for k in ('B','V','c0','c1','c2','s'))
T4,gV,R60=P['T4'].as_expr(),P['G'],P['f60']
G1,calc=P['F1'],P['SP']
CD,Zero5,Zero2=(run_path(str(q))for q in (ns.arithmetic,ns.old_pair,ns.old_mark))
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
def profile(prime):
    Z=Ring('prime',prime=prime)
    K=Ring('B degree60',Z,[Z.to(rational(R60.nth(i)))for i in range(60)])
    bb=K.gen()
    def polys(f,n):
        p=S.Poly(f,V)
        return [eval1(p.nth(i),bb,B)for i in range(n+1)]
    a0,a1=cof(polys(T4,4),polys(gV,3),det)
    vv=-a0/a1
    print('V pivot at',prime,flush=True)
    lam=-j5(bb)/j4(bb)
    J4=(1,-14,56,-84,42,0); J5=(-1,20,-120,300,-330,132)
    T=[(K.to(c)+lam*d)/132 for c,d in zip(J5,J4)]
    R3=quot(quot(T,bb),vv); x0,x1,x2=R3[:3]
    def coeff(P,deg):
        p=S.Poly(P,s)
        return [evalmult(S.Poly(p.nth(i),V,c0,c1,c2),(vv,x0,x1,x2))for i in range(deg+1)]
    a0,a1=cof(coeff(G1,3),coeff(calc,2),det)
    ss=-a0/a1
    rr=15*(x2*ss-x0)/(16*ss)
    print('s pivot',flush=True)
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
    print("Five-initial-ghost determinant is a unit",flush=True)
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
    print("Both multi-ghost-gap crossing reads are excluded by a unit",flush=True)
profile(101)
