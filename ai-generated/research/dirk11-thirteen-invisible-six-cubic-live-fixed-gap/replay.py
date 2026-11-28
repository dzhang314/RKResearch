#!/usr/bin/env python3
"""Exact fixed B rank-12 and rank-36 joint-unit replays for the new genuine gap gates."""
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

def is_unit(x):
    try:
        x.inv()
        return True
    except (S.polys.polyerrors.NotInvertible,ValueError,ZeroDivisionError):
        return False

def gaps(prime,K,vv,ss,rr,T,R3):
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
    def fit(deg):
        k=[zero,*(YY**deg*m).v]
        k=add(k,scale(P0,(vv**deg*kV-ev(k,vv))/ev(P0,vv)))
        return(ev(prim(k),YY)*kInv).v
    m0,m1=fit(0),fit(1)
    A=[m1[0],m1[1]-m0[0],m1[2]-m0[1],-m0[2]]
    gates=[dg]
    for i,j in ((0,1),(0,2),(1,2)):
        d=J.v[i]*C6.v[j]-J.v[j]*C6.v[i]
        f=(J*x).v[i]*C6.v[j]-(J*x).v[j]*C6.v[i]
        val=sum(A[k]*(d-f)**k*d**(3-k) for k in range(4))
        gates.append(val)
    sum(gates).inv()
    if prime==101:
        assert not is_unit(dg)
    print('homogeneous first-gap and prefix joint unit; rank 12',flush=True)
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
    uz,uw=ev(U,z),ev(U,w)
    d,t=ev(m0,z),ev(m0,w)
    cmt=uz*(w-z-d)*t+uw*d*d
    assert not is_unit(g0)
    (g0+(2 if prime==101 else 1)*cmt).inv()
    print('quintic and retained commutator joint unit; rank 36',flush=True)


def sample(prime,bb):
 F=Ring('base',prime=prime)
 B0=F.to(bb)
 lam=-j5(B0)/j4(B0)
 t5=[(F.to(c)+lam*d)/132
     for c,d in zip((-1,20,-120,300,-330,132),(1,-14,56,-84,42,0))]
 t4=quot(t5,B0)
 K=Ring('generic fourth clock residue',F,t4[:-1]);v=K.gen()
 R3=quot([K.to(x)for x in t4],v);c=R3[:3]
 l=[evalmult(S.Poly(S.Poly(P['F3'],s).nth(i),V,c0,c1,c2),(v,*c))for i in range(4)]
 j=l[-1].inv()
 A=Ring('generic constant profile residue',K,[x*j for x in l[:-1]])
 ss=A.gen();vv=A.to(v);cj=[A.to(x)for x in c]
 D0=S.Poly(S.cancel(P['A']*c0),r)
 F0,F1=(evalmult(S.Poly(D0.nth(i),V,c0,c1,c2,s),(vv,*cj,ss))for i in range(2))
 rr=-F0/F1
 R3=[A.to(x)for x in R3];T=[A.to(x)for x in t5]
 gaps(prime,A,vv,ss,rr,T,R3)

for prime,b in ((101,79),(37,33)):
    print('Fixed ordinary clock residue',prime,b,flush=True)
    sample(prime,b)

def witness37():
    K=Ring('F37',prime=37)
    a,b,rr,ss,z,w=map(K.to,[27,5,22,5,3,23])
    zero,one=K.to(0),K.to(1)
    add,scale,mul,prim=ringpoly(K)
    aa,bb=1-a,1-b
    lam=-j5(bb)/j4(bb)
    T5=[(K.to(j)+lam*k)/132 for j,k in zip((-1,20,-120,300,-330,132),(1,-14,56,-84,42,0))]
    assert ev(T5,aa)==ev(T5,bb)==0
    R3=quot(quot(T5,bb),aa)
    C=Ring('old cubic',K,R3[:-1]);Y=C.gen()
    def rep(P):
     A=S.Poly(P,V,c0,c1,c2,s,r);ans=K.to(0)
     for deg,d in A.terms():
      n,k=S.Rational(d).as_numer_denom(); h=K.to(Qf(int(n),int(k)))
      for j,x in zip(deg,[aa,*R3[:3],ss,rr]):h*=x**j
      ans+=h
     return ans
    eta=S.Poly(S.cancel(120*c0*P['A']),r)
    print('old coefficients', [x.v for x in R3])
    print('F1 F2 F3 values', [rep(P[f]).v for f in ('F1','F2','F3')])
    assert rep(P['F3'])==0 and rep(P['D'])==0 and rep(eta.as_expr())==0
    print('affine pivot and discriminant',rep(eta.nth(1)).v,rep(S.discriminant(P['F3'],s)).v)
    assert rep(eta.nth(1))!=0 and rep(S.discriminant(P['F3'],s))!=0
    m=Y**2+C.to(rr)*Y+C.to(ss);kk=Y*m;iv=kk.inv()
    P0=[zero,*R3]
    P1=[zero,*(m.v)]
    ip=prim(P1);qq=ev(ip,aa)/ev((ev(ip,Y)*iv).v,aa)
    h=lambda t:t*j4(t)
    U0=(h(Y)*iv).v
    Ur=add(U0,scale(R3,(h(aa)/qq-ev(U0,aa))/ev(R3,aa)))
    assert len(Ur)==4 and Ur[-1]!=0
    assert ev(prim(P0),aa)==ev((ev(prim(P0),Y)*iv).v,aa)*qq
    assert ev(prim(ip),aa)==ev((ev(prim(ip),Y)*iv).v,aa)*qq
    def match(j):
        x=[zero,*(Y**j*m).v]
        return add(x,scale(P0,(aa**j*qq-ev(x,aa))/ev(P0,aa)))
    def fit(j):
        return (ev(prim(match(j)),Y)*iv).v
    u,v=fit(0),fit(1)
    uz,uw=ev(Ur,z),ev(Ur,w)
    d=ev(u,z); t=ev(u,w)
    assert ev(v,z)==z*d and ev(v,w)==z*t and z!=w and uz!=0 and uw!=0
    poly=prim(mul([-aa,one],P0))
    raw=(ev(poly,Y)*iv).v
    eff=add(raw,scale(R3,(ev(poly,aa)/qq-ev(raw,aa))/ev(R3,aa)))
    v0,v1=ev(eff,z),ev(eff,w)
    old=v1*uz-v0*uw
    new=uz*(w-z-d)*t+uw*d*d
    print('z,w,d,t,uz,uw,qeff(z),qeff(w)',[x.v for x in (z,w,d,t,uz,uw,v0,v1)])
    print('old crossing and actual retained commutator',old.v,new.v)
    assert old==0 and new==28

witness37()
