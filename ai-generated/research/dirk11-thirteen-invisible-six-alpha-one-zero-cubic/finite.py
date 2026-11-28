#!/usr/bin/env python3
"""Exact lower-degree-profile support, with residue full-rank checks."""
from argparse import ArgumentParser
from fractions import Fraction
from math import comb
from flint import nmod_mat
from pathlib import Path
from runpy import run_path
import sympy as S
V,B,Y=S.symbols('V B Y')
def J4(x):return 42*x**4-84*x**3+56*x*x-14*x+1
def J5(x):return 132*x**5-330*x**4+300*x**3-120*x*x+20*x-1
T=S.Poly(J5(Y)*J4(V)-J5(V)*J4(Y),Y).exquo(S.Poly(Y-V,Y))
D=T.LC()
F=S.Poly(T.as_expr().subs(Y,B),B)
C2=T.nth(3)+B*D
C1=T.nth(2)+B*C2
C0=T.nth(1)+B*C1
P2=S.Poly(C2,B);P1=S.Poly(C1,B);Pc0=S.Poly(6*C0*D-5*C1*C2,B)
co,Pc=S.Poly(12*C0*C0*D*D+8*C0*C1*C2*D-6*C0*C2**3+C1*C1*C2*C2,B).prem(F).primitive()
assert S.Poly(co,V).monic()==S.Poly(J4(V)**3,V).monic()
assert Pc.degree()==3

def rat(c):
    t=S.Rational(c);return Fraction(int(t.p),int(t.q))
def ev(f,x):
    out=x.r.to(0)
    for c in reversed(f):out=out*x+c
    return out
def mul(f,g):
    out=[f[0].r.to(0)]*(len(f)+len(g)-1)
    for i,x in enumerate(f):
        for j,y in enumerate(g):out[i+j]+=x*y
    return out
def add(f,g):
    if len(f)<len(g):return add(g,f)
    return [*(a+b for a,b in zip(f,g)),*f[len(g):]]
def scale(f,h):return [h*x for x in f]
def prim(f):return [f[0].r.to(0),*(a/(i+1)for i,a in enumerate(f))]
def wedge(u,v):return u[0]*v[1]-u[1]*v[0]
def checked(k,res,mod,prime,lib):
    Ring,quot,det=(lib[q]for q in ('Ring','quot','det'))
    Fp=Ring('residue prime',prime=prime)
    base=Ring('ordinary V',Fp,[Fp.to(rat(mod.nth(i)))for i in range(mod.degree())])
    v=base.gen()
    def bz(p):return ev([rat(t)for t in reversed(S.Poly(p,V).all_coeffs())],v)
    def cfs(P):return [bz(P.nth(i))for i in range(P.degree()+1)]
    b0=-bz(res.nth(0))/bz(res.nth(1))
    assert ev(cfs(F),b0)==0
    lam=-J5(v)/J4(v)
    T5=[(base.to(c)+lam*d)/132 for c,d in zip((-1,20,-120,300,-330,132),(1,-14,56,-84,42,0))]
    rr=quot(quot(T5,v),b0)
    c0,c1,c2,_=rr
    current=base
    if k in ('m1','Fn-loss'):assert c2==0
    if k=='mY2':assert c1==0
    if k=='Fn-loss':
        s=-c1/6
        current=Ring('lost Fn D in r',base,[-3*s,4*s*s/c0])
        r=current.gen();s=current.to(s)
    v,b0=current.to(v),current.to(b0)
    R=list(map(current.to,rr))
    c0,c1,c2,_=R
    o,z=current.to(1),current.to(0)
    old=Ring('cubic old',current,R[:-1])
    y=old.gen()
    if k=='m1':mm=old.to(1)
    elif k=='mY2':mm=y*y
    elif k=='contact':
        assert 12*c0*c0+8*c0*c1*c2-6*c0*c2**3+c1*c1*c2*c2==0
        mm=y*y+old.to((2*c0+c1*c2)/(c2*c2))*y+old.to(c0/c2)
    elif k=='r0':
        assert 6*c0==5*c1*c2
        mm=y*y+old.to(c0/c2)
    else:
        assert k=='Fn-loss'; mm=y*y+old.to(r)*y+old.to(s)
    m=list(mm.v)
    c,d,e=m
    if k in ('m1','mY2'):p,q=z,o
    elif k=='r0':p,q=-5*c2,4*o
    else:p,q=d*e*c0,3*c*e*c2-4*c*d-3*e*e*c0
    a,b=o-v,o-b0
    def refl(f):
        return [(-1)**i*sum(comb(j,i)*f[j]for j in range(i,len(f)))for i in range(len(f))]
    U=scale(refl(R),-o)
    Jp=[current.to(t)for t in (1,-14,56,-84,42)]
    H=[z,*Jp]
    P0=[z,*R]
    def red(f):return list(ev([old.to(u)for u in f],y).v)
    k0=red(mul(mul([-o,o],mul([-v,o],[-b0,o])),Jp))
    k1=red([z,*k0])
    def dg(f):return det(list(zip(k0,k1,red(f))))
    Fs=prim(mul([z,-b,o],U))
    Kb=add(scale(Fs,ev(H,b)),scale(H,-ev(Fs,b)))
    E6=dg(mul(mul(m,[-p,q]),refl(Kb)))
    A0=prim(P0)[1:]
    l0=ev(A0,v)
    A=(p-v*q)*(l0*ev(m,v)-ev(R,v)*ev(prim([z,*m])[1:],v))-q*l0*ev(prim([z,*m])[1:],v)
    mark5=prim(mul([-v,o],P0))[1:]
    N5=red(add(scale(mark5,J4(v)),scale(Jp,-ev(mark5,v))))
    J=prim([z,*U])
    B2=ev(J,b)**2*det(list(zip(N5,red([z,*N5]),red(mul([-v,o],Jp)))))
    # Normalize the fitted old representative by the verified old inverse.
    Q0=list((ev([old.to(t)for t in N5],y)/mm).v)
    def hom(f,x,d):return sum(t*x**i*d**(len(f)-1-i)for i,t in enumerate(f))
    Qt=add(scale(Q0,hom(R,p,q)),scale(R,-q*hom(Q0,p,q)))
    dd=[q*q*Qt[1]+p*q*Qt[2]+p*p*Qt[3],q*q*Qt[2]+p*q*Qt[3],q*q*Qt[3]]
    jf=red(mul(mul(m,[-p,q]),refl(J)))
    qb1,qb0=dg(jf),dg([z,*jf])
    B1=hom(dd,qb0,qb1)
    def bas(r):
        if r is Fp:return [Fp.to(1)]
        return [r.to(a)*r.gen()**i for i in range(r.d)for a in bas(r.base)]
    def flat(x):
        if x.r is Fp:return [x.v]
        return sum((flat(j)for j in x.v),[])
    basis=bas(current)
    for beta,more in ((1,B1),(2,B2)):
        cs=(E6,A,more)
        row=nmod_mat(list(map(list,zip(*(flat(c*z)for c in cs for z in basis)))),prime).rank()
        print(k,'beta',beta,'ordinary degree',mod.degree(),'p',prime,'rank',row,'/',len(basis),flush=True)
        assert row==len(basis)

def main():
    p=ArgumentParser();p.add_argument('--research',type=Path,default=Path(__file__).resolve().parent.parent)
    p.add_argument('--prime',type=int,default=103)
    p.add_argument('--branch',choices=('m1','mY2','contact','Fn-loss','r0','all'),default='all')
    args=p.parse_args()
    assert S.isprime(args.prime) and args.prime>11
    lib=run_path(str(args.research/'dirk11-thirteen-invisible-six-constant-exclusion/replay.py'))
    for name,G,deg,exp in [('m1',P2,12,2),('mY2',P1,12,3),('contact',Pc,48,7),('Fn-loss',P2,12,2),('r0',Pc0,24,5)]:
        if args.branch not in ('all',name):continue
        zz=S.factor_list(S.Poly(S.resultant(F,G,B),V))[1]
        assert sorted((f.degree(),e)for f,e in zz)==[(4,exp),(deg,1)]
        assert next(f for f,e in zz if f.degree()==4).monic()==S.Poly(J4(V),V).monic()
        q=next(f for f,e in zz if f.degree()==deg).monic()
        seq=S.subresultants(F,G,B)
        s1=S.Poly(seq[-2],B)
        assert s1.degree()==1
        checked(name,s1,q,args.prime,lib)
if __name__=='__main__':main()
