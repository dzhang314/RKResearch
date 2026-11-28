#!/usr/bin/env python3
"""Exact lower-degree-profile support, with residue full-rank checks."""
from argparse import ArgumentParser
from fractions import Fraction
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
P2=S.Poly(C2,B);P1=S.Poly(C1,B)
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
    else:
        assert k=='Fn-loss'; mm=y*y+old.to(r)*y+old.to(s)
    A0=prim([z,*R])[1:]
    A1=prim([z,z,*R])[1:]
    inv=mm.inv()
    M=(J4(y)*inv).v
    W=(ev([old.to(c)for c in A0],y)*inv).v
    Q=(ev([old.to(c)for c in A1],y)*inv).v
    Jp=[current.to(k)for k in (1,-14,56,-84,42)]
    def divmonic(f):
        L=len(f)-1
        f=list(f)
        out=[z]*(L-2)
        for i in range(L,2,-1):
            t=f[i];out[i-3]=t
            for j in range(3):f[i-3+j]-=t*R[j]
        assert f[:3]==[z,z,z]
        return out
    d4=divmonic(add(mul(A0,M),scale(mul(W,Jp),-o)))
    d5=divmonic(add(mul(A1,M),scale(mul(Q,Jp),-o)))
    w0,w1,w2=W
    rrom=(c0*w2*w2-c2*w0*w2+w0*w1,c1*w2*w2-c2*w1*w2-w0*w2+w1*w1)
    pm=lambda P:[w2*P[i]-P[2]*W[i]for i in range(2)]
    qr,mr=pm(Q),pm(M)
    jv=J4(v);qv=ev(d4,v);lv=ev(A0,v);pv=ev(d5,v);mv=ev(A1,v)
    E=lv*(jv*w2*wedge(qr,mr)+pv*wedge(rrom,mr))-qv*(jv*wedge(qr,rrom)+mv*wedge(rrom,mr))
    E.inv()
    print(k,'ordinary degree',mod.degree(),'tower dimension',mod.degree()*(
        2 if k=='Fn-loss' else 1),'p',prime,'reverse eliminant unit',flush=True)

def main():
    p=ArgumentParser();p.add_argument('--research',type=Path,default=Path(__file__).resolve().parent.parent)
    p.add_argument('--prime',type=int,default=103)
    p.add_argument('--branch',choices=('m1','mY2','contact','Fn-loss','all'),default='all')
    args=p.parse_args()
    assert S.isprime(args.prime) and args.prime>11
    lib=run_path(str(args.research/'dirk11-thirteen-invisible-six-constant-exclusion/replay.py'))
    for name,G,deg,exp in [('m1',P2,12,2),('mY2',P1,12,3),('contact',Pc,48,7),('Fn-loss',P2,12,2)]:
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
