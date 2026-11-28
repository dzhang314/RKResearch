#!/usr/bin/env python3
"""New monomial-old-fit cases for any alpha at least one, quadratic U."""
from argparse import ArgumentParser
from pathlib import Path
from fractions import Fraction
from runpy import run_path
import sympy as S
X,a,b=S.symbols("X a b")
J4=lambda x:42*x**4-84*x**3+56*x*x-14*x+1
J5=lambda x:(2*x-1)*(66*x**4-132*x**3+84*x*x-18*x+1)
H=lambda x:x*J4(x)
T=(S.Poly(J4(a)*J5(X)-J5(a)*J4(X),X).exquo(S.Poly(X-a,X)))
D=T.LC()
F=S.Poly(T.as_expr().subs(X,b),b)
C2=T.nth(3)+b*D
C1=T.nth(2)+b*C2
C0=T.nth(1)+b*C1
r0,r1,r2=-(D+C2+C1+C0),3*D+2*C2+C1,-(3*D+C2)
co,contact=S.Poly(12*r0**2*D**2 + 8*r0*r1*r2*D - 6*r0*r2**3 + r1*r1*r2*r2,b).prem(F).primitive()
assert S.Poly(co,a).monic()==S.Poly(J4(a)**3,a).monic()
assert contact.degree()==3
conds=[
 ('zero-mid',S.Poly(6*r0*D-5*r1*r2,b)),
 ('nonzero-contact',contact),
]
def rat(c):
    n,d=S.Rational(c).as_numer_denom()
    return Fraction(int(n),int(d))
def ee(q,x):
    acc=x.r.to(0)
    for c in S.Poly(q,a).all_coeffs():acc=acc*x+rat(c)
    return acc
def mul(f,g):
    ans=[f[0].r.to(0)]*(len(f)+len(g)-1)
    for i,u in enumerate(f):
        for j,v in enumerate(g):ans[i+j]+=u*v
    return ans
def add(f,g):
    if len(f)<len(g):return add(g,f)
    return [*(x+y for x,y in zip(f,g)),*f[len(g):]]
def neg(f):return [-c for c in f]
def prim(U):return [U[0].r.to(0),*(c/(i+1)for i,c in enumerate(U))]
def scale(U,c):return [x*c for x in U]
def certified(cand,k,G,prime,A,B):
    Ring,quot,det=(A[x]for x in ('Ring','quot','det'))
    ev,refl,lin=(B[x]for x in ('ev','refl','linear_cofactor'))
    K0=Ring('prime',prime=prime)
    if cand.degree()==1:
        K=K0;aa=K.to(-rat(cand.nth(0)/cand.nth(1)))
    else:
        cand=cand.monic()
        K=Ring('ordinary a',K0,[K0.to(rat(cand.nth(i)))for i in range(cand.degree())])
        aa=K.gen()
    def coeff(F):return [ee(F.nth(i),aa)for i in range(F.degree()+1)]
    if G.degree()==1:
        g0,g1=coeff(G)
    else:
        g0,g1=lin(coeff(F),coeff(G),det)
    bb=-g0/g1
    assert ev(coeff(F),bb)==0 and ev(coeff(G),bb)==0
    lam=-J5(aa)/J4(aa)
    H0,H1=H(aa),H(bb)
    z,o=K.to(0),K.to(1)
    T5=[(K.to(c)+lam*d)/132 for c,d in zip((-1,20,-120,300,-330,132),(1,-14,56,-84,42,0))]
    r3=quot(quot(T5,aa),bb)
    R=refl(r3); C0,C1,C2,_=R
    Y=Ring('old reverse C',K,R[:-1]).gen()
    q0,q1,q2=(Y.r.to(up)for up in (C0,C1,C2))
    a3=q0/q2
    if k=='zero-mid':
        assert 6*C0==5*C1*C2
        a2=Y.r.to(0)
    else:
        assert 12*C0**2+8*C0*C1*C2-6*C0*C2**3+C1*C1*C2*C2==0
        a2=(2*q0+q1*q2)/(q2*q2)
    Ur=J4(Y)/(Y*Y+a2*Y+a3)
    U=refl(Ur.v)
    W=Ring('quadratic carrier',K,[c/U[-1] for c in U[:-1]])
    XQ=W.gen()
    SA=mul([z,o],T5)
    Q=ev(SA,XQ)
    I5=prim(mul([z,-bb,o],U))
    r=ev(I5,bb)/H1
    Fb=add(I5,scale([z,*(K.to(i)for i in (1,-14,56,-84,42))],-r))
    m=J4(Y)/ev(U,1-Y)
    k0=Y*m
    P0=[z,*refl(r3)]
    w0=(ev(prim(P0),Y)/k0).v
    d=ev(Fb,aa)/(aa*(aa-bb)*ev(U,aa))
    V=1-aa
    ell=(ev(prim([z,*m.v]),Y)/k0).v
    assert ell[2]==0
    z0=-ell[0]/ell[1]
    assert ev(w0,z0)==0
    first=ev(mul([z0-o,o],Fb),XQ)
    cout=first.v[0]*Q.v[1]-first.v[1]*Q.v[0]
    cout.inv()
    print('unit α=1 hull on exact ordinary clock field',k,cand.degree(),prime,flush=True)
    if k=='zero-mid':return
    w=-w0[1]/w0[2]-z0
    proj=d*d*(ev(refl(r3),z0)*ev(U,1-w)-ev(refl(r3),w)*ev(U,1-z0))
    proj.inv()
    print('unit α=2 commutator on exact ordinary clock field',k,cand.degree(),prime,flush=True)
def run(src):
    AA=run_path(str(src/'dirk11-thirteen-invisible-six-constant-exclusion/replay.py'))
    BB=run_path(str(src/'dirk11-thirteen-invisible-six-cubic-zero-five/replay.py'))
    for k,G in conds:
        ff=S.Poly(S.resultant(F,G,b),a)
        f=S.factor_list(ff)[1]
        print('k',k,'raw factors',[(g.degree(),e,str(g.as_expr()) if g.degree()<8 else '') for g,e in f],flush=True)
        want=((4,5),(24,1)) if k=='zero-mid' else ((4,7),(48,1))
        assert sorted((q.degree(),e)for q,e in f)==list(want)
        assert next(q for q,e in f if q.degree()==4).monic()==S.Poly(J4(a),a).monic()
        c=next(q for q,e in f if q.degree()==want[1][0])
        certified(c,k,G,101,AA,BB)
if __name__=='__main__':
    pp=ArgumentParser()
    pp.add_argument('--research',type=Path,default=Path(__file__).resolve().parent.parent)
    run(pp.parse_args().research)
