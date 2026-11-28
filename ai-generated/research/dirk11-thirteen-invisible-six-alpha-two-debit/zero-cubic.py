#!/usr/bin/env python3
"""Exact tau-zero alpha=2 quintic-divisibility obstruction."""
from pathlib import Path
from runpy import run_path
from argparse import ArgumentParser
from fractions import Fraction
import sympy as S
p0=ArgumentParser()
p0.add_argument('--research',type=Path,default=Path(__file__).resolve().parent.parent)
q=p0.parse_args().research
A=run_path(str(q/'dirk11-thirteen-invisible-six-constant-exclusion/replay.py'))
B=run_path(str(q/'dirk11-thirteen-invisible-six-cubic-zero-five/replay.py'))
Ring,det,quot=(A[n]for n in ('Ring','det','quot'))
ev,cof,J4,J5,rat=(B[n]for n in ('ev','linear_cofactor','J4','J5','rational'))
F,G,dd=B['projection']()
a,b=B['a'],B['b']
def EE(p,u,var):
    acc=u.r.to(0)
    for c in S.Poly(p,var).all_coeffs():acc=acc*u+rat(c)
    return acc
def mul(f,g):
    ans=[f[0].r.to(0)]*(len(f)+len(g)-1)
    for i,c in enumerate(f):
        for j,d in enumerate(g):ans[i+j]+=c*d
    return ans
p=101
X=Ring('p',prime=p);K=Ring('a degree24',X,[X.to(rat(dd.nth(i)))for i in range(24)])
aa=K.gen();oo,zz=K.to(1),K.to(0)
coeff=lambda f,d:[EE(S.Poly(f,b).nth(i),aa,a)for i in range(d+1)]
c0,c1=cof(coeff(F,4),coeff(G,3),det)
bb=-c0/c1
lam=-J5(aa)/J4(aa)
qq=[(K.to(c)+lam*d)/132 for c,d in zip((-1,20,-120,300,-330,132),(1,-14,56,-84,42,0))]
U=quot(quot(qq,aa),bb)
hs=lambda x:x*J4(x)
Vv,Bb=1-aa,1-bb
R=B['refl'](U)
Q5=mul([-Vv,oo],[zz,*R])
IQ5=[zz,*(c/(i+1)for i,c in enumerate(Q5))]
IQ0=[zz,*(c/(i+1)for i,c in enumerate([zz,*R]))]
lam5=ev(IQ5,Vv)/hs(Vv)
R0=Ring('old reverse cubic',K,R[:-1]); Y=R0.gen()
M0=ev(IQ0[1:],Y)
M1=ev(IQ5[1:],Y)-R0.to(lam5)*J4(Y)
v=det(list(zip(M0.v,(Y*M0).v,M1.v)))
v.inv()
print('unit old quintic divisibility on whole degree24 field',p,flush=True)
