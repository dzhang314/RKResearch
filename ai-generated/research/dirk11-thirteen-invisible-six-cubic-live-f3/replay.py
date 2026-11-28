#!/usr/bin/env python3
"""Exact elimination of the two auxiliary cubic factors unless F3 also vanishes."""
from argparse import ArgumentParser
from fractions import Fraction as Q
from pathlib import Path
from runpy import run_path
import sympy as S

HERE=Path(__file__).resolve().parent
cli=ArgumentParser()
cli.add_argument("--project",type=Path,default=HERE.parent/"dirk11-thirteen-invisible-six-cubic-live-fourth/project.py")
cli.add_argument("--old-pair",type=Path,default=HERE.parent/"dirk11-thirteen-invisible-six-cubic-zero-five/replay.py")
cli.add_argument("--arithmetic",type=Path,default=HERE.parent/"dirk11-thirteen-invisible-six-constant-exclusion/replay.py")
ns=cli.parse_args()
P=run_path(str(ns.project))
B,V,c0,c1,c2,s,r=(P[i]for i in ('B','V','c0','c1','c2','s','r'))
F1,F2,D,A=(P[i]for i in ('F1','F2','D','A'))
Z5=run_path(str(ns.old_pair)); RR=run_path(str(ns.arithmetic))
Ring,quot,det=(RR[k] for k in ('Ring','quot','det'))
cof,j4,j5,ev=(Z5[k] for k in ('linear_cofactor','J4','J5','ev'))

# Both candidates here are literal roots of the necessary exact cofactor.
rc=c2-c0/s
for f,root in ((F1,15*rc/16),(F2,rc)):
    for q in (D,A):
        num,den=S.cancel(q.subs(r,root)).as_numer_denom()
        assert all(v in (c0,s) for v,_ in S.factor_list(den,(c0,s))[1])
        assert S.rem(num,f,s)==0
print("Exact contact and slope-root identities passed",flush=True)

DP=S.factor_list(S.discriminant(F1,s),(c0,c1,c2))[1]
assert sorted((S.Poly(f,c0,c1,c2).total_degree(),k)for f,k in DP)==[(1,2),(4,1)]
assert any(f==c0 and k==2 for f,k in DP)
W=S.Poly(next(f for f,k in DP if k==1),c0,c1,c2)
T4,lead,C0,C1,C2=(P[k]for k in ('T4','lead','C0','C1','C2'))
UU=S.Poly(sum(co*lead**(4-i-j-k)*C0**i*C1**j*C2**k
              for (i,j,k),co in W.terms()),V).prem(T4)
assert UU.degree()==3
g,h=UU.primitive()
assert S.Poly(g,B,domain=S.QQ).monic()==S.Poly(j4(B)**3,B,domain=S.QQ).monic()
ff=S.factor_list(S.resultant(T4.as_expr(),h.as_expr(),V),B)[1]
assert sorted((S.degree(f,B),k)for f,k in ff)==[(4,7),(48,1)]
assert S.Poly(next(f for f,k in ff if k==7),B,domain=S.QQ).monic()==S.Poly(j4(B),B,domain=S.QQ).monic()
f48=S.Poly(next(f for f,k in ff if k==1),B,domain=S.QQ).monic()
print("Repeated F1 ordinary clock degree 48 (after Jacobi guard)",flush=True)

def rat(q):
    n,d=S.Rational(q).as_numer_denom()
    return Q(int(n),int(d))
def ev1(P,x,var):
    a=x.r.to(0)
    for k in S.Poly(P,var).all_coeffs():a=a*x+rat(k)
    return a
def ev4(P,l):
    p=S.Poly(P,V,c0,c1,c2);Z=l[0].r;o=Z.to(0)
    for ns,a in p.terms():
        prod=Z.to(rat(a))
        for q,n in zip(l,ns):prod*=q**n
        o+=prod
    return o

prime=101
F=Ring('prime',prime=prime)
K=Ring('B degree 48',F,[F.to(rat(f48.nth(i)))for i in range(48)])
b=K.gen()
cs=lambda p,n:[ev1(S.Poly(p,V).nth(j),b,B)for j in range(n+1)]
l,u=cof(cs(T4.as_expr(),4),cs(h.as_expr(),3),det)
v=-l/u
lam=-j5(b)/j4(b)
T=[(K.to(c)+lam*d)/132
   for c,d in zip((-1,20,-120,300,-330,132),(1,-14,56,-84,42,0))]
R3=quot(quot(T,b),v)
l=(v,*R3[:3])
css=lambda p,n:[ev4(S.Poly(p,s).nth(i),l)for i in range(n+1)]
t,u=cof(css(F1,3),css(F1.diff(s),2),det)
ss=-t/u
A0=S.Poly(S.cancel(A*c0),r).nth(1)
ev(css(A0,S.degree(A0,s)),ss).inv()
print("Both cofactor pivots and the alternate-profile affine leader are units modulo 101.",flush=True)
