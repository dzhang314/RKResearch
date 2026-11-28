#!/usr/bin/env python3
"""Exact finite root obstruction on the five-prefix zero-multiplier face."""
from argparse import ArgumentParser
from fractions import Fraction
from pathlib import Path
from runpy import run_path
from math import isqrt
import sympy as S
from zero_project import (X,a,b,c0,c1,c2,J4,J5,L,Y4,projections)
H=lambda x:x*J4(x)
assert len(projections)==1
_,g,content,FF,factors=projections[0]
assert sorted((q.degree(),e)for q,e in factors)==[(4,4),(60,1)]
assert S.Poly(content,a).monic()==S.Poly((a-1)**2*J4(a)**12,a).monic()
assert next(q for q,e in factors if q.degree()==4).monic()==S.Poly(J4(a),a).monic()
f=next(q for q,e in factors if q.degree()==60).monic()
def rational(c):
    n,d=S.Rational(c).as_numer_denom()
    return Fraction(int(n),int(d))
def e1(P,x,var):
    r=x.r; y=r.to(0)
    for v in S.Poly(P,var).all_coeffs():y=y*x+rational(v)
    return y
def split(f,x,quot,ev):
    P=quot(f,x)
    assert ev(f,x)==0
    return P
def prim(U):
    return [U[0].r.to(0),*(d/(i+1)for i,d in enumerate(U))]
def mul(f,g):
    z=[f[0].r.to(0)]*(len(f)+len(g)-1)
    for i,u in enumerate(f):
        for j,v in enumerate(g):z[i+j]+=u*v
    return z
def add(f,g):
    if len(f)<len(g):return add(g,f)
    return [*(u+v for u,v in zip(f,g)),*f[len(g):]]
def scale(f,x):return [u*x for u in f]
def main():
    root=Path(__file__).resolve().parent
    p=ArgumentParser()
    p.add_argument('--arithmetic',type=Path,default=root.parent/'dirk11-thirteen-invisible-six-constant-exclusion/replay.py')
    p.add_argument('--old-pair',type=Path,default=root.parent/'dirk11-thirteen-invisible-six-cubic-zero-five/replay.py')
    p.add_argument('--prime',type=int,default=101)
    o=p.parse_args()
    assert o.prime>11 and all(o.prime%d for d in range(2,isqrt(o.prime)+1))
    Ring,det,quot=(lambda d:tuple(d[n]for n in ('Ring','det','quot')))(run_path(str(o.arithmetic)))
    lc,ev,refl=(lambda d:tuple(d[n]for n in ('linear_cofactor','ev','refl')))(run_path(str(o.old_pair)))
    F=Ring('F',prime=o.prime)
    K=Ring('second forward clean a',F,[F.to(rational(f.nth(i)))for i in range(60)])
    aa=K.gen()
    def cs(p,n):return [e1(p.nth(i),aa,a)for i in range(n+1)]
    p0,p1=lc(cs(Y4,4),cs(g,3),det)
    bb=-p0/p1
    assert ev(cs(Y4,4),bb)==0 and ev(cs(g,3),bb)==0
    a0,b0=1-aa,1-bb
    la=-J5(aa)/J4(aa)
    coeffJ4=[1,-14,56,-84,42]
    t5=[(K.to(u)+la*v)/132
        for u,v in zip((-1,20,-120,300,-330,132),(*coeffJ4,0))]
    quo=split(t5,aa,quot,ev)
    U=split(quo,bb,quot,ev)
    Y3=refl(U)
    zz,oo=K.to(0),K.to(1)
    X3=Ring('forward U cubic',K,U[:-1]);xx=X3.gen()
    J=prim([zz,*U])
    Fb=prim(mul([zz,-bb,oo],U))
    Ji=ev(J,xx).inv()
    test=(ev(Fb,xx)-X3.to(ev(Fb,bb)/H(bb))*H(xx))*Ji
    assert test.v[2]==0
    Tip=Ring('old reflected cubic',K,Y3[:-1]); Y=Tip.gen()
    jrev=ev(J,1-Y)
    m0=J4(Y)*(Y-1)*(Y-Tip.to(a0))*(Y-Tip.to(b0))/jrev
    primitive_old=ev([zz,*(c/(i+2)for i,c in enumerate(Y3))],Y)
    signal=(primitive_old/m0).v[2]
    signal.inv()
    print('unweighted-alpha quartic residue is a unit in the degree-60 clock field',o.prime,flush=True)
    print('checked inversions',[(r.name,r.invs)for r in (F,K,X3,Tip)],flush=True)
if __name__=='__main__':main()
