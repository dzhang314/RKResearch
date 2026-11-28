#!/usr/bin/env python3
"""Exact Fn denominator-loss case c2=0, c1+6s=0."""
from pathlib import Path
from argparse import ArgumentParser
from runpy import run_path
from fractions import Fraction
import sympy as S
P=run_path(str(Path(__file__).resolve().parent.parent/'dirk11-thirteen-invisible-six-alpha-two-debit/project.py'))
V,B,C2,Fc,J4,J5=(P[n] for n in ('V','B','C2','Fc','J4','J5'))
poly=S.Poly(C2,B)
factors=S.factor_list(S.Poly(S.resultant(Fc,poly,B),V))[1]
print('Fn degeneracy resultant factors',[(f.degree(),j)for f,j in factors],flush=True)
assert sorted((f.degree(),j)for f,j in factors)==[(4,2),(12,1)]
assert next(f for f,j in factors if f.degree()==4).monic()==S.Poly(J4(V),V).monic()
f=next(f for f,e in factors if f.degree()==12).monic()
def rat(c):
    n,d=S.Rational(c).as_numer_denom()
    return Fraction(int(n),int(d))
def ev1(F,v):
    a=v.r.to(0)
    for c in S.Poly(F,V).all_coeffs():a=a*v+rat(c)
    return a
def poly_mul(f,g):
    ans=[f[0].r.to(0)]*(len(f)+len(g)-1)
    for i,a in enumerate(f):
        for j,b in enumerate(g):ans[i+j]+=a*b
    return ans
def poly_prim(f):return [f[0].r.to(0),*(a/(i+1)for i,a in enumerate(f))]
def run(src,prime):
    R1=run_path(str(src/'dirk11-thirteen-invisible-six-constant-exclusion/replay.py'))
    R2=run_path(str(src/'dirk11-thirteen-invisible-six-cubic-zero-five/replay.py'))
    Ring,quot=R1['Ring'],R1['quot']; ev,refl=R2['ev'],R2['refl']
    F=Ring('prime',prime=prime)
    O=Ring('ordinary V',F,[F.to(rat(f.nth(i)))for i in range(12)])
    v=O.gen();b=-ev1(poly.nth(0),v)/ev1(poly.nth(1),v)
    assert ev([ev1(Fc.nth(i),v)for i in range(5)],b)==0
    lam=-J5(v)/J4(v)
    T5=[(O.to(u)+lam*w)/132 for u,w in zip((-1,20,-120,300,-330,132),(1,-14,56,-84,42,0))]
    RR=quot(quot(T5,v),b)
    c0,c1,c2,_=RR
    assert c2==0
    s=-c1/6
    R0=Ring('D quadratic in r',O,[-3*s,4*s*s/c0]);r=R0.gen()
    r3=[R0.to(a)for a in RR]
    Z,X=R0.to(0),R0.to(1)
    old=Ring('old cubic',R0,r3[:-1]); Y=old.gen()
    m=Y**2+Y*old.to(r)+old.to(s)
    m_inv=m.inv()
    U=(J4(Y)*m_inv).v
    IP0=poly_prim([Z,*r3])
    UQ=(ev(IP0[1:],Y)*m_inv).v
    vv=R0.to(v); bb=R0.to(b); a=1-vv; b=1-bb
    H=lambda x:x*J4(x)
    u_a=ev(U,vv)
    rev=ev(IP0[1:],vv)*u_a-J4(vv)*ev(UQ,vv)
    test=rev.inv()
    print('Fn loss: reverse pure read unit in the full rank-24 tower',prime,flush=True)
if __name__=='__main__':
    p=ArgumentParser()
    p.add_argument('--research',type=Path,default=Path(__file__).resolve().parent.parent)
    p.add_argument('--prime',type=int,default=103)
    q=p.parse_args()
    run(q.research,q.prime)
