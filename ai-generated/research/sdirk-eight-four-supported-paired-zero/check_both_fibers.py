#!/usr/bin/env python3
"""Exact paired zero-third anchors in the full simultaneous splitting fields."""
from flint import nmod_poly,fq_default_ctx,fq_default_poly_ctx
from itertools import product
from math import isqrt,lcm
expected={
    267613:[('midpoint',168562,168562,133807,69511,198102,164747,241314)],
    4271:[],
    8150279:[],
    16397761:[],
    3517:[('other',338,338,1800,3435,82,2823,2937)],
}
for p,target in expected.items():
    assert all(p%d for d in range(2,isqrt(p)+1))
    L=nmod_poly([3,0,-30,0,35],p);Q=nmod_poly([2,3,-12,4],p)
    fac=[f.factor()[1] for f in (L,Q)]
    assert all(e==1 for q in fac for f,e in q)
    d=lcm(*(f.degree() for q in fac for f,e in q))
    F=fq_default_ctx(p,d,'w');R=fq_default_poly_ctx(F);X=R.gen()
    O=F.one();Z=F.zero()
    roots=[y for y,e in (35*X**4-30*X*X+3).roots()]
    gaps=[u for u,e in (4*X**3-12*X*X+3*X+2).roots()]
    assert len(roots)==4 and len(gaps)==3
    def I(P):
        return sum((c/(i+1) for i,c in enumerate(P.coeffs()) if i%2==0),Z)
    def J(P):
        q=R([Z]+[c/(2*(i+1)) for i,c in enumerate(P.coeffs())])
        return q-q(-O)
    def interp(xs,vs):
        r=R.zero()
        for i,y in enumerate(xs):
            q=R([vs[i]])
            for j,w in enumerate(xs):
                if i!=j:q=q*(X-w)/(y-w)
            r+=q
        return r
    k=lambda u:1+2*u-u*u
    out=[]
    for u,v in product(gaps,repeat=2):
        if k(u)==0 or k(v)==0:continue
        for mode in ('midpoint','other'):
            ell=Z if mode=='midpoint' else u+v
            if mode=='other' and (ell==0 or ell+2==0 or ell==u):continue
            gamma=O/(ell+2)
            a,b=(4*u-ell)/(ell+2),(ell-4*v)/(ell+2)
            if a not in roots or b not in roots or a==b:continue
            ss=2*gamma-1
            xs=[Z,u,-v] if mode=='midpoint' else [ss,-ss,(u-v)/(ell+2)]
            vs=[O,k(u),k(v)] if mode=='midpoint' else [O,k(u)/k(v),k(u)]
            if any(xs[i]==xs[j] for i in range(3) for j in range(i)):continue
            r=interp(xs,vs)
            if J(r)(a)!=gamma*r(a) or I(r)-J(r)(b)!=gamma*r(b):continue
            if mode=='other':r=u*r
            assert r[1]==0 and b==-a
            assert Z in xs
            rest=[y for y in xs if y!=0]
            assert len(rest)==2 and rest[0]==-rest[1] and r(rest[0])!=0
            yy=[y for y in roots if y not in (a,b)]
            w=6*O/7-a*a
            assert len(yy)==2 and yy[0]==-yy[1] and all(y*y==w for y in yy)
            r0,r2=r[0],r[2]
            pin=w*(r0+r2*w/3)**2-(2*gamma)**2*(r0+r2*w)**2
            assert pin!=0
            out.append((mode,*map(int,(u,v,gamma,a,b,w,pin))))
    assert out==target
    print(p,'simultaneous splitting degree',d,'anchored controls and nonzero pins',out)
