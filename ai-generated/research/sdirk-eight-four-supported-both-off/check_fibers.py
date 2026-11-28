#!/usr/bin/env python3
"""Complete splitting-field anchors and order-independent odd-block pins."""
from flint import nmod_poly,fq_default_ctx,fq_default_poly_ctx
from itertools import permutations
from math import isqrt,lcm
CASES={
    277:(2,231,184,93,18,10),
    2014914997:(578011555,994173867,909066419,1105848578,731209713,999087437),
}
for p,target in CASES.items():
    assert all(p%d for d in range(2,isqrt(p)+1))
    qu=nmod_poly([1,0,-3,1],p)
    L=nmod_poly([3,0,-30,0,35],p)
    splits=[f.factor()[1] for f in (qu,L)]
    assert all(e==1 for group in splits for f,e in group)
    degree=lcm(*(f.degree() for group in splits for f,e in group))
    F=fq_default_ctx(p,degree,'w');R=fq_default_poly_ctx(F);X=R.gen()
    O=F.one()
    roots=[y for y,e in (35*X**4-30*X*X+3).roots()]
    gaps=[F(2)]+[u for u,e in (X**3-3*X*X+1).roots()]
    assert len(roots)==4 and len(gaps)==4
    out=[]
    for u in gaps:
        if u==0 or u==-1 or 1+2*u-u*u==0:
            continue
        gamma=O/(2*(1+u))
        r0=u*(1+2*u-u*u);r2=(u-2)*(u+1)**2
        r=lambda y:r0+r2*y*y
        j=lambda y:r2*(y**3+1)/6+r0*(y+1)/2
        I=r0+r2/3
        for a,b in permutations(roots,2):
            if j(a)!=gamma*r(a) or I-j(b)!=gamma*r(b):
                continue
            yy=[x for x in roots if x not in (a,b)]
            assert b==-a and len(yy)==2 and yy[1]==-yy[0]
            w=6*O/7-a*a
            assert all(y*y==w for y in yy)
            pin=w*(r0+r2*w/3)**2-(2*gamma)**2*(r0+r2*w)**2
            assert pin!=0
            out.append(tuple(map(int,(u,gamma,a,b,w,pin))))
    assert out==[target]
    print(p,'splitting degree',degree,'u,gamma,outer,inner square,pin:',target)
