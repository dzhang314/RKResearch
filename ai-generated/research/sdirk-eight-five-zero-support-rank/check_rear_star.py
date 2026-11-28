#!/usr/bin/env python3
"""The earlier live-star rear controls also have nonzero second residual."""
from itertools import permutations
from math import lcm,isqrt
from flint import nmod_poly,fq_default_ctx,fq_default_poly_ctx
for p,gap in ((37,26),(269,156),(379,277)):
    assert all(p%d for d in range(2,isqrt(p)+1))
    deg=lcm(*(f.degree() for f,k in nmod_poly([1,-20,90,-140,70],p).factor()[1]))
    F=fq_default_ctx(p,deg,'t')
    R=fq_default_poly_ctx(F);X=R.gen()
    roots=[x for x,k in (70*X**4-140*X**3+90*X**2-20*X+1).roots()]
    assert len(roots)==4 and all(x!=0 for x in roots)
    vals=[]
    for x,y in permutations(roots,2):
        w=4*x-y
        if w not in roots or w in (x,y):continue
        v=(y-x)/x
        val=1+2*v-v*v
        assert val==gap and val!=0
        vals.append(val)
    assert len(vals)==2
    print(p,'both geometric rear-star branches have nonzero kappa',gap)
