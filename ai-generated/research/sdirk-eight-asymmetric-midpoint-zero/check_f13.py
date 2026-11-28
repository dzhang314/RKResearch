#!/usr/bin/env python3
"""Complete ordered anchor test over the nonsplit F13² zero-clock algebra."""
from flint import nmod_poly,fq_default_ctx,fq_default_poly_ctx
from itertools import permutations
p=13
for k in (1,-1):
    X=nmod_poly([0,1],p)
    P=X*(X*X-k*X-1)
    fac=P.factor()[1]
    assert sorted(f.degree() for f,e in fac)==[1,2] and all(e==1 for f,e in fac)
    F=fq_default_ctx(p,2,'u');Q=fq_default_poly_ctx(F)
    z=[y for y,e in Q([0,-1,-k,1]).roots()]
    assert len(z)==3
    one=F.one()
    r=lambda x:x*x+k*x-one
    J=lambda x:(x**3+one)/6+k*(x*x-one)/4-(x+one)/2
    R=lambda x:J(one)-J(x)
    assert all(r(y)!=0 for y in z)
    for y,x in permutations(z,2):
        assert J(y)*r(x)!=R(x)*r(y)
    print('k',k,'complete quadratic splitting roots',z,'ordered diagonal anchor pairs',0)
