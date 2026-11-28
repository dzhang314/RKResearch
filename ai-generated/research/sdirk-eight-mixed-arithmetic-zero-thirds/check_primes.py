#!/usr/bin/env python3
"""Exact geometric finite closure of the A/Z characteristic support."""
import sys
from pathlib import Path
from prime_certificates import PRIMES,certify
from flint import nmod_poly,nmod_mpoly_ctx,fq_default_ctx,fq_default_poly_ctx
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'sdirk-eight-three-zero-169-paid-characteristics'))
from scalar_basis import OUT

def check(p):
    data=OUT['AZ'];var=data['var']
    C=nmod_mpoly_ctx.get((var,'q'),p)
    polys=[C.from_dict({(i,j):c%p for i,j,c in g if c%p}) for g in data['basis']]
    projection=nmod_poly([],p)
    for g in polys[1:]:
        h=polys[0].resultant(g,var)
        if h.is_zero():continue
        assert h.degrees()[0]==0
        a=[0]*(h.degrees()[1]+1)
        for (_,j),c in h.terms():a[j]=int(c)
        projection=projection.gcd(nmod_poly(a,p))
    assert not projection.is_zero()
    for h,e in projection.factor()[1]:
        F=fq_default_ctx(p,h.degree(),'u');R=fq_default_poly_ctx(F)
        q=R(list(map(int,h.coeffs()))).roots()[0][0]
        def eval(g):
            cs=[F.zero()]*(max(i for i,j,c in g)+1)
            for i,j,c in g:cs[i]+=(c%p)*q**j
            return R(cs)
        guard=eval(data['guard'])
        if guard.is_zero():continue
        z=R.zero()
        for g in data['basis']:z=z.gcd(eval(g))
        assert not z.is_zero()
        while z.degree()>0:
            bad=z.gcd(guard)
            if bad.degree()==0:break
            z,rem=divmod(z,bad)
            assert rem.is_zero()
        assert z.degree()==0,(p,h,z)
    print('A/Z complete geometric characteristic',p,'projection degree',projection.degree())
for p in PRIMES:
    assert certify(p)
    check(p)
