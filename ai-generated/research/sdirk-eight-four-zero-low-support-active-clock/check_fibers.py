#!/usr/bin/env python3
"""Complete geometric reverse fibers and four-slot front chronology."""
from itertools import permutations
from math import lcm,isqrt
from flint import nmod_poly,fq_default_ctx,fq_default_poly_ctx

controls={
    1265639:(271082,143450,1122189,384363,881277,721186),
    1174307:(534271,925539,819552,61751,1112557,324894),
    263949107:(125965887,168410348,77082229,144027915,119921193,215819840)}
for p in controls:
    assert all(p%d for d in range(2,isqrt(p)+1))
    degree=lcm(*(f.degree() for cs in ([2,3,-12,4],[3,0,-30,0,35])
                             for f,e in nmod_poly(cs,p).factor()[1]))
    F=fq_default_ctx(p,degree,'w')
    R=fq_default_poly_ctx(F);X=R.gen();O=F.one();Z=F.zero()
    vs=[v for v,e in (4*X**3-12*X**2+3*X+2).roots()]
    gs=[y for y,e in (35*X**4-30*X**2+3).roots()]
    assert len(vs)==3 and len(gs)==4 and degree==2
    assert all(y not in (-O,O) for y in gs)
    def J(P):return R([Z]+[a/(j+1) for j,a in enumerate(P.coeffs())])

    admissible=[]; ct=[0,0,0]
    for v in vs:
        b=1+2*v
        if b==0:continue
        r=(X-1)*(X-1-v);P=1+(2-v)*(X-1)
        gate=r(b)*(J(P)-P)-P(b)*(J(r)-r)
        assert gate(b)==0
        for y,z in permutations(gs,2):
            h=b*(1+z)/(1+y)
            if gate(h)!=0:continue
            gamma=(1+y)/(2*b);d=1-gamma;e=1-gamma*(1+v)
            expect=controls[p]
            assert (v,y,z,gamma,d,e)==tuple(F(t) for t in expect)
            admissible.append(expect)
            kv=1+2*v-v*v
            assert kv!=0 and gamma!=d and gamma!=e
            # Positions 2,3,4 (zero-indexed here), since row 1 is silent.
            for slots in permutations([1,2,3],2):
                sd,se=slots
                j=min(slots); c=(d if sd==j else e)/gamma
                for phase in ('star','arithmetic'):
                    u=c-1 if j==1 else 3-c if phase=='star' else (c-1)/2
                    k=1+2*u-u*u
                    if u==0 or k==0:continue
                    if phase=='star':
                        if u in (O,2*O):continue
                        w=2-u;t=Z
                    else:
                        H=-2+u+4*u**2-u**3
                        if H==0 or 3*u==2:continue
                        w=2*u;t=2*u*(3*u-2)/H
                    xs=[O,1+u,1+w]
                    zs=[O/2,k/2,(1+2*w-w*w+2*t*u)/2]
                    if zs[-1]==0:continue
                    if any(xs[sl]!=c0/gamma for sl,c0 in zip(slots,(d,e)) if sl<3):continue
                    gd=zs[j]/(O if sd==j else kv)
                    if any(zs[sl]!=gd*k0 for sl,k0 in zip(slots,(O,kv)) if sl<3):continue
                    assert 3 in slots
                    ct[0]+=1
                    P=R.zero()
                    for i,t in enumerate(xs):
                        basis=R.one()
                        for n,s in enumerate(xs):
                            if n!=i:
                                assert t!=s
                                basis=basis*(X-s)/(t-s)
                        P+=zs[i]*basis
                    assert all(P(t)==s for t,s in zip(xs,zs))
                    for yy in gs:
                        if yy in (y,z):continue
                        a=(1-yy)/(2*gamma)
                        D=P(a)-J(P)(a)
                        N=a*P(a)-J(P*X)(a)
                        if D==0:
                            assert N!=0 # Do not suppress a hypothetical free case.
                            ct[1]+=1
                        else:
                            x4=(d if sd==3 else e)/gamma
                            assert x4*D!=N
                            ct[2]+=1
    assert admissible==[controls[p]]
    assert ct==([8,0,16] if p==1265639 else [8,4,12])
    print(p,'complete quadratic splitting field; reverse tuple',admissible[0],
          'front readouts / zero D with nonzero N / inconsistent live row 4:',ct)
