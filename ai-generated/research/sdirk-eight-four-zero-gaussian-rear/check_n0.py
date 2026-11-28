#!/usr/bin/env python3
"""Complete n=0 geometric rear census; these are necessary controls only."""
from flint import nmod_poly,fq_default_ctx,fq_default_poly_ctx
from math import lcm,isqrt
from itertools import permutations
cases={397:(162,[218]),487:(144,[344]),69877:(46321,[58162]),
       37:(28,None),269:(212,[252,58]),379:(212,[168,301])}
for p,(gamma,seconds) in cases.items():
    assert all(p%d for d in range(2,isqrt(p)+1))
    f=[1,-20,90,-140,70]
    degree=lcm(*(x.degree() for x,k in nmod_poly(f,p).factor()[1]))
    F=fq_default_ctx(p,degree,'u')
    R=fq_default_poly_ctx(F); X=R.gen()
    roots=[x for x,k in (70*X**4-140*X**3+90*X**2-20*X+1).roots()]
    assert len(roots)==4 and all(x!=0 for x in roots)
    out=[]
    for x,y in permutations(roots,2):
        v=(y-x)/x
        if p in (397,487,69877):
            if -2+v+4*v*v-v**3==0:out.append((x,y,2*y-x))
        else:
            z=4*x-y
            if z in roots and z not in (x,y):out.append((x,y,z))
    assert out and all(x==gamma for x,y,z in out)
    if seconds is None:
        assert degree==2 and len(out)==2 and out[0][1]**p==out[1][1]
    else:
        assert sorted(int(y) for x,y,z in out)==sorted(seconds)
    print('n=0',p,'degree',degree,'first three reflected clocks',out)
