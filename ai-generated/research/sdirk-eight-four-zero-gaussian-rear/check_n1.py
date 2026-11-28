#!/usr/bin/env python3
"""Complete canceled-clock rear controls and varying-residual front obstruction."""
from itertools import permutations
from flint import nmod_poly,fq_default_ctx,fq_default_poly_ctx
from math import lcm,isqrt
complete={13:(10,2,8),17:(3,1,8),103:(38,1,8),131:(34,2,16),7793:(2485,1,8)}
for p,(gamma,number,frontcount) in complete.items():
    assert all(p%d for d in range(2,isqrt(p)+1))
    ds=lcm(*(f.degree() for cs in ([3,0,-30,0,35],[-1,-2,1])
             for f,e in nmod_poly(cs,p).factor()[1]))
    F=fq_default_ctx(p,ds,'w');R=fq_default_poly_ctx(F);X=R.gen();O=F.one();Z=F.zero()
    J=lambda P:R([Z]+[a/(j+1) for j,a in enumerate(P.coeffs())])
    gs=[x for x,e in (35*X**4-30*X**2+3).roots()]
    ks=[x for x,e in (X**2-2*X-1).roots()]
    assert len(gs)==4 and len(ks)==2 and all(y not in (O,-O) for y in gs)
    ct=0;out=[]
    for y,z in permutations(gs,2):
        for v in ks:
            assert v!=0 and v!=-1
            for ph,b in (('arith',1+2*v),('star',3-v)):
                if b*(1+y)!=(1+v)*(1+z):continue
                ga=(1+y)/(2*(1+v));dd=1-ga
                assert ga==gamma and ga!=dd and 1-2*dd not in gs
                assert ph==('star' if number==2 else 'arith')
                out.append((y,z,v,ga,dd))
                xd=dd/ga
                h=xd-1
                for u,w,style in ((h,2-h,'S'),(h,2*h,'A'),(2-h,h,'S'),(h/2,h,'A')):
                    k=1+2*u-u*u
                    if u==0 or k==0:continue
                    if style=='S':
                        if u in (O,2*O):continue
                        r=Z
                    else:
                        H=-2+u+4*u*u-u**3
                        if H==0 or 3*u==2:continue
                        r=2*u*(3*u-2)/H
                    xs=[O,1+u,1+w];zs=[O/2,k/2,(1+2*w-w*w+2*r*u)/2]
                    if zs[2]==0:continue
                    assert all(s!=t for s,t in permutations(xs,2))
                    P=R.zero()
                    for i,t in enumerate(xs):
                        T=R.one()
                        for j,s in enumerate(xs):
                            if j!=i:T=T*(X-s)/(t-s)
                        P+=zs[i]*T
                    assert all(P(t)==z for t,z in zip(xs,zs))
                    for aa in gs:
                        if aa in (y,z):continue
                        a=(1+aa)/(2*ga)
                        D=P(a)-J(P)(a);N=a*P(a)-J(P*X)(a)
                        assert xd*D!=N
                        ct+=1
    assert len(out)==number and ct==frontcount
    if number==2:assert tuple(a**p for a in out[0])==out[1]
    print('n=1 canceled',p,'reflected centered pair, gap, gamma, d:',out,
          '; varying-residual first-zero exclusions:',ct)
