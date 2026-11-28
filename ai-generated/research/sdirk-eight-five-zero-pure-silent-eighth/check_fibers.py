#!/usr/bin/env python3
"""Complete gap and interior-node fibers, including the singular Cramer guard."""
from flint import nmod_poly,fq_default_ctx,fq_default_poly_ctx
from itertools import product,combinations
from math import lcm,isqrt
for p,which in ((17,1),(62753,2)):
    assert all(p%d for d in range(2,isqrt(p)+1))
    ps=([2,3,-12,4],[2,-1,-4,1])
    degree=lcm(*(f.degree() for cs in ps for f,m in nmod_poly(cs,p).factor()[1]))
    F=fq_default_ctx(p,2*degree,'a')
    R=fq_default_poly_ctx(F);T=R.gen();O=F.one();Z=F.zero()
    us=[u for u,e in (4*T**3-12*T*T+3*T+2).roots()]
    vs=[v for v,e in (T**3-4*T*T-T+2).roots()]
    assert len(us)==len(vs)==3
    def J(P):return R([Z]+[c/(i+1) for i,c in enumerate(P.coeffs())])
    raw=valid=0
    for u,v in product(us,vs):
        D=2+2*v+(u if which==2 else Z)
        a=1+2*u;h=D-1-v;s=D-1
        I=lambda P:sum((D**i*c/(i+1) for i,c in enumerate(P.coeffs())),Z)
        L=lambda t:70*t**4-140*D*t**3+90*D**2*t*t-20*D**3*t+D**4
        P=(T-a)*(T-h)*(T-s)
        m0,m1,m2,m3,m4=[I(P*T**j) for j in range(5)]
        H=m0*(m2*m4-m3*m3)-m1*(m1*m4-m2*m3)+m2*(m1*m3-m2*m2)
        if H!=0:continue
        raw+=1
        if p==62753:
            assert (u,v,D)==(55124,35190,0)
            assert m0==57172 and m1==m2==m3==m4==0
            continue # D=1/gamma cannot vanish; this is the only rank drop.
        assert u==16 and v*v+2*v-6==0
        assert D!=0 and L(a)!=0 and all(x!=y for x,y in combinations((a,h,s),2))
        delta=m0*m2-m1*m1
        assert delta==9
        k=(m1*m2-m0*m3)/delta;q=(m1*m3-m2*m2)/delta
        assert all(q*x+k*y+z==0 for x,y,z in ((m0,m1,m2),(m1,m2,m3),(m2,m3,m4)))
        zz=[z for z,e in (T*T+k*T+q).roots()]
        assert len(zz)==2 and O in zz and D+1 in zz
        assert all(z not in (a,h,s) for z in zz)
        r=(T-1)*(T-1-u);j0=J(r);j1=J(T*r)
        def gate(x):
            return 12*(L(a)*(a*(j0(x)-r(x))+x*r(x)-j1(x))-L(x)*(a*r(a)-j1(a)))
        assert gate(O)==2*v+2 and gate(O)!=0
        assert gate(D+1)==-6*v-6 and gate(D+1)!=0
        valid+=1
        print(p,'gap',u,v,'Cramer delta',delta,'inner clocks',zz,'gate values',gate(O),gate(D+1))
    assert (raw,valid)==((2,2) if p==17 else (1,0))
    print(p,'moment roots',raw,'nondegenerate before local gate',valid)
