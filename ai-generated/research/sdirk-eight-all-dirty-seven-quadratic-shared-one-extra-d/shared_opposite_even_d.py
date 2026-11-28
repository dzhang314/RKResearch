"""Shared clock D ends, distinct opposite extra D labels, centered-even graph."""
from shared_match_d import FF,d,X,shape
from itertools import combinations
import sympy as S

L=lambda t:t**4-FF(6)*t*t/7+FF(3)/35
S0=(21*d*d-15)/(35*d*d-21)
W=lambda t:t*t-S0
for f,r in combinations(('A2','A3','S'),2):
    df,sf,gf,gu=shape(d,f)
    dr,sr,gr,gv=shape(d,r)
    sr=-sr
    guard=[d,5*d*d-3,L(d),sf,sr,sf-d,sf+d,sr-d,sr+d,sf-sr,W(sf),W(sr)]+gu+gv
    assert all(guard)
    rho=gf/W(sf);lam=rho*W(sr)/gr
    assert lam and (lam-1)
    B=-4*L(0)/lam
    guard+=[lam,lam-1]
    Ap=L(d)/df-B*df
    Am=L(d)/(lam*dr)-B*lam*dr
    A0=-B*(1+lam)/2
    def C(x):return A0+x*(Ap-Am)/(2*d)+x*x*(Ap+Am-2*A0)/(2*d*d)+B*rho*W(x)
    e1=L(sf)-gf*C(sf)
    e2=L(sr)-lam*gr*C(sr)
    for p in (e1,e2):
        den=p.denom
        for x in guard:
            while (j:=den.gcd(x.numer)).degree()>0:den=den.exquo(j)
        assert den.degree()==0
    g=e1.numer.gcd(e2.numer)
    print(f,r,'raw degrees',e1.numer.degree(),e2.numer.degree(),g.degree(),flush=True)
    for v in guard:
        while (j:=g.gcd(v.numer)).degree()>0:g=g.exquo(j)
    print(f,r,'guarded gcd',g.degree(),flush=True)
    assert g.degree()==0
print('verified all three mixed centered-even opposite-label phases')
