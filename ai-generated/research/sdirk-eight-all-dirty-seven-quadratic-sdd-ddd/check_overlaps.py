"""One singleton endpoint: two literal overlapping D reads."""
from sympy.polys.fields import field
import sympy as S
from itertools import permutations,product,combinations
F,v=field('v',S.QQ)
def K(z):return 1+2*z-z*z
def D(z):return -2+z+4*z*z-z**3
def N(z):return (1+4*z-4*z*z)*D(z)+4*z*z*(3*z-2)
def residuals(mode,z):
    if mode=='S':return (K(z)/2,K(z)/2),[z,z-1,z-2,K(z)]
    return (K(z)/2,N(z)/(2*D(z))),[z,K(z),D(z),N(z),3*z-2]
def strip(p,gg):
    for g in gg:
       while p and (d:=p.gcd(g)).degree()>0:p=p.exquo(d)
    return p
HS,VS=S.symbols('H v')
EXPECTED={
 ('AA',1,2):(11,v*v), ('AA',1,3):(14,v*v),
 ('AS',1,2):(11,v), ('AS',1,3):(11,v-2),
 ('AS',2,3):(11,v-1), ('AS',3,2):(11,v-1),
 ('SA',1,2):(8,v), ('SA',2,1):(8,v), ('SA',1,3):(11,v),
 ('SA',3,1):(11,v), ('SA',2,3):(11,v), ('SA',3,2):(11,v),
 ('SS',1,2):(8,v*(v-2)), ('SS',2,1):(8,v*(v-2)),
 ('SS',1,3):(8,v*(v-2)), ('SS',3,1):(8,v*(v-2))
}
def run():
    visited=set()
    ordinary=parity=0
    for ff,rr in product('AS',repeat=2):
        ns=[HS,HS-VS,HS-2*VS] if rr=='A' else [HS,HS-VS,HS+VS-2]
        for i,j in permutations(range(3),2):
            rel=ns[j]-2*ns[i] if ff=='A' else ns[j]+ns[i]-2
            hp,=S.solve(rel,HS)
            H=F.from_expr(hp)
            cc=[F.from_expr(z.subs(HS,hp)) for z in ns]
            m=1+H/2;t=[z-H/2 for z in cc]
            s=[H,m]+cc+[x-y for x,y in combinations(cc,2)]
            p=t+[x+y for x,y in combinations(t,2)]
            if not all(s):
                ordinary+=1;continue
            if not all(p):
                parity+=1;continue
            L3=[z**3-3*m*m*z/5 for z in t]
            L4=[z**4-6*m*m*z*z/7+3*m**4/35 for z in t]
            u=cc[i]
            (f2,f3),fg=residuals(ff,u)
            (r2,r3),rg=residuals(rr,v)
            gs=s+p+L4+fg+rg+[u-2]
            assert all(gs)
            rg=[F.one/2,r2,r3]
            leg=(L3[1]/L4[1]-L3[0]/L4[0])*(cc[2]-cc[0])-(L3[2]/L4[2]-L3[0]/L4[0])*(cc[1]-cc[0])
            fit=L4[i]*f3*rg[j]-L4[j]*f2*rg[i]
            guards=[q.numer for q in gs]+[q.denom for q in gs]
            assert all(strip(g.denom,guards).degree()==0 for g in [leg,fit])
            g=leg.numer.gcd(fit.numer).monic()
            G=strip(g,guards)
            h=ff+rr,i+1,j+1
            ex,fail=EXPECTED[h]
            assert leg.numer.degree()==12 and fit.numer.degree()==ex
            assert g==fail.numer and G.degree()==0
            # Every nonconstant factor is known to be a literal reverse guard.
            assert strip(g,[z.numer for z in residuals(rr,v)[1]]).degree()==0
            assert h not in visited
            visited.add(h)
            print(h,'collinearity degree',12,'overlap degree',ex,'gcd',g,flush=True)
    assert visited==set(EXPECTED) and ordinary==2 and parity==6
    print('all sixteen literal placements excluded; eight clocks-only losses')
if __name__=='__main__':run()
