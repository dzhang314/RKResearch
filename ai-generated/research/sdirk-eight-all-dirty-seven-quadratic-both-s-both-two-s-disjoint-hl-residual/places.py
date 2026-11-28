"""Exact geometric residue arithmetic at certified lead-stable places."""
from flint import nmod_poly
def spec(P,p,H0,var=1):
    a=[0]*(P.degrees()[var]+1);hh=[pow(H0,i,p) for i in range(1+P.degrees()[0])]
    for ix,g in P.to_dict().items():
        a[ix[var]]=(a[ix[var]]+(int(g)%p)*hh[ix[0]])%p
    return nmod_poly(a,p)
def special_fb(P,p,h,a):
    u=[0]*(P.degrees()[2]+1);Hs=[pow(h,i,p) for i in range(P.degrees()[0]+1)]
    As=[pow(a,i,p) for i in range(P.degrees()[1]+1)]
    for (i,j,k),z in P.to_dict().items():u[k]=(u[k]+int(z)%p*Hs[i]*As[j])%p
    return nmod_poly(u,p)
def stable_common(rows,full):
    if not any(r.degree()==d and d>0 for r,d in zip(rows,full)):return None
    g=rows[0]
    for r in rows[1:]:g=g.gcd(r)
    return g
