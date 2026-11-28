"""Exact oriented factor and exact true-nonzero fourth support."""
from arith67_cover import oriented_mod
from arith67_fibers import all_mod
from arith67_model import model
from arith67_norm_cover import source
from arith_star_fibers import gpoly,modgamma
from check_star_family import F as ExField
from quadratic_poly import E
from paired_proposals import recover,fast_guard
from regular_star_projection import Co
from star4_actual_fifth import Bfield,trim,sc
from flint import fmpq_poly,fmpz_poly
from collections import Counter

pr=65537;tt=2040

def ration(P):
    A=fmpq_poly(P);return E(A*(1/A[A.degree()]))

def exact_orientation(M,d):
    n=M.degree()
    assert 0<d<=n
    if d==n:return M
    def trial(p,t):
        G=modgamma(M,p,t).gcd(oriented_mod(p,t))
        return [int(G[i]) for i in range(d)] if G.degree()==d else []
    def verify(A,B):
        S=E(fmpq_poly([*A,1]),fmpq_poly(B))
        if M%S:return None
        T=M.exact(S)
        U=modgamma(T,pr,tt);assert U.degree()==T.degree() and U.leading_coefficient()==1
        if U.gcd(oriented_mod(pr,tt)).degree():return None
        return S
    V=recover(d,trial,verify,('arith67 exact orientation',n,d))
    assert V.degree()==d and V.lc()==E(1)
    return V

PLAN={
    (8,144):(4,30,6,2),
    (48,2):(24,31,1,7),
    (24,18):(12,32,3,3),
    (60,18):(30,32,3,3),
    (18,24):(9,32,4,1),
    (42,72):(21,32,6,4),
    (4,108):(4,32,9,3),
}

def main():
    all_count=0
    A,B,J,*_,gd=model()
    for P,e,d,ann in source():
        n=len(P)-1
        dd,s0,degree,components=PLAN[n,e]
        assert dd==d
        S=exact_orientation(ration(P),d)
        K=ExField(S)
        spec=lambda P:trim([K(gpoly(R)) for R in Co(P,1)])
        T=min((W for W in map(spec,(A,B,J)) if W),key=len)
        assert len(T)==s0+1
        G=spec(gd['nodal_lead']);assert G
        Q=fast_guard(K,T,G,degree,'nodal_lead')
        Q=sc(Q,Q[-1].inv());assert len(Q)==s0+1-degree
        R=modgamma(S,pr,tt);assert R.degree()==d and R.leading_coefficient()==1
        m=all_mod(R,pr,tt,Q);assert m==components
        all_count+=m
        print('all true coefficient-domain guarded fourth branches',n,e,d,m,flush=True)
    assert all_count==23

if __name__=='__main__':main()
