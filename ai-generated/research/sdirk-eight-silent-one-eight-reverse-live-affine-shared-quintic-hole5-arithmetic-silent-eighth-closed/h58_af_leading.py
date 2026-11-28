"""Exact common nominal leading-degree locus and its fully specialized local fiber."""
from functools import lru_cache
from h58_af_projection import early,y_project,model,gpoly,Co
from aq_modular import Bfield,nmod_poly,gcdp
from unequal_finite import E

def norm(P):return P.a*P.a-P.b*P.b/2

def rem(P,L):
    D=norm(L)
    return E(P.a%D,P.b%D)%L

def cut_by(P,Q):
    cut=0
    while True:
        d=P.gcd(rem(Q,P)) if P.degree()<Q.degree() else Q.gcd(rem(P,Q))
        if d.degree()==0:return P.monic(),cut
        P=P.exact(d);cut+=d.degree()
        assert P

@lru_cache(None)
def degree_locus():
    P,Q=early(),y_project()
    p,q=[gpoly(Co(T)[-1]) for T in (P,Q)]
    G=p.gcd(rem(q,p))
    assert G and not rem(p,G) and not rem(q,G)
    D=gpoly(model(False)[3])
    L,e=cut_by(G,E([0,1]))
    L,v=cut_by(L,D)
    print('true silent8 exact common leading locus',
          G.degree(),L.degree(),e,v,L,flush=True)
    assert L.degree()>0 and not rem(p,L) and not rem(q,L)
    assert L.gcd(rem(D,L)).degree()==0 and L.gcd(E([0,1])).degree()==0
    return L,P,Q

def test_locus(p,t):
    L,P,Q=degree_locus()
    pc,qc=[[rem(gpoly(z),L) for z in Co(T)] for T in (P,Q)]
    while pc and not pc[-1]:pc.pop()
    while qc and not qc[-1]:qc.pop()
    assert pc and qc
    base=Bfield(nmod_poly([0,1],p),p,t)
    d=base.cast(L)
    assert d.degree()==L.degree() and d.leading_coefficient()==1
    primes=d.factor()[1]
    prod=nmod_poly([1],p)
    for h,e in primes:
        prod*=h**e
        B=Bfield(h,p,t)
        P0,Q0=[[B(u) for u in A] for A in (pc,qc)]
        assert P0[-1] or Q0[-1]
        gg=gcdp(P0,Q0)
        print('true silent8 exact degree-loss reduced factor',str(h),e,
              'specialized full Y degrees',len(pc)-1,len(qc)-1,'gcd degree',len(gg)-1,flush=True)
        assert gg==[B(1)]
    assert prod==d
    return d

if __name__=='__main__':test_locus(1129,203)
