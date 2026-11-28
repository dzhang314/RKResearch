"""Exact outer projection for arithmetic front, star rear, literal silent fourth."""
from functools import lru_cache
from h54_af_star_shape import U,trial
from h5_arthfront_projection import early,model,gpoly,Co,remove,crt
from aq_rear import g

def norm(Q):
    return Q.a*Q.a-Q.b*Q.b/2

@lru_cache(None)
def project():
    P=early()
    C,N=trial()
    gs=model(False)[6]
    H=crt(P,C,'arithmetic front true star-rear silent fourth')
    H0,e=remove(H,tuple(h for h in gs if h.degrees()[0]==0))
    M=gpoly(H0).monic()
    d=norm(gpoly(Co(P)[-1])).gcd(norm(gpoly(Co(C)[-1])))
    g2=norm(M).gcd(d)
    h3=g2.gcd(norm(gpoly(Co(N)[-1])))
    assert H.degrees()==(0,0,1007,1) and H0.degrees()==(0,0,677,1)
    assert e==[150,45,0,0] and g2.degree()==0 and h3.degree()==0
    print('silent4 arithmetic-front star-rear exact outer',H.degrees(),H0.degrees(),
          e, 'Y-leading norm 2/3 overlap',g2.degree(),h3.degree(),flush=True)
    return M,P,C,N
