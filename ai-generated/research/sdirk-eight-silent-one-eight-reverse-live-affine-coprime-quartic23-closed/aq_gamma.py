"""Exact diagonal projection, polynomial guard division, and complete leading checks."""
from aq_rear import tail_data, lru_cache
from regular_star_projection import remove
from small_crt import small_resultant
from unequal_finite import E
from flint import fmpq_poly

def gpoly(F):
    pairs={}
    for (u,s,g,t),a in F.to_dict().items():
        assert u==s==0 and t in (0,1)
        pairs[g,t]=a
    n=max((g for g,t in pairs),default=-1)+1
    return E(*(fmpq_poly([pairs.get((j,t),0) for j in range(n)]) for t in (0,1)))

@lru_cache(None)
def projection(front,rear,slot):
    F,G,J,gs=tail_data(front,rear,slot)
    O=small_resultant(F,G)
    assert O and O.degrees()[:3]==(0,0,62 if rear else 92)
    print('diagonal exact before guards',front,rear,slot,O.degrees(),flush=True)
    L,G0=remove(gs[4],gs[:4]);assert L.degrees()[2]==12 and G0==[0,0,1,1]
    R,ms=remove(O,gs+(L,))
    print('diagonal exact after guards',R.degrees(),ms,flush=True)
    assert ms==[6 if rear else 7,0,1,1,0,0,0,2,0,0,1]
    R=gpoly(R)
    R=R.monic()
    assert R.degree()==(26 if rear else 55)
    return R
